#!/usr/bin/env python3
"""stmt_diff.py — for every `LeeDiam.X_proved`, compare its type with the type of the claim `LeeDiam.X`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Usage: stmt_diff.py <core> <scratch|lake>  |  stmt_diff.py --test <core>
  scratch: the scratch oleans of scripts/lc.sh first on LEAN_PATH (during the work); lake: only `lake build` oleans (final check).
Exit: 0 every pair IDENTICAL, IDENTICAL_AUX or allowed (--test: every fixture verdict as expected) | 1 some pair not
  allowed (--test: a wrong verdict) | 2 usage or probe failure.
The Lean probe takes one of the two compile slots (the lock files of scripts/lc.sh)."""
import fcntl
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = 'LeeDiam'
SCRATCH_OLEAN = ROOT / '.lake' / 'scratch' / 'olean'
SLOT_DIR = ROOT / '.lake' / 'scratch' / 'lean_slots'
ALLOW_FILE = ROOT / 'scripts' / 'stmt_diff_allow.txt'
MARK = 'STMTDIFF|'

META = r'''
open Lean in
/-- Is `n` an auxiliary proof constant `Y._proof_k` (a theorem)? Lean names the `by ...` proofs inside a type this way
and reuses one such theorem for equal proofs in the same file, so `Y` need not be the declaration itself. -/
def stmtDiffIsAuxProof (env : Environment) (n : Name) : Bool :=
  match n, env.find? n with
  | .str _ s, some (.thmInfo _) => s.startsWith "_proof_"
  | _, _ => false

open Lean in
/-- Replace every auxiliary proof constant by one placeholder constant. -/
def stmtDiffEraseAux (env : Environment) (e : Expr) : Expr :=
  e.replace fun t =>
    match t with
    | .const n _ => if stmtDiffIsAuxProof env n then some (.const `stmtDiffAuxProof []) else none
    | _ => none

open Lean Meta Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let pairs := env.constants.fold (fun acc n _ =>
    match n with
    | .str p s =>
      if (`LeeDiam).isPrefixOf n && s.endsWith "_proved" then
        acc.push (Name.str p (String.ofList (s.toList.take (s.length - 7))), n)
      else acc
    | _ => acc) (#[] : Array (Name × Name))
  for (b, p) in pairs do
    match env.find? b, env.find? p with
    | some cb, some cp =>
      let st ← liftTermElabM do
        if cb.type == cp.type then return "IDENTICAL"
        else if (← isDefEq cb.type cp.type) then
          if stmtDiffEraseAux env cb.type == stmtDiffEraseAux env cp.type then return "IDENTICAL_AUX"
          else return "DEFEQ"
        else return "DIFFERENT"
      logInfo m!"STMTDIFF|{st}|{b}|{p}"
    | _, _ => pure ()
'''

# --test: one X / X_proved pair per verdict. tAux is the case met in 004: the same `⟨i, by omega⟩` in two FILES (the
# claim in the probe, the proof in module StmtDiffFixtureA) gives auxiliary theorems with different names (in one file
# Lean reuses one). tChanged checks that a real change inside such a type is still caught.
FIXTURE_A = r'''
namespace LeeDiam
theorem tAux_proved (k : Nat) (hk : 2 ≤ k) : (⟨0, by omega⟩ : Fin k) = ⟨1, by omega⟩ → False := by
  intro h; cases h
theorem tChanged_proved (k : Nat) (hk : 2 ≤ k) : (⟨1, by omega⟩ : Fin k) = ⟨0, by omega⟩ → False := by
  intro h; cases h
end LeeDiam
'''
FIXTURE = r'''
namespace LeeDiam
def stmtDiffTwo : Nat := 2
theorem tIdentical : 1 = 1 := rfl
theorem tIdentical_proved : 1 = 1 := rfl
theorem tAux (k : Nat) (hk : 2 ≤ k) : (⟨0, by omega⟩ : Fin k) = ⟨1, by omega⟩ → False := by
  intro h; cases h
theorem tDefeq : stmtDiffTwo = 2 := rfl
theorem tDefeq_proved : 2 = 2 := rfl
theorem tChanged (k : Nat) (hk : 2 ≤ k) : (⟨0, by omega⟩ : Fin k) = ⟨1, by omega⟩ → False := by
  intro h; cases h
end LeeDiam
'''
FIXTURE_EXPECTED = {'LeeDiam.tIdentical': 'IDENTICAL', 'LeeDiam.tAux': 'IDENTICAL_AUX', 'LeeDiam.tDefeq': 'DEFEQ',
                    'LeeDiam.tChanged': 'DIFFERENT'}


def lean_modules():
    """Every module of the library (versions/ folders excluded)."""
    files = sorted((ROOT / LIB).rglob('*.lean'))
    return ['.'.join(f.relative_to(ROOT).with_suffix('').parts) for f in files if 'versions' not in f.parts]


def lean_path(mode):
    base = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, capture_output=True, text=True,
                          check=True).stdout.strip()
    if mode == 'scratch':
        return f'{SCRATCH_OLEAN}:{base}'
    if mode == 'lake':
        return base
    raise SystemExit(f'usage: oleans must be scratch or lake, not {mode!r}')


def acquire_slot():
    """Hold one of the two compile slots (same lock files as scripts/lc.sh) until the process ends."""
    SLOT_DIR.mkdir(parents=True, exist_ok=True)
    while True:
        for k in (1, 2):
            handle = open(SLOT_DIR / f'slot{k}.lock', 'w')
            try:
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return handle
            except BlockingIOError:
                handle.close()
        time.sleep(3)


def tree_probe_text():
    """The probe over the whole library: import every module, then run META."""
    return ''.join(f'import {m}\n' for m in lean_modules()) + 'import Lean\n' + META


def run_lean(core, env, args):
    out = subprocess.run(['nice', '-n', '19', 'taskset', '-c', str(core), 'lean', *args], cwd=ROOT,
                         capture_output=True, text=True, env=env)
    if out.returncode != 0:
        print('probe failed:\n' + out.stdout + out.stderr, file=sys.stderr)
        raise SystemExit(2)
    return out.stdout


def run_probe(core, mode, text, pre_modules):
    """Compile `pre_modules` ({module name: source}) to oleans in a scratch folder, then run the probe `text`."""
    with tempfile.TemporaryDirectory(dir=ROOT / 'scripts', prefix='.stmt_diff.') as tmp:
        env = {'LEAN_PATH': f'{tmp}:{lean_path(mode)}', 'LEAN_NUM_THREADS': '1',
               'PATH': '/usr/bin:/bin:' + str(Path.home() / '.elan/bin')}
        slot = acquire_slot()
        for name, source in pre_modules.items():
            (Path(tmp) / f'{name}.lean').write_text(source)
            run_lean(core, env, [f'--root={tmp}', '-o', f'{tmp}/{name}.olean', f'{tmp}/{name}.lean'])
        probe = Path(tmp) / 'StmtDiffProbe.lean'
        probe.write_text(text)
        stdout = run_lean(core, env, [str(probe)])
        slot.close()
    return stdout


def parse(text):
    rows = []
    for line in text.splitlines():
        idx = line.find(MARK)
        if idx >= 0:
            status, base, proved = line[idx + len(MARK):].strip().split('|')
            rows.append((base, proved, status))
    return sorted(rows)


def read_allow():
    """`<claim name> <reason>` per line; `#` starts a comment line."""
    allow = {}
    if ALLOW_FILE.exists():
        for line in ALLOW_FILE.read_text().splitlines():
            if line.strip() and not line.lstrip().startswith('#'):
                name, _, reason = line.strip().partition(' ')
                allow[name] = reason.strip()
    return allow


def report(rows, allow):
    bad = 0
    for base, proved, status in rows:
        if status == 'IDENTICAL':
            mark = 'ok'
        elif status == 'IDENTICAL_AUX':
            mark = 'ok (identical up to auxiliary proofs X._proof_k)'
        elif base in allow:
            mark = f'ALLOWED ({allow[base]})'
        else:
            mark = 'NOT ALLOWED'
            bad += 1
        print(f'{status:13} {base}  <-  {proved}   [{mark}]')
    seen = {base for base, _, _ in rows}
    for name in sorted(set(allow) - seen):
        print(f'WARNING: allow-list entry {name} has no X_proved pair now (stale entry?)')
    for base, _, status in rows:
        if base in allow and status in ('IDENTICAL', 'IDENTICAL_AUX'):
            print(f'WARNING: allow-list entry {base} is {status} now (remove the entry)')
    print(f'stmt_diff: {len(rows)} pairs, {bad} not allowed')
    return bad


def main_test(core):
    """Run META on FIXTURE (one pair per verdict); every verdict must be the expected one."""
    rows = parse(run_probe(core, 'lake', 'import StmtDiffFixtureA\nimport Lean\n' + FIXTURE + META,
                           {'StmtDiffFixtureA': FIXTURE_A}))
    got = {base: status for base, _, status in rows}
    wrong = [f'{base}: expected {want}, got {got.get(base)}' for base, want in FIXTURE_EXPECTED.items()
             if got.get(base) != want]
    for line in wrong:
        print(f'TEST FAILED: {line}', file=sys.stderr)
    if not wrong:
        print(f'PASS: {len(FIXTURE_EXPECTED)} fixture pairs, verdicts {sorted(set(FIXTURE_EXPECTED.values()))}.')
    raise SystemExit(1 if wrong else 0)


def main():
    if len(sys.argv) == 3 and sys.argv[1] == '--test':
        main_test(int(sys.argv[2]))
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        raise SystemExit(2)
    rows = parse(run_probe(int(sys.argv[1]), sys.argv[2], tree_probe_text(), {}))
    if not rows:
        print('ERROR: the probe reported no X / X_proved pair.', file=sys.stderr)
        raise SystemExit(2)
    raise SystemExit(1 if report(rows, read_allow()) else 0)


if __name__ == '__main__':
    main()

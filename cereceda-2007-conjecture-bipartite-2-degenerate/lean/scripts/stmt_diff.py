#!/usr/bin/env python3
"""stmt_diff.py — for every `Cereceda.X_proved`, compare its type with the type of the claim `Cereceda.X`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Usage: stmt_diff.py <core> <scratch|lake>
  scratch: the oleans in $LEAN_SCRATCH_OLEAN first on LEAN_PATH (a work tool); lake: only `lake build` oleans
  (the final check).
Exit: 0 every pair IDENTICAL or allowed | 1 some pair not allowed | 2 usage or probe failure.
When LEAN_SLOT_DIR is set, the Lean probe takes one of its two compile slots (the lock files of scripts/lc.sh)."""
import fcntl
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = 'Cereceda'
SCRATCH_OLEAN_ENV = 'LEAN_SCRATCH_OLEAN'  # scratch mode only: the scratch olean dir (a work tool, not used by check.sh)
SLOT_DIR_ENV = 'LEAN_SLOT_DIR'  # optional: lock dir of the shared compile slots (scripts/lc.sh)
ALLOW_FILE = ROOT / 'scripts' / 'stmt_diff_allow.txt'
MARK = 'STMTDIFF|'

META = r'''
open Lean Meta Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let pairs := env.constants.fold (fun acc n _ =>
    match n with
    | .str p s =>
      if (`Cereceda).isPrefixOf n && s.endsWith "_proved" then
        acc.push (Name.str p (String.ofList (s.toList.take (s.length - 7))), n)
      else acc
    | _ => acc) (#[] : Array (Name × Name))
  for (b, p) in pairs do
    match env.find? b, env.find? p with
    | some cb, some cp =>
      let st ← liftTermElabM do
        if cb.type == cp.type then return "IDENTICAL"
        else if (← isDefEq cb.type cp.type) then return "DEFEQ"
        else return "DIFFERENT"
      logInfo m!"STMTDIFF|{st}|{b}|{p}"
    | _, _ => pure ()
'''


def lean_modules():
    """Every module of the library (versions/ folders excluded)."""
    files = sorted((ROOT / LIB).rglob('*.lean'))
    return ['.'.join(f.relative_to(ROOT).with_suffix('').parts) for f in files if 'versions' not in f.parts]


def lean_path(mode):
    base = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, capture_output=True, text=True,
                          check=True).stdout.strip()
    if mode == 'scratch':
        scratch = os.environ.get(SCRATCH_OLEAN_ENV)
        if not scratch:
            raise SystemExit(f'scratch mode needs {SCRATCH_OLEAN_ENV} (the scratch olean dir)')
        return f'{scratch}:{base}'
    if mode == 'lake':
        return base
    raise SystemExit(f'usage: oleans must be scratch or lake, not {mode!r}')


def acquire_slot():
    """If LEAN_SLOT_DIR is set, hold one of its two compile slots (the lock files of scripts/lc.sh) until the process ends."""
    if not os.environ.get(SLOT_DIR_ENV):
        return None
    slot_dir = Path(os.environ[SLOT_DIR_ENV])
    slot_dir.mkdir(parents=True, exist_ok=True)
    while True:
        for k in (1, 2):
            handle = open(slot_dir / f'slot{k}.lock', 'w')
            try:
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return handle
            except BlockingIOError:
                handle.close()
        time.sleep(3)


def run_probe(core, mode):
    text = ''.join(f'import {m}\n' for m in lean_modules()) + 'import Lean\n' + META
    env = {'LEAN_PATH': lean_path(mode), 'LEAN_NUM_THREADS': '1',
           'PATH': '/usr/bin:/bin:' + str(Path.home() / '.elan/bin')}
    with tempfile.TemporaryDirectory(dir=ROOT / 'scripts', prefix='.stmt_diff.') as tmp:
        probe = Path(tmp) / 'StmtDiffProbe.lean'
        probe.write_text(text)
        slot = acquire_slot()
        out = subprocess.run(['nice', '-n', '19', 'taskset', '-c', str(core), 'lean', str(probe)], cwd=ROOT,
                             capture_output=True, text=True, env=env)
        if slot is not None:
            slot.close()
    if out.returncode != 0:
        print('probe failed:\n' + out.stdout + out.stderr, file=sys.stderr)
        raise SystemExit(2)
    return out.stdout


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
        elif base in allow:
            mark = f'ALLOWED ({allow[base]})'
        else:
            mark = 'NOT ALLOWED'
            bad += 1
        print(f'{status:9} {base}  <-  {proved}   [{mark}]')
    seen = {base for base, _, _ in rows}
    for name in sorted(set(allow) - seen):
        print(f'WARNING: allow-list entry {name} has no X_proved pair now (stale entry?)')
    for base, _, status in rows:
        if base in allow and status == 'IDENTICAL':
            print(f'WARNING: allow-list entry {base} is IDENTICAL now (remove the entry)')
    print(f'stmt_diff: {len(rows)} pairs, {bad} not allowed')
    return bad


def main():
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        raise SystemExit(2)
    rows = parse(run_probe(int(sys.argv[1]), sys.argv[2]))
    if not rows:
        print('ERROR: the probe reported no X / X_proved pair.', file=sys.stderr)
        raise SystemExit(2)
    raise SystemExit(1 if report(rows, read_allow()) else 0)


if __name__ == '__main__':
    main()

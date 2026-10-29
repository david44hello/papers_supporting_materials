#!/usr/bin/env python3
"""audit.py — status of every claim in Cereceda/Paper/Statements.lean, read from Lean's `#print axioms`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Usage: audit.py <core> --oleans scratch|lake
  scratch: scripts/lc.sh oleans first (compile Statements.lean and its imports with lc.sh before); lake: after lake build."""
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRATCH_OLEAN_ENV = 'LEAN_SCRATCH_OLEAN'
STD = {'propext', 'Classical.choice', 'Quot.sound'}
CITED = {'Cereceda.Cited.cer07_thm522', 'Cereceda.Cited.bjlpp14_thm8', 'Cereceda.Cited.bjlpp14_thm10',
         'Cereceda.Cited.bh22_thm1_quadratic'}
STATEMENTS = 'Cereceda/Paper/Statements.lean'


def paper_version():
    """The paper version the rows cite, from the line "PAPER VERSION: vX.YY" of the Statements header."""
    found = re.findall(r'^PAPER VERSION: (v\d+\.\d+)\b', (ROOT / STATEMENTS).read_text(), re.M)
    if len(found) != 1:
        raise SystemExit(f'{STATEMENTS} must have exactly one line "PAPER VERSION: vX.YY" (found {len(found)})')
    return found[0]


def refs_pattern(version):
    return re.compile(rf'{re.escape(version)} l\. (\d+(?:-\d+)?(?:(?:, | and )(?:l\. )?\d+(?:-\d+)?)*)')


def claim_names():
    src = (ROOT / 'Cereceda/Paper/Statements.lean').read_text()
    return re.findall(r'^theorem (\S+)', src, re.M)


def docstring_of(src, start):
    """The docstring directly above the declaration at `start` (only `open Classical in` may sit between), else ''."""
    end = src.rfind('-/', 0, start)
    begin = src.rfind('/--', 0, end)
    between = src[end + 2:start].strip()
    return src[begin:end] if begin != -1 and between in ('', 'open Classical in') else ''


GIVEN = re.compile(r'GIVEN NOT-FORMALIZED INPUT: ([^.]*)\.')


def given_inputs():
    """Claim -> the not-formalized inputs named in its docstring (rows proved from hypotheses that stand for facts)."""
    src = (ROOT / STATEMENTS).read_text()
    given = {}
    for m in re.finditer(r'^theorem (\S+)', src, re.M):
        g = GIVEN.search(' '.join(docstring_of(src, m.start()).split()))
        if g:
            given[m.group(1)] = g.group(1).strip()
    return given


def paper_column(version):
    """Claim -> its lines in the paper version cited, or None for a Lean-only row (no line of that version)."""
    src = (ROOT / STATEMENTS).read_text()
    column = {}
    for m in re.finditer(r'^theorem (\S+)', src, re.M):
        doc = ' '.join(docstring_of(src, m.start()).split())
        if f'not in {version}' in doc:
            raise SystemExit(f'{m.group(1)}: its docstring says "not in {version}"; rows of claims not in the paper are deleted')
        refs = refs_pattern(version).findall(doc)
        column[m.group(1)] = 'l. ' + '; '.join(refs) if refs else None
    return column


def search_path(mode):
    lean_path = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, capture_output=True,
                               text=True, check=True).stdout.strip()
    if mode == 'scratch':
        if not os.environ.get(SCRATCH_OLEAN_ENV):
            raise SystemExit(f'scratch mode needs {SCRATCH_OLEAN_ENV} (the scratch olean dir)')
        return f'{os.environ[SCRATCH_OLEAN_ENV]}:{lean_path}'
    return lean_path


def run_probe(core, names, mode):
    probe = ROOT / 'scripts' / 'AuditProbe.lean'
    probe.write_text('import Cereceda.Paper.Statements\n' + ''.join(f'#print axioms Cereceda.{nm}\n' for nm in names))
    env = {'LEAN_PATH': search_path(mode), 'LEAN_NUM_THREADS': '1', 'PATH': '/usr/bin:/bin:' + str(Path.home() / '.elan/bin')}
    out = subprocess.run(['nice', '-n', '19', 'taskset', '-c', str(core), 'lean', str(probe)], cwd=ROOT,
                         capture_output=True, text=True, env=env)
    probe.unlink()
    if out.returncode != 0:
        raise SystemExit('probe failed:\n' + out.stdout + out.stderr)
    return out.stdout


def classify(text, names):
    status = {}
    for nm in names:
        m = re.search(rf"'Cereceda\.{re.escape(nm)}' depends on axioms: \[(.*?)\]", text, re.S)
        if m:
            axs = {a.strip() for a in m.group(1).replace('\n', ' ').split(',') if a.strip()}
        elif re.search(rf"'Cereceda\.{re.escape(nm)}' does not depend on any axioms", text):
            axs = set()
        else:
            raise SystemExit(f'no axiom line for {nm}')
        if 'sorryAx' in axs:
            status[nm] = ('OPEN', axs)
        elif axs <= STD:
            status[nm] = ('PROVED', axs)
        elif axs <= STD | CITED:
            status[nm] = ('PROVED-FROM-CITED', axs)
        else:
            status[nm] = ('VIOLATION', axs)
    return status


KINDS = ('PROVED', 'PROVED-FROM-CITED', 'PROVED-GIVEN-INPUT', 'OPEN', 'VIOLATION')


def count_line(label, rows):
    counts = {k: sum(1 for v in rows.values() if v[0] == k) for k in KINDS}
    return f'{label}: ' + ' / '.join(f'{k} {counts[k]}' for k in KINDS) + f' (of {len(rows)})'


def mark_given(status):
    """A proved row with a GIVEN line becomes PROVED-GIVEN-INPUT (its inputs are shown with its axioms)."""
    given = given_inputs()
    for nm, (st, axs) in list(status.items()):
        if nm in given and st in ('PROVED', 'PROVED-FROM-CITED'):
            status[nm] = ('PROVED-GIVEN-INPUT', axs | {f'GIVEN: {given[nm]}'})
    return status


def write_report(status):
    version = paper_version()
    status = mark_given(status)
    paper = paper_column(version)
    claims = {nm: v for nm, v in status.items() if paper[nm]}
    lean_only = {nm: v for nm, v in status.items() if not paper[nm]}
    lines = ['# AUDIT — Cereceda, generated by scripts/audit.py from `#print axioms`', '',
             count_line(f'PAPER {version} CLAIMS', claims), '', count_line('LEAN-ONLY ROWS (no paper line)', lean_only), '',
             f'| # | Claim | Paper {version} | Status | Axioms |', '|---|---|---|---|---|']
    for idx, (nm, (st, axs)) in enumerate(status.items(), 1):
        lines.append(f'| {idx} | `{nm}` | {paper[nm] or "Lean-only"} | {st} | {", ".join(sorted(axs))} |')
    (ROOT / 'AUDIT.md').write_text('\n'.join(lines) + '\n')
    print(lines[2]); print(lines[4])


def main():
    if len(sys.argv) != 4 or sys.argv[2] != '--oleans' or sys.argv[3] not in ('scratch', 'lake'):
        raise SystemExit('usage: audit.py <core> --oleans scratch|lake')
    names = claim_names()
    status = classify(run_probe(int(sys.argv[1]), names, sys.argv[3]), names)
    write_report(status)


if __name__ == '__main__':
    main()

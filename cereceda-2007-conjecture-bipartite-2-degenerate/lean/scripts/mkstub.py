#!/usr/bin/env python3
"""mkstub.py — copy exact statements from Cereceda/Paper/Statements.lean into a proof-stub file as `<name>_proved`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Usage: mkstub.py <out.lean> <header-comment> <import1,import2,...> <thm1> [<thm2> ...]
The statement text is copied character for character (only the name gains `_proved`), so types cannot drift."""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def extract(src, name):
    """Return (prefix_lines, signature) of theorem `name`: signature = text from `theorem name` to `:=`."""
    lines = src.split('\n')
    for idx, line in enumerate(lines):
        if re.match(rf'^theorem {re.escape(name)}(\s|$)', line):
            sig = []
            for jj in range(idx, len(lines)):
                sig.append(lines[jj])
                if re.search(r':=( by)?\s*$', lines[jj]):
                    break
            text = '\n'.join(sig)
            text = text[:text.rindex(':=')].rstrip()
            back = idx - 1
            if back >= 0 and lines[back].rstrip().endswith('-/'):
                while back >= 0 and not lines[back].startswith('/--'):
                    back -= 1
                back -= 1
            prefix = lines[back] if back >= 0 and lines[back].startswith('open Classical in') else ''
            return prefix, text
    raise SystemExit(f'theorem {name} not found')


def main_mkstub(out, header, imports, names):
    src = (ROOT / 'Cereceda/Paper/Statements.lean').read_text()
    parts = [f'/-\n{out} — {header}\nCopyright (C) Dave Goel 2026--now.\n## version 0.01 - stubs made by scripts/mkstub.py '
             f'from Statements.lean (statements copied verbatim, name + `_proved`).\n-/']
    parts += [f'import {imp}' for imp in imports]
    parts += ['', 'namespace Cereceda', '', 'open Finset', '']
    for name in names:
        prefix, sig = extract(src, name)
        sig = sig.replace(f'theorem {name}', f'theorem {name}_proved', 1)
        if prefix:
            parts.append(prefix)
        parts.append(sig + ' := by\n  sorry\n')
    parts.append('end Cereceda\n')
    path = ROOT / out
    if path.exists():
        raise SystemExit(f'{path} exists; refusing to overwrite')
    path.write_text('\n'.join(parts))
    print(f'wrote {path}')


def main():
    out, header, imports = sys.argv[1], sys.argv[2], sys.argv[3].split(',')
    main_mkstub(out, header, imports, sys.argv[4:])


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
# build_serial.py — `lake build` one module at a time, in import order, so at most ONE Lean process runs (low
# machine load). 20261027.
"""Usage: scripts/build_serial.py <core> [--wrap "PREFIX"]   (from anywhere; builds every module under Cereceda/, then
         the root; with --wrap, each module's build runs as PREFIX + the build command, e.g. a machine's compile gate)
         scripts/build_serial.py --test    (checks the import order on this project)"""
import os
import re
import shlex
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LIB = "Cereceda"
IMPORT = re.compile(r"^import\s+(\S+)", re.M)


def local_imports(path):
    return [m for m in IMPORT.findall(path.read_text()) if m == LIB or m.startswith(LIB + ".")]


def modules():
    found = {}
    for path in sorted((ROOT / LIB).rglob("*.lean")):
        name = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        found[name] = local_imports(path)
    return found


def import_order(graph):
    """Depth-first topological order: every module after all modules it imports."""
    order, state = [], {}

    def visit(mod):
        if state.get(mod) == "done":
            return
        if state.get(mod) == "open":
            raise SystemExit(f"import cycle at {mod}")
        state[mod] = "open"
        for dep in graph.get(mod, []):
            if dep not in graph:
                raise SystemExit(f"{mod} imports unknown module {dep}")
            visit(dep)
        state[mod] = "done"
        order.append(mod)

    for mod in sorted(graph):
        visit(mod)
    return order


def build(core, target, wrap):
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    cmd = wrap + ["env", "LEAN_NUM_THREADS=1", "nice", "-n", "19", "taskset", "-c", str(core), "lake", "build", target]
    result = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True)
    if result.returncode != 0:
        print(result.stdout[-4000:], result.stderr[-4000:])
        raise SystemExit(f"FAILED: lake build {target} (exit code {result.returncode}; negative = killed by that signal)")
    tail = result.stdout.strip().splitlines()[-1:] or [""]
    print(f"ok {target}: {tail[0][:100]}", flush=True)


def run_tests():
    order = import_order(modules())
    position = {mod: i for i, mod in enumerate(order)}
    graph = modules()
    assert all(position[dep] < position[mod] for mod, deps in graph.items() for dep in deps)
    print(f"PASS: {len(order)} modules in import order")


def main_build_serial(core, wrap):
    for mod in import_order(modules()):
        build(core, mod, wrap)
    build(core, LIB, wrap)


def main():
    if sys.argv[1:] == ["--test"]:
        run_tests()
    elif len(sys.argv) == 2 and sys.argv[1].isdigit():
        main_build_serial(int(sys.argv[1]), [])
    elif len(sys.argv) == 4 and sys.argv[1].isdigit() and sys.argv[2] == "--wrap":
        main_build_serial(int(sys.argv[1]), shlex.split(sys.argv[3]))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()

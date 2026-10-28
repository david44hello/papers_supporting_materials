# No parity class contains half of the reduced Latin squares

<!-- version 0.10 — 2026-10-28: exact-arithmetic supporting computation. -->

Supporting computations for the paper by Dave Goel.

`verify_threshold.py`: the exact inequalities for orders 23 through 63. It uses only the Python standard library.

```
python3 verify_threshold.py --test
python3 verify_threshold.py --first 23 --last 63
```

The second command reproduces `threshold_23_63.txt`. Its middle column is an upper bound, rounded up, for one million times the ratio of the signed-count bound to the total-count bound. Every entry is less than one million.

Copyright (C) Dave Goel 2026--now. All rights reserved.

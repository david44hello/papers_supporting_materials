# Supporting materials for the papers of Dave Goel

[![Lean build](https://github.com/david44hello/papers_supporting_materials/actions/workflows/lean_build.yml/badge.svg)](https://github.com/david44hello/papers_supporting_materials/actions/workflows/lean_build.yml)

Author: Dave Goel. Copyright (C) Dave Goel 2026--now. Licence: Apache-2.0 (see [LICENSE](LICENSE)).

One folder per paper. Each folder holds what supports that paper: today a formal proof in the Lean 4 proof assistant
(in `<paper>/lean/`), later possibly code and data. Each folder's README says what is there and how to check it.

| Paper | Folder | What is there |
|---|---|---|
| The Hibi–Li (2016) conjecture is fully resolved | [hibi-li-2016-conjecture/](hibi-li-2016-conjecture/) | A Lean 4 proof of every result of the paper |

At every change, GitHub rebuilds every Lean proof here on a fresh machine and checks that each published audit table
(`AUDIT.md`: every claim of the paper and exactly what its proof assumes) is what Lean reports (the "Lean build" mark
above; the steps are in [.github/workflows/lean_build.yml](.github/workflows/lean_build.yml)).

## Acknowledgment

This work was done overwhelmingly by AI models and supervised by the author. The models were Anthropic's Claude and
OpenAI's ChatGPT. The author takes full responsibility for the papers.

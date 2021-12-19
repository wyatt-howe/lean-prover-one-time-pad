# Perfect secrecy of the one-time pad formalized and proven in Lean

Final Project for [Brown CS 1951x: Formal Proof and Verification, 2021](https://github.com/BrownCS1951x/fpv2021/tree/main/src)

## Using this repository

This repository is a [Lean project](https://leanprover-community.github.io/install/project.html).
There are some basic steps you should take at the beginning to set it up.
These only need to be done once.
If and when you need to create any new `.lean` files,
create them in the `src` directory of this project,
to ensure that all your expected imports are available.

### Setup

We assume that you have installed:
* `git`
* `lean` (via `elan`)
* `leanproject`
* VSCode and the Lean extension

To set up this project, run:

```bash
leanproject get git@github.com:wyatt-howe/lean-prover-one-time-pad.git
cd fpv2021
lean --make src/final_project.lean
```

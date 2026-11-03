# sssp-lean-scratch

Scratch builds for the Big O Speedrun directed shortest paths race
(https://bigospeedrun.com). This repository holds our own Lean drafts only.

The computation model and the C-HD proof come from
https://github.com/bigospeedrun/c-hd-proof (a fork of spicylemonade/c-hd-proof),
pinned in `lakefile.toml`. The build workflow fetches it; this repository has
no copy of its files.

The one workflow (`build`) runs only by hand (workflow_dispatch), reads the
repository only, and uses no secrets. It runs `lake exe cache get`, `lake build`
and `#print axioms` (`Axioms.lean`; with the `chd` input, also the C-HD proof and `AxiomsCHD.lean`).

We archive this repository when the race opens.

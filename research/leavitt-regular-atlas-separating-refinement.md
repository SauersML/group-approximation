---
rg: 2
id: leavitt-regular-atlas-separating-refinement
kind: claim
title: Canonical regular-A8 atlas models can preserve any fixed nontrivial word separation
distinct_from:
  leavitt-regular-atlas-hyperlinearity-criterion: That is the bare iff feasibility criterion; this records the strengthened forward direction needed for contradiction arguments, preserving the group-trace separation of finitely many chosen nontrivial words during finite-factor regularization.
  compiled-raw-source-word-nontrivial: That proves one particular word is nontrivial; this applies uniformly to any fixed finite list of nontrivial words.
artifacts:
  - docs/EXPLICIT_LEAVITT_ATLAS.md
---

Assume

```text
Q=L_(F_2)(1,2)^x
```

is hyperlinear.  Fix a finite set `W subset bar_P=K_1*K_2` such that
`bar_rho(w)!=1` in `Q` for every `w in W`.

Then the canonical regular-`A_8` models from
`leavitt-regular-atlas-hyperlinearity-criterion` may be chosen so that, in
addition to

```text
max_(s in bar_S) ||pi_n(s)-1||_2 -> 0,
```

one has for every `w in W`

```text
tau(pi_n(w)) -> 0,
||pi_n(w)-1||_2 -> sqrt(2).
```

In particular this applies to the compiled raw source word from
`compiled-raw-source-word-nontrivial`.

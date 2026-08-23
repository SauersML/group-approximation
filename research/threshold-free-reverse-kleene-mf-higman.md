---
rg: 2
id: threshold-free-reverse-kleene-mf-higman
kind: claim
title: Qualitative MF-radical collapse and effective Higman suffice for reverse Kleene
distinct_from:
  threshold-free-reverse-kleene-higman-diagonal: that is the normalized-Hilbert--Schmidt theorem and concludes nonhyperlinearity; this is its operator-norm analogue, uses the MF radical, and has no canonical-trace conditions.
  reverse-kleene-operator-norm-collapse-gives-non-mf: that assumes a finite presentation and one computable finite-coordinate defect threshold; this permits a uniformly recursively enumerable relator stream and assumes only qualitative death in every norm matrix corona.
  canonical-profile-kleene-higman: that permits a rational group-algebra mark but only controls canonical tracial microstates; this uses a group word and all norm-corona homomorphisms.
---

Suppose a total computable compiler sends every Turing-machine index `e` to
a finite alphabet `S_e`, a uniformly recursively enumerable relator stream
`R_e`, and a marked word `w_e`.  Put

```text
Gamma_e=<S_e | R_e>.
```

Assume

```text
e halts     => w_e!=1 in Gamma_e,                         (TFM1)
e nonhalts  => w_e lies in Res_MF(Gamma_e),               (TFM2)
```

where `Res_MF` is the intersection of the kernels of all homomorphisms into
unitary groups of norm matrix coronas.  Then one can effectively construct a
finitely presented non-MF group.

The fixed-point program enumerates proofs, not matrix tuples.  Consequently
the compiler interface needs no defect threshold, separation cutoff,
dimension report, convergence rate, runtime bound, or finite presentation at
the source stage.

---
rg: 2
id: geometric-infinite-counter-is-hs-trace-diluting
kind: claim
title: A geometrically localized infinite-counter witness dilutes both its head and its boundary in normalized HS trace
distinct_from:
  kleene-completeness-needs-only-a-nontrivial-exact-representation: that correctly permits an infinite exact witness to prove algebraic nontriviality; this shows why a normalizable counter STATE does not also provide the finite-matrix soundness or positive canonical density.
  fanizza-coherent-verifier-wandering-promotion: that requires a fixed positive-density group-algebra carrier and canonical wandering growth; this rules out replacing that carrier by the head or history-state line of a standard infinite-counter verifier.
---

Let `S_D` be cyclic increment on `C^D`, let `q_0=|0><0|`, and let a
counter verifier use at most `ell` increments/decrements.  Relative to
normalized matrix trace (including any multiplicity amplification `C^m`),

```text
tr_Dm(q_0 tensor I_m)=1/D,                              (ICT1)
```

and cyclic increment agrees with the unilateral counter on every path which
stays outside the last `ell` counter sites.  Thus every bounded-range local
counter identity has a cyclic finite-dimensional realization whose possible
failure is supported on a projection of normalized trace at most `ell/D` and
normalized HS norm at most `sqrt(ell/D)`.

The geometrically decaying perfect witness

```text
psi_D proportional_to sum_(d=0)^(D-1) gamma^d |d>,
|gamma|<1,
```

does not repair `(ICT1)`: its support projection has rank one and normalized
trace `1/D`, independently of its vector-state mass near the head.  Direct
sum or tensor multiplicity amplification preserves that normalized fraction.

Consequently a Jeffery--Witteveen-style infinite-counter purification can
legitimately prove exact infinite-dimensional completeness, but its geometric
history state cannot be substituted for the fixed positive-density mark in a
normalized-Hilbert--Schmidt nonhyperlinearity argument.  The finite cyclic
truncations make the local shift rules *more* accurately satisfiable while
the distinguished counter line becomes trace-null.  A successful Fanizza
return must therefore use an extensive multiplicity/index obstruction, not
normalizable geometric localization on a counter.

The motivating primary construction is Jeffery--Witteveen,
arXiv:2506.15551, equations (4), (8)--(11) and Section 5: its exact witness
has geometrically decaying amplitudes, and its finite cyclic truncation has
completeness error decaying exponentially in `D`.

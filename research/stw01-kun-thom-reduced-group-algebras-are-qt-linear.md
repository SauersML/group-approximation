---
rg: 2
id: stw01-kun-thom-reduced-group-algebras-are-qt-linear
kind: claim
title: The Kun--Thom nonsofic groups are exact, so their reduced group C*-algebras have only tracial quasitraces
distinct_from:
  kun-thom-nonsofic-wreath: that imports nonsoficity of the Kun--Thom wreath; this proves exactness of the same groups and the resulting quasitrace linearity of their reduced algebras.
  stw99-quasitrace-problem-for-cstar-simple-groups: that asks for a unique quasitrace on reduced algebras of C*-simple groups; this settles quasitrace linearity for the specific exact Kun--Thom groups, with no C*-simplicity assumption.
artifacts:
  - research/artifacts/stw01-host-survey-2026-09-12.md
---

Let `Gamma <= G` be a Kun--Thom Theorem E pair, for a prime power `q` and
`r, d >= 3`:

```text
Gamma = EL_r(F_q[x_1,...,x_d]),
G     = EL_r(F_q[x_1^(+-1),...,x_d^(+-1)]) semidirect SL_d(Z).
```

Let `W = (Z/2Z) wr_(G/Gamma) G` be the nonsofic coset wreath and `D = G *_Gamma G`
the nonsofic group double.

Then `G`, `W`, `D` and all their subgroups have property A. Their reduced group
C*-algebras are exact. So every bounded 2-quasitrace on `C*_r(G)`, `C*_r(W)`,
`C*_r(D)`, on any C*-subalgebra of these, and on any quotient of these, is a trace.

**Consequence for Problem I.** The repo's nonsofic groups cannot host a
counterexample through their reduced algebras. Their full group C*-algebras are
non-exact, since they contain `C*(F_2)` because `F_2 <= SL_3(Z) <= G`. But `G`,
`W` and `D` have finite abelianization, so none of them surjects onto `F_2`, and
their full algebras are not universal tests in the sense of
`stw01-full-free-group-algebra-quasitraces-are-traces`.

Proof: `stw01-kun-thom-reduced-group-algebras-qt-linear-proof`.

---
rg: 2
id: kassabov-nikolov-alternating-frames-are-not-fp
kind: claim
title: No Kassabov-Nikolov frame of a product of alternating groups is finitely presented
distinct_from:
  fp-rf-group-with-unbounded-prime-torsion: that asks for some finitely presented residually finite group with torsion of infinitely many prime orders; this shows that the frame subgroups of Kassabov and Nikolov, which have such torsion, are not finitely presented.
  products-of-finite-groups-with-schur-factors-not-fp: that is the general H_2 obstruction for groups containing a restricted product; this applies it to products of alternating groups and to the Kassabov-Nikolov frames.
---

**Statement.** Let `S = prod_n S_n` be a product of infinitely many finite
factors, each an alternating group `A_(k_n)` with `k_n >= 4`; repeated factors
are allowed. Every subgroup `G <= S` containing `(+)_n S_n` has `H_2(G; Z)` not
finitely generated, so it is not finitely presented.

In particular no frame of such a product, in the sense of Kassabov--Nikolov
(arXiv:math/0602446, §2), is finitely presented. This covers:
- the 10-generated frame of their Theorem `beginning` for
  `prod_(n >= 3) Alt(u_(n,p))`;
- the frames their proof of Theorem `main1` builds for products
  `prod_n Alt(n)^(f(n))`.

The proof is `kassabov-nikolov-frames-not-fp-proof`.

**Consequence for torsion.** These frames are finitely generated, residually
finite, and contain `A_(k)` for unbounded `k`, so they have elements of every
prime order. They still cannot witness `fp-rf-group-with-unbounded-prime-torsion`.

**Not covered.** The obstruction is blind to factors with trivial Schur
multiplier. Kassabov's group `G_0 = EL_3(R) <= prod_(n >= 3) SL_(3n)(F_p)`,
the starting point of the Kassabov--Nikolov construction (their Proposition
`g0`), contains `(+)_n SL_(3n)(F_p)`. Its factors are perfect with trivial
multiplier for large `n` (standard, not rechecked here). `G_0` is not
finitely presented either, for a different reason: a marked-limit argument
with twisted cycles (`kassabov-g0-is-not-finitely-presented`, 2026-09-13).

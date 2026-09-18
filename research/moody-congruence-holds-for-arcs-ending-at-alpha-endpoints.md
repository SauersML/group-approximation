---
rg: 2
id: moody-congruence-holds-for-arcs-ending-at-alpha-endpoints
kind: claim
title: The Moody polynomial is well defined and congruent mod a palindromic ideal for arcs ending at p_1 or p_2, the endpoints of alpha, so the Burau-to-Moody bridge covers every Gamma in B_5 and not only the pure ones
distinct_from:
  brunnian-burau-kernel-mod-cyclotomic-products-nontrivial: that is the congruence statement whose Part 2 quantifies over every Gamma in B_5; this is the missing geometric input its last step needs, and without it that Part 2 is proved only for pure Gamma.
  burau-minus-one-kernel-meets-brunnian-four-braids: that is the single braid Phi_0 with rho_4(Phi_0) = I mod (t+1); this is about the arc-to-loop dictionary used to push such a congruence into Moody polynomials.
  moody-polynomial-change-certifies-burau-nonkernel: that is Moody's criterion, the case a = 0 of Theorem A, used only for arcs to p_n; this asks for the dictionary at the two marked points that alpha itself joins.
artifacts:
  - research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md
---

**OPEN.**

## Statement

Notation as in `research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md`:
`alpha` is the arc from `p_1` to `p_2`, `A` is an arc from `p_*` to a marked point `p`,
`M(alpha, A)` is the Moody polynomial and `I` the intersection form on loop classes.

Let `p in {p_1, p_2}`. Then:

1. **(Well-definedness.)** `M(alpha, A)` depends only on the homotopy class of `A` rel
   endpoints through arcs with interior in `D_n` — the conclusion of Corollary 3.2 of the
   artifact — for arcs `A` ending at `p_1` or `p_2`.
2. **(Congruence.)** Let `a` be an ideal of `Z[t^{±1}]` stable under `t -> t^{-1}` and
   `Psi in B_n` with `rho_n(Psi) = I mod a`. Then `M_{Psi Gamma} = M_Gamma mod a` for
   **every** `Gamma in B_n`, including those whose underlying permutation sends `3` to `1`
   or to `2`.

## Why this is not covered by Lemma 3.1

Lemma 3.1 of the artifact is the bridge from Theorem A (a statement about the intersection
form `I` of loop classes, valid for all `Gamma in B_5`) to `M`. Its construction explicitly
requires that "the circle is small enough to miss `alpha`". When `p = p_1` or `p = p_2` that
hypothesis is unsatisfiable: `alpha` runs from `p_1` to `p_2`, so every small circle about
`p` crosses `alpha°` exactly once.

Lemma 3.1 is then **false as stated**. Take `A` a simple arc from `p_*` to `p_1` meeting
`alpha°` nowhere. Then `M(alpha, A) = 0` while `I([c~_A]) = ±t^{k_0} != 0`, the one crossing
being the one contributed by the small circle. Redoing the computation gives

    I([c~_A]) = (1 - t^s) M_A + eps_0 t^{k_0}.

For two arcs `A` and `B` sitting over different sheets the two correction terms differ by
`eps_0 t^{k_0}(t^delta - 1)`, which lies in `(t - 1)` but not in `(F·(t-1))`. So the mod-`F`
conclusion does not follow, and Corollary 3.2 is likewise unproved, for those arcs.

## What depends on it

- Part 2 of `brunnian-burau-kernel-mod-cyclotomic-products-nontrivial`, as quantified over
  every `Gamma in B_5`. For **pure** `Gamma` — in particular for every
  `Gamma in K_5 = pi_1(D_4, p_5)`, which is the only case the "what this kills" discussion and
  `brunnian-four-braids-have-five-strand-moody-witness` use — the arc `(beta_*^3)Gamma` ends
  at `p_3` and Lemma 3.1 applies, so that case is unaffected.
- The same over-broad quantifier is inherited from Proposition 9.1 and Theorem B of the
  artifact, so it also touches `parity-clean-arc-counts-see-only-burau-mod-t-plus-one` and
  `parity-correcting-push-fails-for-a-brunnian-four-braid`. Recorded here, not yet acted on:
  the operative content of both is about pure braids.

## What would settle it

A corrected bridge lemma carrying the boundary term, showing that the `eps_0 t^{k_0}` terms of
the two arcs agree, or agree modulo `F`; or a normalisation of the small circle at `p_1`, `p_2`
that removes the forced crossing. Failing that, restrict every statement of the form
"for every `Gamma in B_5`" to pure `Gamma`, which is what the arguments actually prove.

## Attempts

- 2026-09-18 (referee pass on `brunnian-burau-kernel-mod-cyclotomic-products-nontrivial`):
  recorded as the gap, with the counterexample to Lemma 3.1 above. No repair attempted.

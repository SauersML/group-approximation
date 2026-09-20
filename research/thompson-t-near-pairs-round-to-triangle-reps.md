---
rg: 2
id: thompson-t-near-pairs-round-to-triangle-reps
kind: claim
title: "Uniform rounding through the triangle cover: every sufficiently T-near exact pair phi of Z/4 * Z/3 has phi (+) phi-bar (+) 1_k operator-norm close to an honest representation of Delta(4,3,5), uniformly in dimension"
distinct_from:
  torus-knot-groups-are-rq-stable: that is Willett's R_q-stability of K(3,4), with an arbitrary auxiliary block factoring through a finite quotient; this asks for honest Delta(4,3,5)-representations with only a trivial auxiliary block, after doubling by the conjugate.
  torus-knot-group-k34-is-matricially-stable: that is unpadded, same-dimension stability of K(3,4); this concerns the cocompact Fuchsian quotient Delta(4,3,5), only on T-near pairs, and allows doubling and trivial padding.
  dadarlat-matricial-stability-obstruction: that is the H^2 obstruction to unpadded stability; the conjugate summand phi-bar cancels the pentagon winding kappa_P, which is the only such obstruction here (item 4 of thompson-t-not-mf-iff-triangle-gap-and-rounding).
  thompson-t-pentagon-winding-rigidity: that is (PW); the undoubled form of this claim implies (PW), and this doubled form does not obviously do so.
---

**OPEN.** This is condition (S_T) of `thompson-t-not-mf-iff-triangle-gap-and-rounding`.

For every `eps > 0` there is `delta > 0` with the following property. Let `phi = (A,B)` in `U(n)`, for any
`n`, have `A^4 = B^3 = 1` and operator-norm defect `< delta` on `r_1`, `r_2` and `(ba)^5`. Then there are
`k >= 0` and a representation `rho : Delta(4,3,5) -> U(2n+k)` with

```text
|| rho(s) - (phi (+) phi-bar (+) 1_k)(s) || < eps       (s = a, b).
```

## What is known

- **It is necessary.** Its failure makes `T` MF.
- **Automatic in each fixed dimension.** Take `delta = delta_n`. So the claim is purely about uniformity in
  `n`.
- **The target implies it**, trivially.
- **The doubling cannot be dropped for free.** The undoubled form implies (PW), even when the trivial
  block is replaced by any honest representation.
- **A T-free sufficient condition.** The claim follows from (S_Delta), which does not mention `T`:

  > **(S_Delta)** For every `eps` there is `delta` such that every exact pair `phi` with
  > `||(BA)^5 - 1|| < delta` has `phi (+) phi-bar (+) 1_k` eps-close to an honest `Delta`-representation.

  (S_Delta) is operator-norm stability of the cocompact Fuchsian group `Delta(4,3,5)`, up to conjugate
  doubling and trivial padding, on pairs that are exact on the free factors.

## Relation to the literature

Willett, arXiv:2408.13350, is the nearest literature. None of it applies directly.
- **Remark 1.12** says that it is not known whether "R_q-stable" can be replaced by "stable" for surface
  groups other than the torus, the Klein bottle and the projective plane: "We do not if 'R_q-stable' can be
  replaced by 'stable' in Theorem 1.10 other than in the case of the torus or Klein bottle covered by Theorem
  1.5, and the elementary case of the projective plane."
- **Remark 1.13** says that flexible stability "only allows block sum with an auxiliary trivial
  representation which is 'small' relative to the dimension …; Theorem 1.10 gives no control on the size of
  the auxiliary representation θ appearing in Definition 1.6".
- **Section 1.7** says: "Another issue we have nothing to say about is what happens in the presence of finite
  subgroups." `Delta(4,3,5)` has torsion.

So (S_Delta) is at least as hard as an open case of Willett's programme. It asks for
- trivial padding in place of `R_q` padding,
- for an orbifold group, and
- in operator norm.

By `thompson-t-padded-cover-stability-is-inert`, nontrivial padding is useless here. (S_T) is weaker than
(S_Delta) only in that it may use the smallness of `r_1, r_2`.

## Remark (recalled, not load-bearing, no citation claimed)

An honest `Delta`-representation needs a product relation `A · B · (BA)^(-1) = 1` among unitaries with
prescribed spectra. By the multiplicative Horn problem such products are constrained by linear
inequalities on the eigenvalue angles. Trivial padding adds the eigenvalue 1 to all three classes at once,
and it is not clear that this can repair a violated inequality. A counterexample to (S_Delta) of this kind
would be a family of exact pairs with `(BA)^5` close to 1 whose rounded spectral data violate a Horn-type
inequality by an amount that trivial padding does not remove. It would *not* refute (S_T) unless it also
had small `r_1, r_2` defect.

## Attempts

- **2026-09-19 (swarm-0917-w17-w17-ptl-follow).** Node created.
  - *Padding.* Nontrivial padding was shown to be inert (see above).
  - *Doubling.* The doubling was shown to be forced unless (PW) holds.
  - No uniform rounding estimate was found. Defect-diminishing at honest `Delta`-representations would
    need a uniform `H^1`-type estimate with adjoint coefficients over all finite-dimensional unitary
    representations of `Delta`. No such estimate is known in operator norm.

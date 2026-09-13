---
rg: 2
id: toms-diagonal-quotient-has-nonconstant-continuous-ranks
kind: claim
title: Toms's non-simple limit has a uniformly distributed element and a diagonal quotient with non-constant continuous ranks, so rank obstructions must use off-diagonal traces
distinct_from:
  toms-schubert-algebra-continuous-ranks-are-constant: that conjectures constancy of continuous ranks in Toms's algebra; this proves that the conjecture fails on the diagonal quotient, so any proof must see traces that do not factor through it.
  doubling-ah-finite-stage-continuous-ranks-are-constant: that shows orthogonal sums of finite-stage elements have constant continuous ranks; this realizes non-constant continuous ranks on a quotient by a norm limit that is not such a sum.
  stw23-skew-product-diffuse-fibres-have-all-ranks: that realizes ranks in skew products with diffuse fibres; this exhibits the diffuse element inside Toms's tower and shows exactly where the product mechanism stops working.
---

Let `A = lim (A_L, phi_L)` be the non-simple limit of Toms's Section 4
(arXiv:2606.12188v2), with `X_1 = Gr(d,2d)`, `X_(L+1) = X_L x X_L x CP^(j_L)`,
`A_L = q_L (C(X_L) tensor K) q_L`, and
`phi_L(a) = (pi_1^* a tensor gamma_(L,1)) + (pi_2^* a tensor gamma_(L,2))`.

**Theorem.**
1. **A uniformly distributed element.** Write `q_L = sum_l 1_l` over the
   `N = 2^(L-1)` leaf summands `lambda_l^* q_1 tensor gamma_l`, indexed by binary
   strings. There is `b in A_+` with `||b|| <= 1` whose spectral law is Lebesgue
   measure on `[0,1]` for **every** `tau in T(A)`.
2. **The diagonal quotient.** Put `D_1 = X_1` and
   `D_(L+1) = { (x, x, l) : x in D_L, l in CP^(j_L) }`. Restriction to the `D_L`
   defines a quotient `pi: A -> A_D`. Every Lemma 2 point trace of Toms factors
   through `A_D`.
3. **Non-constant continuous ranks there.** For `h in C(X_1)` with
   `0 <= h <= 1`, the element `pi((b - (1 - h))_+)` of `A_D` has rank
   `tau -> tau(h)` on `T(A_D)`. This rank is continuous, and non-constant when
   `h` is non-constant.
4. **Toms's pair is not degeneracy-forcing on the diagonal.** On `D_2` there is
   a bundle map `p_2 -> q_2` that vanishes nowhere. Also
   `Delta_(d_L)(c(q_L - p_L))` restricts to `0` on `D_L` for `L >= 2`.

**Consequence.** Constancy of continuous ranks in `A` or `B`
(`toms-schubert-algebra-continuous-ranks-are-constant`) cannot be proved from
traces factoring through `A_D`. An obstruction has to use the independence of
leaf coordinates. At such traces the central elements `h(x_l)` vary from leaf
to leaf, while `b` assigns fixed thresholds to leaves. So the joint law of
`(b, h)` can be concentrated on a graph, and the skew-product realizer
`(b - (1 - h))_+` loses continuity.

So the realizer problem in `A` reduces to a sharp **decorrelation question**. Is
there a uniformly distributed `b'` whose joint law with every stage-central
scalar is a product at every trace? Toms's twists obstruct the continuous
re-assignment of thresholds between leaves, because it rotates twisted
summands. This is the same Thom–Porteous obstruction, now visible only off the
diagonal.

**Model test.**
- *Part 1 needs equal leaf ranks.* Every `1_l` has fibre rank `d` in `q_L` of
  rank `Nd`, so its trace is `1/N` at every point. With unequal leaf ranks the law
  would depend on the trace.
- *Part 3 fails in `A` itself for this element.* At a point `x in X_L` with
  `h(x_l) = 1 - k_l/N` on every leaf (`k_l/N` the threshold of leaf `l` in
  `b_L`), `(b_L - (1 - h))_+` vanishes at `x`, although `tau_x(h)` can be near
  `1/2`. So the diagonal hypothesis is load-bearing.

Proof: `toms-diagonal-quotient-nonconstant-ranks-proof`. Internal derivation,
unreviewed.

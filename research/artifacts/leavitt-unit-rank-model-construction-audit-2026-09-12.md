# Rank models of the Leavitt unit group: the algebra route is dead, the units route is open

Lane `gk-l-gate-pos`, 2026-09-12. Supports the claims
`leavitt-algebra-has-no-unital-rank-model` and the construction record on
`binary-leavitt-unit-group-is-f2-linear-sofic`.

Throughout `R = L_(F_2)(1,2) = F_2<s_0,s_1,t_0,t_1 | t_i s_j = delta_ij, s_0t_0+s_1t_1=1>`,
and `H = R^x` its unit group, `H = EL_n(R) = GL_n(R)` for every `n >= 2`
(Khanh--Thanh). A **rank ultraproduct** over a field `F` is
`M = prod_omega M_(n_k)(F) / d_omega`, with `d_omega` the ideal of
normalized-rank-null sequences. `M` is unit-regular, hence directly finite:
`rk(1 - ab) = rk(1 - ba)` for all `a,b` (Arzhantseva--Paunescu,
arXiv:1212.6780, Proposition 2.8; the map `v -> bv` carries `ker(1-ab)`
bijectively onto `ker(1-ba)` because `v = abv` on that kernel).

## 1. No unital rank model of the algebra `R`

**Proposition.** There is no unital `F`-algebra homomorphism `phi : R -> M`
into any rank ultraproduct `M` over any field `F`.

*Proof.* `R` is simple (the Leavitt algebra of the rose with two petals is a
simple ring; Leavitt 1962, or the Leavitt path algebra of a graph with one
vertex and two loops). A unital homomorphism is nonzero, so its kernel is a
proper two-sided ideal, hence `0`, so `phi` is injective. Now
`phi(t_0) phi(s_0) = phi(t_0 s_0) = phi(1) = 1_M`. `M` is directly finite, so
`phi(s_0) phi(t_0) = 1_M = phi(1)`, i.e. `phi(s_0 t_0 - 1) = 0`. But
`s_0 t_0 - 1 != 0` in `R`, contradicting injectivity. QED

The same argument kills any field: direct finiteness of `M` is characteristic
free. It also kills any unital rank-approximate homomorphism
`phi_k : R -> M_(m_k)(F)` (additive, `rk(phi_k(ab) - phi_k(a)phi_k(b)) -> 0`,
`rk(phi_k(1) - 1) -> 0`, `rk(phi_k(a)) not-> 0` for `a != 0`): assembling the
`phi_k` gives exactly a unital injective `phi : R -> M`, which cannot exist.

This is the rank-metric shadow of `binary-leavitt-algebra-not-directly-finite`:
`R` is not directly finite, and rank ultraproducts are, so `R` cannot sit
unitally inside one. Contrast `linear-sofic-group-algebra-is-stably-finite`,
which embeds the *group algebra* `F[G]` of a linear sofic group; that needs the
group elements to go to invertibles, which the isometries `s_i` are not.

## 2. What this forbids, and what it does not

**Forbidden: the algebra route to a model of `H`.** The natural way to build a
rank model of `H = EL_n(R)` is to first model the coefficient algebra and then
take elementary matrices:

```text
e_ij(a) = 1 + a E_ij   |-->   1 + phi(a) E_ij .
```

The Steinberg relation `[e_12(a), e_23(b)] = e_13(ab)` forces
`phi(ab) = phi(a) phi(b)`, and `e_ij(a) e_ij(b) = e_ij(a+b)` forces additivity,
so `phi` must be an (approximate) unital algebra homomorphism `R -> M`. Section 1
rules that out. So **no rank model of `H` extends to a rank-approximate
homomorphism of the ambient algebra `R`.** Any model must be genuinely
non-multiplicative on `R`.

**Not forbidden: a model of the units.** The obstruction is about `s_i`, which
are one-sided invertible non-units. In `EL_n(R)` they never appear inverted:
`e_ij(a)^{-1} = e_ij(-a)`, so `s_i` sits only as an off-diagonal entry of a
matrix whose inverse re-uses `s_i`, never `s_i^{-1}`. Direct finiteness of `M`
therefore places no constraint of the Section 1 kind on a group homomorphism
`sigma : EL_n(R) -> M^x`. This is the gap that keeps
`binary-leavitt-unit-group-is-f2-linear-sofic` open: the algebra is provably
un-modellable in rank, while the unit group might still be modellable, because
a group model may read the letters `s_i, t_i` only through the invertible
elementary matrices they build.

## 3. Constructions tried, and where each dies

Every construction below aims at `sigma : H -> M^x` and fails against a recorded
constraint.

1. **Graded path-space truncation.** `R` acts on `F_2[{0,1}^*]` by
   `s_i : e_w -> e_iw`, `t_i : e_iw -> e_w` (`e_jw -> 0`, `j != i`),
   `t_i e_empty = 0`. Truncating to strings of length `<= N` forces a choice at
   level `N` (send `s_i` of a leaf to `0`, or wrap). The tree `{0,1}^(<=N)` has
   `2^N` leaves and `2^N - 1` internal nodes, so the error is supported on a
   `1/2` fraction and the normalized-rank defect is bounded below by a constant.
   This is the exponential-growth (paradoxicality) obstruction, and it is the
   precise mechanism behind "the natural Cantor truncation is dead" recorded on
   `binary-leavitt-unit-group-is-f2-linear-sofic`. It is fatal to any model that
   represents the algebra, consistent with Section 1.

2. **Model the algebra, then take elementary matrices.** Dead by Section 2:
   there is no approximate unital algebra homomorphism to assemble.

3. **Genuine finite-dimensional representation of `H`.** Dead: `H` is finitely
   generated, infinite and simple, so every genuine finite-dimensional
   representation is trivial (recorded on the target). Models must be genuinely
   almost multiplicative.

4. **A model where the nine-leaf Kazhdan `Gamma` fixes a linear-size piece.**
   Excluded in every tensor degree by
   `leavitt-rank-models-kazhdan-fixed-ideals-are-global`.

## 4. Where a positive construction must now live

A model of `H` must (i) be genuinely non-multiplicative on `R` (Section 2),
(ii) not factor through a finite group (Section 3.3), (iii) respect the global
fixed-ideal constraint of Section 3.4, and (iv) place its multiplicative defect
below linear rank scale, since the linear-scale layer is conserved for free
(`rank-ultraproduct-compressors-conserve-fixed-right-ideals`). The remaining
concrete question is whether the Leavitt multiplication `(a,b) -> ab` can be
carried on the off-diagonal blocks of elementary matrices with `o(n_k)` rank
defect while never inverting the isometries. Property (T) alone does not decide
it in either direction: it supplies no rank rounding over a finite field
(`kazhdan-group-rank-models-admit-no-expander-decomposition`). No construction
in this lane produced such a model, and no obstruction to one was found; the
question stays open, and it is the same heart as the rank row
`f2-linear-sofic-groups-kill-rigid-compression-defects`.

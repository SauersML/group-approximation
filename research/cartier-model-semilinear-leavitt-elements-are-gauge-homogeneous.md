---
rg: 2
id: cartier-model-semilinear-leavitt-elements-are-gauge-homogeneous
kind: claim
title: In the Frobenius–Cartier model of L_{F_2}(1,2^d) on a char-2 field with a finite p-basis, Frobenius-semilinearity of twist k is exactly gauge degree k, so no semilinear (multiplication, Frobenius, Cartier, derivation-type) construction yields F_2[Z^2] in the Leavitt algebra
distinct_from:
  algebraic-core-gradings-bound-homogeneous-laurent-rank: that kills commuting gauge-homogeneous units; this identifies the gauge grading with Frobenius-semilinearity in a faithful function-field model, so it transfers that kill to every operator-theoretic construction by semilinear maps, and adds that the only multiplication operators in the image are the constants.
  f2-z4-embeds-in-z2-sft-boundary-product-hosts: that is the decisive fork; this kills one class of YES constructions for its sufficient condition (F_2[Z^2] inside L_∂ ≅ L_{F_2}(1,2)).
  constant-c3-normalizer-is-f4-leavitt-semilinear: that is about semilinearity over the coefficient field F_4 of a normalizer; this is about semilinearity of operators on a representation space with respect to Frobenius of a function field.
artifacts:
  - research/cartier-semilinear-leavitt-gauge-homogeneity-proof.md
---

**ESTABLISHED (unreviewed).** Let `K` be a field of characteristic 2 with a finite
p-basis `t = (t_1, …, t_d)`, `d >= 1`. So `K` is a free `K^2`-module with basis the
monomials `t^e`, `e ∈ {0,1}^d`. Examples are `F_2(t_1, …, t_d)`, `F_2((t))`, and
function fields of curves (`d = 1`). Let `n = 2^d` and `L = L_{F_2}(1,n)`, with
generators `S_e, S_e^*` for `e ∈ {0,1}^d`.

**Cartier model.** Put `S_e f = t^e f^2`. Let `S_e^*` be the `e`-th Cartier
coordinate, so `g = Σ_e t^e (S_e^* g)^2`. These maps are `F_2`-linear on `K` and
satisfy `S_e^* S_{e'} = δ_{e e'}` and `Σ_e S_e S_e^* = 1`. They define a unital
representation `π : L -> End_{F_2}(K)`. It is faithful because `L` is simple.

**Theorem.** Fix `x ∈ L` and `k ∈ Z`. The following are equivalent:
1. `x ∈ L_k`, the gauge-degree-`k` component, spanned by `S_α S_β^*` with
   `|α| - |β| = k`;
2. `π(x)` is Frobenius-semilinear of twist `k`: there is `N >= max(0, -k)` with
   `π(x)(c^{2^N} g) = c^{2^{N+k}} π(x)(g)` for all `c, g ∈ K`.

**Corollaries.**
- **(C1) Constants only.** `π(L) ∩ {multiplication by f : f ∈ K} = F_2`. For
  example, multiplication by `t` is not in `π(L)`.
- **(C2) Linear part is the AF core.** `π(L) ∩ ⋃_N End_{K^{2^N}}(K) = π(L_0)`, the
  ultramatricial core. The derivation `d/dt` (for `d = 1`) is `π(S_0 S_1^*)`, and it
  is nilpotent.
- **(C3) Class kill.** Let `u, v` be commuting units of `L` whose images are both
  semilinear, with any twists and any `N`. Then `u, v` do not generate `F_2[Z^2]`.
  The same holds in `M_m(L)` for semilinear matrices of one common twist.

**Obstruction (the invariant and where every member dies).** The invariant is the
Frobenius twist. By Artin's independence of characters, a twist-`k` semilinear
operator in `π(L)` is gauge-homogeneous of degree `k`. The gauge grading has rank 1
and a locally finite core. So
`algebraic-core-gradings-bound-homogeneous-laurent-rank` (A), with `s = 1`, makes
some `u^a v^b`, `(a,b) != 0`, algebraic.

Every construction of `F_2[Z^2] ⊂ L` dies at this step if it:
- realizes the Laurent generators on a function field as multiplication operators;
- uses twisted Frobenius or Cartier maps;
- uses Hasse-type `K^{2^N}`-linear operators;
- or uses any product of these with one twist.

A YES witness for the sufficient condition of
`f2-z4-embeds-in-z2-sft-boundary-product-hosts` must therefore act on every
p-basis Cartier model by operators that mix at least two Frobenius twists, and
cannot be linear over any `K^{2^N}`.

**What stays open.** Non-semilinear operators, i.e. non-homogeneous elements, are
untouched. That is exactly the gap between (A) and the commutative-rank conjecture.

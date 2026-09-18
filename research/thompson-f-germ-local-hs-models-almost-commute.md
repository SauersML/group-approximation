---
rg: 2
id: thompson-f-germ-local-hs-models-almost-commute
kind: claim
title: Unitary models of Thompson's F with an approximately covariant, germ-local dyadic frame almost commute
distinct_from:
  thompson-f-spatial-permutation-models-almost-commute: that treats permutation models that follow F's action on points; this treats unitary HS models and infinite-dimensional representations with a projection-valued frame on the Cantor set. These include Koopman, Pythagorean and Cuntz-algebra representations and their finite-rank compressions, which have no underlying point set.
  thompson-v-covariant-cantor-representations-are-not-amenable: for V, covariance alone kills amenability, because every proper clopen can be moved into disjoint copies. For F the end cylinders cannot be moved, covariance alone is compatible with witnesses (see Scope), and the extra invariant is germ-locality.
  thompson-f-following-models-separate-iff-mean-charges-commutator: that is a separation criterion for models following an action through a mean; this proves that the mean carried by a covariant frame lives on the two end germs, and that locality then makes the commutator trivial.
  thompson-f-hyperlinear-models-normalize-a-full-masa: that asks for a masa frame in every witness; this shows that a dyadic frame which is also germ-local forces non-separation. So a frame extracted from a witness can never be local.
---

**ESTABLISHED.** **Setting.**
- `X = {0,1}^N` is the Cantor set, and `F` acts on it by finite prefix replacements (tree-pair
  diagrams). `x_0, x_1` are the standard generators, and `c = [x_0, x_1]` fixes the cylinders
  `[00]` and `[11]` pointwise.
- Every `g ∈ F'` fixes `[0^m] ∪ [1^m]` pointwise for some `m`.
- For a finite binary word `w`, `[w]` is its cylinder. A *dyadic frame* on a Hilbert space `H` is a
  family of commuting projections `P_w` with `P_∅ = 1` and `P_w = P_{w0} + P_{w1}`. Write `P_C` for
  the sum over a finite disjoint cylinder decomposition of a clopen set `C`.

**(A) Representations.** Let `π` be a unitary representation of `F` on `H` with a dyadic frame
satisfying:
- **covariance:** `π(g) P_C π(g)* = P_{gC}`;
- **germ-locality:** `π(g) P_w = π(h) P_w` whenever `g` and `h` agree on `[w]`. In particular
  `π(g) P_w = P_w` when `g` fixes `[w]` pointwise.

Let `Φ` be any state on `B(H)` with `Φ(π(g) T π(g)*) = Φ(T)` for all `g`. Then:
- `Φ(P_C) = 0` for every clopen `C` avoiding both points `0^∞` and `1^∞`;
- `Φ(π(g)) = 1` for every `g ∈ F'`.

So the amenable trace `Φ|_{C*(π(F))}` has regular weight `t = 0` in `thompson-f-character-simplex`.
Moreover, finite-rank projections `Q_n` with `||π(g)Q_n − Q_n π(g)||_2 / ||Q_n||_2 → 0` give
compressed HS models `Q_n π Q_n` in which `||Q_n π(c) Q_n − Q_n||_2 / ||Q_n||_2 → 0`.

**(B) Finitary HS version.** Let `M_n` carry the normalized trace `tr` and `||X||_2 = tr(X*X)^(1/2)`.
Let `U_g`, for `g` in a finite window `W ⊆ F` containing `e` with `U_e = 1`, be unitaries, and let
`(P_w)` be a dyadic frame in `M_n`. Fix `g ∈ W` that fixes `[0^m] ∪ [1^m]` pointwise, and set
`C = X \ ([0^m] ∪ [1^m])`. Choose `L ≥ 1` with `x_0^L(1 − 2^-m) < 2^-m` in `[0,1]`, and `N ≥ 1`.
Assume the following two bounds.
- **Covariance defect.** `||U_h P_C U_h* − P_{hC}||_2 ≤ η_cov` for `h = x_0^(iL)`, `1 ≤ i < N`.
- **Locality defect.** `||(U_g − 1) P_w||_2 ≤ η_loc` for `w ∈ {0^m, 1^m}`.

Then

`||U_g − 1||_2 ≤ 2 η_loc + 2 sqrt(1/N + η_cov)`.

For `g = c` one may take `m = 2`, `L = 3` (`x_0^3(3/4) = 1/8 < 1/4`). So along any sequence of models
with covariance and locality defects `→ 0` on a fixed window, `||U_c − 1||_2 → 0`. This is the
opposite of a witness for `thompson-f-is-hyperlinear`.

**Members killed** (exactly covariant and germ-local, so (A) applies to them and to every finite-rank
almost-invariant compression of them):
- Koopman representations `U_g ξ(x) = (d(g_*μ)/dμ)^(1/2)(x) ξ(g^-1 x)` for any `F`-quasi-invariant
  measure `μ` on `X` (or on `[0,1]`, through dyadic intervals), with `P_w = 1_[w]`. This includes
  `ℓ^2` of any `F`-orbit, i.e. the quasi-regular representations `ℓ^2(F/Stab(x))`.
- Pythagorean (direct-sum Jones) representations built from `A*A + B*B = 1`, with `P_w` the
  projection onto the leaf-`w` component. Refining a leaf is the isometry `ξ ↦ (Aξ, Bξ)` into the
  two child components, so the decomposition is compatible, and `π(g)` just relabels leaf
  components by prefix replacement.
- Restrictions to `F ≤ V ≤ U(O_2)` of arbitrary representations of the Cuntz algebra `O_2`, with
  `π(g) = Σ_i S_{u_i} S_{v_i}*` for a tree pair `(v_i → u_i)` and `P_w = S_w S_w*`. Refining the pair
  below `w` gives `π(g) P_w = Σ_{v_i ⊇ w} S_{u_i} S_{v_i}*`, which is determined by `g|_[w]`.
- The unitary analogue of the spatial permutation models (permutation matrices following points,
  with the cylinder partition as frame). Here `η_cov²` and `η_loc²` are at most a constant times the
  fraction of bad points of the words used, so (B) recovers the qualitative content of that node.

**Invariant and dying step.** The invariant is germ-locality of the frame at the two end germs.
Every member dies at the same step. Covariance plus centrality of the limit state forces the frame
mean onto the two fixed ends: interior clopens have `N` disjoint `x_0`-translates, so their mass is
`≤ 1/N`. Locality then says `F'` acts trivially on the entire surviving mass. Cauchy–Schwarz
transfers this to `Φ(π(g)) = 1`.

**Scope.**
- *Covariance alone does not suffice, and a covariance-only version would be equivalent to the target.*
  Let `σ_n` be any HS witness for `thompson-f-is-hyperlinear`. Let `λ_n` be the permutation models on
  `x_0`-ray windows from `thompson-f-spatial-permutation-models-almost-commute`, whose cylinder frames
  have covariance defect `→ 0` on each fixed window. Then `λ_n ⊗ σ_n` is again a witness: relator
  defects add, and `λ_n(c) ≈ 1`, so `||λ_n(c) ⊗ σ_n(c) − 1||_2 ≈ ||σ_n(c) − 1||_2`. The frame
  `P_w ⊗ 1` is approximately covariant, but its locality defect at `c` is about `||σ_n(c) − 1||_2`.
  So "approximately covariant frame ⇒ almost commuting" is equivalent to `thompson-f-is-not-hyperlinear`.
  Locality is the hypothesis that makes the obstruction provable, and no witness can satisfy it.
- *Not covered.* Tensor-type Jones representations (Temperley–Lieb–Jones and other tensor-category
  functors, `ξ ↦ R(ξ)` into `H ⊗ H`) and Koopman representations of generalized Bernoulli actions
  over `X`. These carry no evident germ-local dyadic frame. They are the only natural families of
  unitary representations of `F` that this obstruction leaves open.
- Elementary. It decides neither `thompson-f-is-hyperlinear` nor `thompson-f-is-not-hyperlinear`;
  it excludes the direct-sum/Cuntz/Koopman construction class.

Proof route: `thompson-f-germ-local-hs-models-almost-commute-proof`.

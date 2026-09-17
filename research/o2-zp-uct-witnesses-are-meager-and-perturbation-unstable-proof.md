---
rg: 2
id: o2-zp-uct-witnesses-are-meager-and-perturbation-unstable-proof
kind: route
title: Show the Rokhlin condition is G_delta and dense by the strongly self-absorbing tensor trick, then read off the category dichotomy for invariant sets
target: o2-zp-uct-witnesses-are-meager-and-perturbation-unstable
requires: [outer-actions-on-o2-kk-g-contractible-iff-rokhlin, cartan-respecting-o2-automorphisms-give-uct-crossed-products, barlak-li-uct-iff-z2-z3-actions-fix-cartan]
artifacts:
  - research/artifacts/uct-o2-cyclic-actions-2026-09-12.md
---

Fix a prime `p`, a dense sequence `(x_i)` in the unit ball of `O_2`, and the
Rokhlin model `μ = id ⊗ ⊗_n Ad(λ)` on `O_2 ⊗ M_(p^∞) ≅ O_2`, where `λ ∈ M_p` is
the cyclic permutation matrix.  Definitions of the Rokhlin property and of
strong approximate innerness are as recorded in
`izumi-rokhlin-approximately-representable-duality`, item 1.

## Step 0. The space

Let `End_1(O_2)` be the unital \*-endomorphisms with the metric
`d(θ, θ') = Σ_i 2^(−i) ‖θ(x_i) − θ'(x_i)‖`.  A `d`-Cauchy sequence converges
pointwise on `(x_i)`.  The maps are contractive, so it converges pointwise on
`O_2`, and the limit is a unital \*-endomorphism.  So `End_1(O_2)` is complete
and separable.  `Act_p = {θ : θ^p = id}` is closed, because composition is
jointly continuous for isometric maps in this topology.  Each `θ ∈ Act_p` is
bijective with inverse `θ^(p−1)`, so the topology agrees with the point-norm
topology of `Aut(O_2)` (which also controls inverses).  So `Act_p` is Polish.
Conjugation `(σ, α) ↦ σ α σ^(−1)` is continuous.

## Step 1. `R_p` is G_δ

For `k ≥ 1` let `U_k` be the set of `α ∈ Act_p` for which there are projections
`e_0, …, e_(p−1) ∈ O_2` with `Σ_j e_j = 1`, `‖[e_j, x_i]‖ < 1/k` for `i ≤ k`, and
`‖α(e_j) − e_(j+1 mod p)‖ < 1/k` for all `j`.  For fixed projections the last
condition is open in `α` and the others do not involve `α`.  So `U_k` is open.

`R_p = ⋂_k U_k`.  If `α` is Rokhlin, lift the equivariant unital map
`C(Z_p) → F_∞(O_2)` to sequences of projections: projections in `ℓ^∞/c_0` lift
to projections, and relations holding exactly in the quotient hold up to `o(1)`
along the sequence.  This gives `α ∈ U_k` for all `k`.  Conversely, choosing
`e^(k)_j` for each `k` gives elements of `(O_2)_∞ ∩ O_2'` with `Σ_j e_j = 1`,
`α_∞(e_j) = e_(j+1)`, and each `e_j` a projection.  That is a unital
equivariant \*-homomorphism `(C(Z_p), σ) → F_∞(O_2)`.

## Step 2. `R_p` is dense

`O_2` is strongly self-absorbing.  So there is an isomorphism
`φ : O_2 → O_2 ⊗ O_2` approximately unitarily equivalent to `x ↦ x ⊗ 1`
(Toms--Winter's definition; for `O_2`, Kirchberg--Phillips, or Rørdam's
`O_2 ⊗ O_2 ≅ O_2` with all unital endomorphisms approximately inner).  Choose
unitaries `w_n` with `ψ_n := Ad(w_n) ∘ φ` satisfying `ψ_n(x) → x ⊗ 1` for every
`x`.

Let `α ∈ Act_p` and put `β_n := ψ_n^(−1) ∘ (α ⊗ μ) ∘ ψ_n ∈ Act_p`.  For
`x ∈ O_2`, since `ψ_n` is isometric,

`‖β_n(x) − α(x)‖ = ‖(α ⊗ μ)(ψ_n(x)) − ψ_n(α(x))‖`
`≤ ‖ψ_n(x) − x ⊗ 1‖ + ‖α(x) ⊗ 1 − ψ_n(α(x))‖ → 0`,

using `(α ⊗ μ)(x ⊗ 1) = α(x) ⊗ 1`.  So `β_n → α`.

`α ⊗ μ` is Rokhlin.  If `(e_j)` are Rokhlin projections for `μ` for a finite
set `G` and tolerance `δ`, then `1 ⊗ e_j` are exactly permuted up to `δ` by
`α ⊗ μ`, and they commute up to `δ` with `a ⊗ b` for `b ∈ G`.  Finite sums of
elementary tensors are dense, so this suffices.  The Rokhlin property is
invariant under conjugation by isomorphisms, so `β_n ∈ R_p`.

## Step 3. `R_p` is one conjugacy class, and `R_p ⊆ S_p ∩ Out_p`

Rokhlin actions of `Z_p` are outer.  If `α = Ad(w)`, the Rokhlin projections
approximately commute with `w`, so `e_1 ≈ α(e_0) = w e_0 w* ≈ e_0`.  But `e_0`
and `e_1` are orthogonal, so `e_0 ≈ 0`, and likewise every `e_j ≈ 0`,
contradicting `Σ_j e_j = 1`.  Since `p` is prime, every nontrivial power is
also non-inner.  By item 2 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`,
every outer Rokhlin action on `O_2` is conjugate to the model `μ`.

The model is strongly approximately inner: `v_n = 1 ⊗ λ^(⊗n) ⊗ 1` is a unitary
with `μ(v_n) = v_n`, and `Ad(v_n) → μ` pointwise.  Strong approximate innerness
is conjugation invariant.

## Step 4. `S_p` is G_δ

For `k ≥ 1` let `V_k` be the set of `α` for which there is a unitary `u` with
`‖α(u) − u‖ < 1/k` and `‖α(x_i) − u x_i u*‖ < 1/k` for `i ≤ k`.  For fixed `u`
these conditions are open in `α`, so `V_k` is open.  `S_p ⊆ ⋂_k V_k`.

Conversely, let `α ∈ ⋂_k V_k` with witnesses `u_k`.  Put
`a_k = (1/p) Σ_(j<p) α^j(u_k)`.  It lies in `O_2^α`, and
`‖a_k − u_k‖ ≤ (1/p) Σ_j j/k ≤ p/k`.  For large `k`, `a_k` is invertible and its
unitary part `v_k = a_k |a_k|^(−1)` lies in `O_2^α`.  (`O_2^α` is a unital
C\*-subalgebra containing `a_k`, and functional calculus stays inside it.)
Also `‖v_k − u_k‖ = O(p/k)`.  So `Ad(v_k) → α` pointwise, and `α ∈ S_p`.

So `S_p` is a G_δ containing the dense G_δ `R_p`, hence comeager.  This is
item 1.

## Step 5. The dichotomy (item 2)

Let `Y` be conjugation invariant.  If `Y` contains one Rokhlin action, it
contains the whole conjugacy class `R_p` (Step 3), which is comeager.
Otherwise `Y ⊆ Act_p ∖ R_p`, which is meager because `R_p` is a dense G_δ.

Let `X ⊇ R_p` carry the subspace topology.  `R_p` is dense in `X`: an open
set `U ∩ X` with `U` open in `Act_p` and nonempty meets `R_p`, since `R_p` is
dense in `Act_p` and `R_p ⊆ X`.  `R_p` is a G_δ of `X`.  A space with a dense
completely metrizable subspace is a Baire space, so `X` is Baire.  The
dichotomy relativizes verbatim.

## Step 6. Witness sets (item 3)

Each set is conjugation invariant, since UCT for the crossed product, Cartan
fixing, strong approximate innerness, outerness and KK-contractibility of the
crossed product are all conjugation invariants.  Each set is disjoint from
`R_p`:

- **`W^Cart_p`.**  The model `μ` fixes the Cartan subalgebra
  `D_2 ⊗ D_(p^∞)`: `λ` normalizes the diagonal masa of `M_p`, and a tensor
  product of Cartan pairs from topologically principal étale groupoids is the
  Cartan pair of the product groupoid (Renault).  Conjugates fix the image
  Cartan.
- **`W^UCT_p`.**  For outer strongly approximately inner actions this is
  `W^Cart_p`, by Barlak--Li II Corollary 4.15 (recorded in
  `barlak-li-p-half-iff-zp-actions-fix-cartan`, part (a)).  Directly, Rokhlin
  crossed products satisfy the UCT (`gardella-rokhlin-actions-preserve-uct`).
- **`W^sai_p`.**  Step 3.
- **`W^det_p`.**  By definition.

Step 5 then gives meagerness.

## Step 7. Stable certificates (item 4)

A conjugation-invariant `Q ⊆ X` with nonempty interior in `X` meets `R_p`
(Step 5, density), so `Q ⊇ R_p`, and `Q` meets no witness set.  A test that
reads `α` through finitely many elements to finite precision defines a set with
nonempty interior around each accepted action.  So its accepted set, if
nonempty, is such a `Q`.

## Step 8. The calibration set (item 5)

Let `ζ = e^(2πi/p)` and `λ_ζ(s_i) = ζ s_i`.  It has order `p`.  It multiplies
`s_μ s_ν*` by `ζ^(|μ|−|ν|)`, so it fixes `D_2` pointwise.  By
`cartan-respecting-o2-automorphisms-give-uct-crossed-products` (the gauge case
`u = ζ1` of the normalizer family), its crossed product satisfies the UCT.

By Kumjian--Pask (skew-product graphs, Ergodic Theory Dynam. Systems 19
(1999)), `O_2 ⋊_(λ_ζ) Z_p` is the graph algebra of the skew product
`E ×_c Z_p`.  Here `E` has one vertex and two loops, both labeled `1`.  Its
vertex matrix is `A = 2S`, with `S` the cyclic shift on `Z^p`.  So
`K_0 = coker(1 − A^t)` and `K_1 = ker(1 − A^t)`.  Now
`det(1 − 2S) = Π_(k<p) (1 − 2ζ^k) = 1 − 2^p ≠ 0`.  Also
`Z^p/(1 − 2S) ≅ Z[x]/(x^p − 1, 1 − 2x) ≅ Z[1/2]/(2^(−p) − 1) ≅ Z/(2^p − 1)`.
So `K_0 ≅ Z/(2^p − 1) ≠ 0` and `K_1 = 0`.

`λ_ζ` is not inner.  An inner order-`p` action `Ad(w)` can be rescaled to
`w^p = 1`, since `α(w) = w` and `w^p` is central, hence scalar.  It is then
exterior equivalent to the trivial action, with crossed product `O_2 ⊗ C^p`
and zero K-theory.  Since `p` is prime, `λ_ζ` is outer.

`λ_ζ` is not Rokhlin.  A Rokhlin action on `O_2` is KK^G-contractible (item 1
of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`), and Green--Julg descent
then makes the crossed product KK-contractible.  So `λ_ζ ∈ N_p`.  `N_p` is
invariant and disjoint from `R_p`, hence meager, and it meets no witness set
of item 3.  (`W^det_p` needs zero K-theory, and the others need a non-UCT
crossed product, no invariant Cartan, or failure of strong approximate
innerness while fixing a Cartan with a UCT crossed product.)  Membership of
`λ_ζ` in `S_p` is not needed and is not claimed.

## Step 9. Closure form (item 6)

Let `X = S_p ∩ Out_p`, and let `Φ ⊆ X` be conjugation invariant with `μ ∈ Φ`.
Then `Φ ⊇ R_p`, which is dense in `X` (Step 5).  If `Φ` is closed in `X`, then
`Φ = X`.  With `Φ = C_p`, this gives `D_p`.  Conversely `D_p` says `C_p = X`,
which is closed.  At `p = 2, 3` combine with
`barlak-li-uct-iff-z2-z3-actions-fix-cartan`.

**Where the naive limit argument fails.**  Let `α_n → α` in `X` with each
`α_n ∈ C_p`.  To show `α ∈ C_p`, one needs Cartan subalgebras `D_n` with
`α_n(D_n) = D_n` that converge in a sense forcing an `α`-invariant limit masa.
The hypothesis controls `α_n − α` only on a fixed finite set chosen before `n`.
The `D_n` (and, for `S_p`, the implementing unitaries `u_n ∈ O_2^(α_n)`) are
chosen after `n`, and nothing bounds `α(D_n)` against `α_n(D_n)`.  This
quantifier order is what fails.  It is also why `S_p` is only shown to be G_δ,
not closed.  A limit-closed certificate must carry data that can be fixed
before the approximation index, for instance compactness of the witnessing
objects in a topology coarser than norm.

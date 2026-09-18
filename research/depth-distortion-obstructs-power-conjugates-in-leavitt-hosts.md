---
rg: 2
id: depth-distortion-obstructs-power-conjugates-in-leavitt-hosts
kind: claim
title: In Leavitt tensor unit groups and Brin--Thompson nV, an element conjugate to a proper power has zero depth and support growth rates, and a Baumslag--Gersten generator has depth growth at most exponential in log* along towers
distinct_from:
  almost-automorphism-conjugate-to-proper-power-is-equicontinuous: that works with homeomorphisms of a rooted forest and an exponent cocycle; this works with linear operators on the Cantor module, including Leavitt units that are not homeomorphisms, over any field and in every tensor power, and adds the Baumslag--Gersten tower bound.
  leavitt-heisenberg-centers-have-infinite-centralizer-rank: that obstructs x ~ x^k in the binary Leavitt unit group through centralizer rank; this uses a different invariant, cylinder-depth and support-measure growth, valid in all tensor powers and all bounded-depth operator groups.
  baumslag-solitar-towers-have-no-faithful-linear-image: that is the finite-dimensional eigenvalue obstruction; this is its infinite-dimensional analogue for operators of bounded depth shift, where eigenvalues are unavailable.
  leavitt-units-of-infinite-order-have-linear-depth-growth: that conjectures positive algebraic depth rate for every infinite-order unit of L_(F_2)(1,2); this proves unconditional statements for all tensor powers and fields, and for the Baumslag--Gersten group needs only the much weaker pointwise iterated-log growth DG.
  thompson-elements-are-undistorted-in-leavitt-unit-group: that excludes power conjugates of V elements inside L_(F_2)(1,2)^x through germs; part 5 here recovers it for every field K and inside BDep_1(K) through cylinder depth.
artifacts:
  - research/depth-distortion-power-conjugates-leavitt-hosts-proof.md
  - experiments/leavitt-depth-rate-2026-09-17/depth_rate.py
  - experiments/leavitt-depth-rate-2026-09-17/results.txt
---

**ESTABLISHED** (proof: `depth-distortion-power-conjugates-leavitt-hosts-proof`).
This is an obstruction for a class of Boone--Higman host constructions. It does not settle the target.

## Setting

- `K` is any field, `X = {1,2}^N`, `d ≥ 1`. `C_d = C(X^d, K)` is the space of locally constant functions.
- `V_k ⊂ C_d` is the set of functions that depend only on the first `k` letters of each coordinate.
  - `depth(f)` is the least such `k`.
  - `μ` is the uniform Bernoulli measure.
- An invertible operator `T` has *depth shift* `s(T) = sup_{f≠0} (depth(Tf) − depth f)`.
- It has *support distortion* `m(T) = sup_{f≠0} μ(supp Tf)/μ(supp f)`.
- `BDep_d(K)` is the group of operators with `s(T), s(T^-1) < ∞`, and `BSD_d(K)` the group with
  `m(T), m(T^-1) < ∞`.
- Growth functions:
  - `E_T(n) = max(s(T^n), s(T^-n))`;
  - `ε(T) = lim E_T(n)/n`, the depth rate;
  - `ℓ(T) = lim max(log₂ m(T^n), log₂ m(T^-n))/n`, the support rate.

**Hosts.** For every field `K` and every `d ≥ 1`, the following groups act faithfully inside
`BDep_d(K) ∩ BSD_d(K)`:

- the unit group of `L_K(1,2)^{⊗d}` acting on `C_d`. This includes `U = L_{F_2}(1,2)^×` and the finitely
  presented simple group `(L_{F_2}(1,2) ⊗ L_{F_2}(1,2))^×` from `leavitt-square-unit-group-is-fp-simple-and-acyclic`;
- Brin--Thompson `dV`, acting by `f ↦ f∘v^-1`.

## Statement

1. **Invariance.** `ε` is a conjugacy invariant of `BDep_d(K)`, and `ℓ` is one of `BSD_d(K)`. Both satisfy
   `ε(T^k) = |k| ε(T)` and `ℓ(T^k) = |k| ℓ(T)` for `k ≠ 0`.
2. **Power conjugates.** Suppose `g T g^-1 = T^k` with `|k| ≥ 2` inside `BDep_d(K)`. Then `ε(T) = 0`, and
   quantitatively `E_T(|k|^m) ≤ E_T(1) + 2m·max(s(g), s(g^-1))`. The same holds for `ℓ` inside `BSD_d(K)`.
   In particular, for any `BS(1,k)` with `|k| ≥ 2` in these hosts, the generator `a` has zero depth rate and zero
   support rate.
3. **Baumslag--Gersten tower bound.** Let `BG = <a,t | b a b^-1 = a^2>` with `b = t a t^-1`, and let
   `ρ : BG → BDep_d(K)` be any homomorphism. Put `A = ρ(a)`, and let `N_0 = 1`, `N_{i+1} = 2^{N_i}`. Then
   `E_A(2^m) ≤ 2 E_A(m) + c`, so `E_A(N_i) ≤ C·2^i`, where `C` depends only on `ρ(a)` and `ρ(t)`.
   - Since `i = log* N_i`, depth growth along the tower is at most `exp(O(log* n))`.
   - The same bound holds for `log₂ m(A^{±n})` in `BSD_d(K)`.
   - **Killed class.** Suppose there are `α > 0` and `j ≥ 0` with `E_A(n) ≥ α·log^{(j)} n` for all large `n`.
     Then `ρ` cannot exist. Here `log^{(j)}` is the `j`-times iterated logarithm, and `j = 0` means linear growth.
     This covers positive rate, polylogarithmic growth, and every fixed iterated-log growth.
4. **Bounded depth over finite fields.** If `K` is finite and `sup_n E_T(n) < ∞`, then `T` is locally periodic:
   every `f` lies in a finite-dimensional `T`-invariant subspace, so its `T`-orbit is finite.
   - **BG triviality.** Let `ρ : BG → GL_K(W)` be any linear representation, over any field and on any vector
     space `W`, in which every vector has a finite `ρ(a)`-orbit. Then `ρ(a) = 1`.
   - Consequently, over a finite field, any `ρ : BG → BDep_d(K)` with `sup_n E_A(n) < ∞` kills `a`.
   - **Counting upgrade.** Let `K = F_q` and suppose some `f ∈ V_k` has an infinite `T`-orbit. Then for every
     `D ≥ 0`, `|{n ∈ Z : s(T^n) ≤ D}| ≤ q^(2^{dk}·2^{d(k+D)})`. So `s(T^n) → ∞` as `|n| → ∞`, and
     `max_{0≤m≤n} s(T^m) ≥ log₂(log_q(n+1))/d − 2k`.
   - **Profile window for BG.** Let `ρ : BG → BDep_d(F_q)` be faithful and `A = ρ(a)`. Then `A` is not locally
     periodic, so there is such an `f`, and
     - `E_A(n) → ∞`, with at most `q^(2^{d(2k+D)})` exponents `n` having `E_A(n) ≤ D`;
     - `c₁·log log n ≤ max_{|m|≤n} E_A(m) ≤ C₁·log n` for large `n`;
     - `E_A(N_i) ≤ C·2^i` along the tower (part 3).
5. **Calibration on V.**
   - For `v ∈ V`, `ε(v) > 0` exactly when `v` has infinite order.
   - Therefore an infinite-order element of `V` is not conjugate to a proper power inside `L_K(1,2)^×`, for any
     `K`, or inside `BDep_1(K)`. For `K = F_2` this was already on main through germs
     (`thompson-elements-are-undistorted-in-leavitt-unit-group`); the depth argument gives every field.
   - `BS(1,k)` and `BG` do not embed in `V`, which is already dead in the graph.
6. **Sharpness.** The invariants do not kill `BS(1,2)` itself.
   - Over `K = Q`, `BS(1,2) ⊂ GL_2(Q) ⊂ L_Q(1,2)^×` through matrix units, and there every power of `a` has depth
     shift at most 1.
   - The unit `[[x_1,1],[1,0]] ∈ GL_2(F_2[x_1]) ⊂ L_{F_2}(1,2)^×` has `ε = 1` but `ℓ = 0`. So the depth rate is
     strictly finer than the support rate.

## What this kills and what it leaves

It kills every construction that places the Baumslag--Gersten generator `a` in a Leavitt tensor unit group, or in
`dV`, on an element with any of these:

- an attracting or repelling cylinder: north--south units such as the Thompson unit `c` and `c⊗1`, and
  infinite-order elements of `V ⊂ dV`;
- polynomial-degree growth, such as non-torsion elements of `GL_n(F_2[x_1])` embedded through matrix units;
- depth growth at or above any fixed iterated logarithm;
- over a finite field, bounded depth growth (part 4).

**Surviving placements.** Over a finite field, the image `A` must have depth growth that tends to infinity
(with the counting bound of part 4), whose running maximum lies between `log log n` and `log n`, and which
nevertheless drops to `C·2^i = exp(O(log* n))` along the tower `N_i`. So `E_A` must be both divergent and
*irregular*.

**Conditional reduction.** Consider the following statement (**DG**). Every unit `A` of `L_{F_q}(1,2)^{⊗d}` with
unbounded `E_A` satisfies `E_A(n) ≥ α·log^{(j)} n` for all large `n`, for some `α > 0` and `j ≥ 0`.

- If DG holds, then `BG` embeds in no unit group of `L_{F_q}(1,2)^{⊗d}`.
- In particular, it would embed in none of the finitely presented simple Leavitt hosts in the graph.
- By part 4, DG is only needed for units with `E_A(n) → ∞`.
- DG is about operator depth shift `s`. The algebraic depth `ell` of
  `leavitt-units-of-infinite-order-have-linear-depth-growth` only satisfies `s(u) ≤ ell(u)`. So that conjecture,
  even if proved, does not formally give DG for `d = 1`. It excludes `BG` from `L_{F_2}(1,2)^×` by a different
  route, because `λ(a) = 0` for a `BS(1,2)` base.

**Where counting stops.** The pigeonhole of part 4 cannot prove DG. The exponents `n` with `|a^n|_BG ≤ ℓ` number
at most `4^ℓ`, and they all have `E_A(n) ≤ c·ℓ`. Part 4 allows `q^(2^{d(2k+cℓ)})` such exponents, which is doubly
exponential. So counting is consistent with every Baumslag--Gersten placement. A proof of DG must use more than the
dimension of the depth filtration: for example the Leavitt grading, or the Frobenius identity
`(A − 1)^(2^m) = B^m (A − 1) B^{-m}` that holds in characteristic 2.

**Next step.** Test DG. Either prove a depth-growth dichotomy for Leavitt tensor units, or find a unit whose depth
growth oscillates.

## Paradigm record

- **Why this can succeed where dead approaches failed.** The dead host arguments are dynamical: they use
  equicontinuity, germs, or derivatives at fixed points of homeomorphisms. None of them applies to Leavitt units,
  which are linear combinations of partial isometries. Cylinder depth and support measure are filtrations of the
  Cantor module that every Leavitt monomial shifts by a bounded amount. So they survive linear combination.
- **First falsifiable step.** Invariance and homogeneity of `ε`, checked by computing `ε` for `V` elements (the
  script `depth_rate.py`). It gives slope 1 for Thompson's `x_0` and 0 for an involution. It also checks that
  `[[x_1,1],[1,0]]` has `ε = 1` with bounded support ratio.
- **Calibration.** It recovers the known exclusion of `BS(1,k)` from `V`, and it correctly fails to exclude
  `BS(1,2) ⊂ GL_2(Q) ⊂ L_Q(1,2)^×`.

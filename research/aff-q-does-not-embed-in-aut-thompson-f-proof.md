---
rg: 2
id: aff-q-does-not-embed-in-aut-thompson-f-proof
kind: route
title: Direct proof from four cited Belk-Hyde-Matucci statements
target: aff-q-does-not-embed-in-aut-thompson-f
requires: []
artifacts:
  - research/artifacts/gq-gq-lit-q-embeddings.md
---

Direct proof from four cited statements. Quotations are from Belk–Hyde–Matucci,
*Embedding Q into a finitely presented group*, arXiv:2005.02036v4 (Bull. AMS 59 (2022)),
read on the ar5iv rendering on 2026-09-17. They are recorded in
`research/artifacts/gq-gq-lit-q-embeddings.md` §1.

**Inputs.**
- **(I1) Proposition 13.** "Every subgroup of T̄ isomorphic to ℚ contains the center of T̄."
- **(I2) Central extension.** T̄ is "a central extension of T by ℤ"; the kernel of
  `T̄ → T` (the induced map of `R/Z`) is `⟨z⟩`, `z(x) = x + 1`. Thompson's `T` is simple
  and nonabelian, so the centre of `T̄` is `⟨z⟩`.
- **(I3) Brin, quoted by BHM.** "Aut(F) has an index-two subgroup Aut₊(F) which is
  isomorphic to the group of all homeomorphisms of ℝ that satisfy conditions (1), (2), and
  (3) above and agree with elements of T̄ in neighborhoods of −∞ and ∞."
- **(I4) Higman, quoted by BHM.** "Higman proved that elements of Thompson's group V of
  infinite order do not have roots of arbitrarily large orders." And `F ≤ V`.

Write `A₊` for Brin's model of `Aut₊(F)` in (I3). Every element of `T̄`, of `A₊` and of
`PL₂(R)` is an increasing homeomorphism of `R`, since all slopes are powers of 2.

**Step 0 (increasing homeomorphisms).** Let `r` be an increasing homeomorphism of `R` and
`m ≥ 1`. If `r(x) > x`, then `r^m(x) > r^{m-1}(x) > ⋯ > x`, and similarly when `r(x) < x`.
So `{x : r^m(x) ≠ x} = {x : r(x) ≠ x}`. In particular `r^m = 1` forces `r = 1`, so all
three groups are torsion-free.

**Step 1 (item 1).** Let `N_1 × N_2 ≤ T̄` with `N_1 ≅ N_2 ≅ Q`. By (I1) and (I2),
`z ∈ N_1 ∩ N_2 = 1`, which contradicts `z ≠ 1`.
- `Q^n ⊇ Q × Q` for `n ≥ 2`.
- In `U_3(Q)`, the subgroups `X = {1 + a e_12}` and `C = {1 + b e_13}` commute, meet
  trivially and are both `≅ Q`, so `XC ≅ Q × Q`.

**Step 2 (item 2).** Suppose `h ∈ T̄` normalizes `N ≅ Q` and, for an isomorphism
`θ : Q → N`, satisfies `h θ(q) h^{-1} = θ(λ q)` with `λ ≠ 1`. By (I1) and (I2),
`z = θ(q_0)` for some `q_0 ≠ 0`. Since `z` is central, `z = h z h^{-1} = θ(λ q_0)`. So
`λ q_0 = q_0`, and `λ = 1`, a contradiction.

**Step 3 (germ homomorphisms).**
- **Definition.** For `g ∈ A₊` there is `t ∈ T̄` with `t = g` on some `[M, ∞)`.
- **Uniqueness.** Suppose `t, t' ∈ T̄` agree on `[M', ∞)`. Then `u = t^{-1} t'` is the
  identity on some `[M'', ∞)` and commutes with `z`. So for any `x`, choosing `k` with
  `x + k ≥ M''` gives `u(x) = z^{-k} u z^k (x) = x`. Hence `t = t'`, and we write
  `γ₊(g) = t`. Define `γ₋(g)` in the same way at `−∞`.
- **Homomorphism.** Let `g, h ∈ A₊`. For large `x`, both `h(x)` and `x` lie beyond the
  thresholds, so `gh(x) = γ₊(g) γ₊(h) (x)`. By uniqueness, `γ₊(gh) = γ₊(g) γ₊(h)`.
- **Kernel.** `K = ker γ₊ ∩ ker γ₋` consists of the elements of `A₊` that are the identity
  outside a compact set.

**Step 4 (`K` contains no copy of Q).** Let `N ≤ K` with `N ≅ Q`, and pick `1 ≠ g ∈ N`.
1. `g` is the identity outside `[−2^k, 2^k]` for some `k`.
2. For each `m ≥ 2`, `N` contains an `r` with `r^m = g`. By Step 0, `r` moves exactly the
   points `g` moves, so `r` is also the identity outside `[−2^k, 2^k]`.
3. The affine map `α(x) = (x + 2^k)/2^{k+1}` has slope `2^{-k-1}` and maps dyadic rationals
   bijectively to dyadic rationals. Conjugating by `α` carries the elements of `A₊`
   supported in `[−2^k, 2^k]` into the piecewise-linear homeomorphisms of `[0,1]` with
   finitely many dyadic breakpoints and power-of-2 slopes, which is Thompson's `F ≤ V`.
4. So `α g α^{-1}` is an element of `V` of infinite order (Step 0) with roots of every
   order `m`, which contradicts (I4).

**Step 5 (item 3).** Let `ι : H → Aut(F)` be injective, and let `H' = ι^{-1}(A₊)`, which
has index at most 2 in `H`.
1. **`N ≤ H'`.** The image of `N` in `H/H'` is a quotient of `Q` of order at most 2, hence
   trivial, since `Q = 2Q`.
2. **Invariant intersections.** Let `L' = L ∩ H'`, of index at most 2 in `L`. For each sign
   `σ ∈ {+, −}` put `M_σ = N ∩ ker(γ_σ ∘ ι)`. This is an `L'`-invariant subgroup of `N`,
   because `ker γ_σ` is normal in `A₊`, `ι(L') ≤ A₊`, and `L'` normalizes `N`. By
   hypothesis, `M_σ ∈ {1, N}`.
3. **One germ is injective.** If `M₊ = M₋ = N`, then `ι(N) ≤ K`, which contradicts Step 4.
   So `γ_σ ∘ ι` is injective on `N` for some `σ`.
4. **Contradiction.** By hypothesis some `l ∈ L'` acts on `N` by multiplication by
   `λ ≠ 1`. Then `γ_σ ι(l) ∈ T̄` normalizes `N̄ = γ_σ ι(N) ≅ Q` and acts on it by `λ`. This
   contradicts Step 2.

**Step 6 (item 4).** Every subgroup `L'` of index at most 2 in `Q^x` contains all squares.
1. **`Aff(Q)`.** Take `N` the translations and `L ≅ Q^x` the dilations, acting by
   multiplication.
   - Nontrivial action: `L'` contains the dilation by `4`, which acts nontrivially.
   - Invariant subgroups: suppose `1 ≠ M ≤ N` is `L'`-invariant and `q ∈ M` is nonzero.
     Then `M` contains the `Z`-span of `{c^2 q : c ∈ Q^x}`. Every rational `r` is a
     `Z`-combination of nonzero rational squares:
     - `r = 1^2` or `r = −1^2` when `r = ±1`;
     - `r = ((r+1)/2)^2 − ((r−1)/2)^2` otherwise;
     - `r = 0` trivially.

     So `M = N`.
2. **`SL_2(Q)`.** Take `N = {[[1,b],[0,1]]}` and `L = {diag(a, a^{-1})}`, acting by
   `b ↦ a^2 b`.
   - Nontrivial action: `L'` contains the squares `diag(a^2, a^{-2})`, which act by
     fourth powers. For example `diag(4, 1/4)` acts by `16`.
   - Invariant subgroups: `r = u/v` with `v ≥ 1` equals `u v^3 (1/v)^4`, so the `Z`-span of
     `{c^4 q}` is `Q q`. Every nonzero `L'`-invariant subgroup is again `N`.
3. **Larger groups.** `GL_2(Q) ⊇ SL_2(Q)`. For `n ≥ 2`, `SL_n(Q)` and `GL_n(Q)` contain
   `SL_2(Q)`, and `B_n(Q)` contains `{[[a,b],[0,1]]} ⊕ I_{n-2} ≅ Aff(Q)`.
4. **Hosts.** Item 3 therefore excludes `Aut(F)`, and `T̄ ≤ Aut₊(F)` (Brin, as quoted by
   BHM) excludes `T̄`. Item 2 also gives the `T̄` case directly. ∎

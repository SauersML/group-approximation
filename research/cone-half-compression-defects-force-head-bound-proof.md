---
rg: 2
id: cone-half-compression-defects-force-head-bound-proof
kind: route
title: Fix the vertex of an infinite Kazhdan subgroup on the Bass-Serre tree, transport the Kazhdan commutant through the exact compressor by a dimension count, and spread the defect to the head by simplicity
target: cone-half-compression-defects-force-head-bound
requires:
  - property-t-implies-property-fa
  - leavitt-cuntz-cone-halves-have-rf-amalgam-cover
  - leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding
artifacts:
  - research/kazhdan-cover-actor-models-normalize-proof.md
---

Notation is as in the claim. In `M_d`, `tr` is the normalized trace and `||x||_2 = tr(x^* x)^(1/2)`. For unitaries
`v, w`: `||v x w||_2 = ||x||_2`, `||v - 1||_2 = ||v^* - 1||_2`, and `||v w - 1||_2 <= ||v - 1||_2 + ||w - 1||_2`.

**Imported, verbatim.**
- `property-t-implies-property-fa`: "Every group with Kazhdan's property (T) has Serre's property FA: every action
  on a tree by automorphisms has a global fixed point." (Watatani, Math. Japon. 27 (1982) 97--103.)
- `leavitt-cuntz-cone-halves-have-rf-amalgam-cover`, Statement 2: "`Delta_0 = SL_20(F_2) x SL_20(F_2)`". Statement 3:
  "the inclusions induce a surjection `p : Gamma -> Delta`. Its kernel `K` is finitely normally generated."
  Statement 1: "The map `g -> (g^*)^(-1)` exchanges them" (the two halves).
- `leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding`, Setting: "`Delta = St_20(R) = GL_20(R)`, which is
  simple, infinite and finitely generated"; the definition of `(QC)`; and Theorem 1: "`Delta` is not hyperlinear
  **iff** `(QC)` and `(HR)` both hold."
- The Kazhdan inequality in the form proved in `kazhdan-cover-actor-models-normalize-proof`, Section 2. For a Kazhdan
  pair `(S, kappa)` of a group `L`, and every unitary representation `pi` of `L` on `H` with `Q` the projection onto
  the invariant vectors: "`||ξ - Qξ|| <= κ^-1 max_(s ∈ S) ||π(s)ξ - ξ||` for all `ξ ∈ H`."

## Step 1. Bass-Serre localization (Theorem 1)

1. `Gamma` acts without inversion on its Bass-Serre tree `T`.
   - The vertex stabilizers are the conjugates of `Delta_+` and `Delta_-`.
   - The edge stabilizers are the conjugates of `Delta_0`, which is finite by the import.
2. Let `L <= Gamma` be infinite with property (T). By property FA, `Fix(L)` is nonempty. It is a subtree: if `L`
   fixes vertices `a` and `b`, it fixes the unique geodesic between them pointwise.
3. `Fix(L)` contains no edge. Otherwise `L` would lie in an edge stabilizer, which is finite. So `Fix(L) = {v}` for a
   single vertex `v`.
4. Let `u ∈ Gamma` with `u L u^-1 <= L`.
   - `u L u^-1` is again infinite with (T), so `Fix(u L u^-1) = u·Fix(L) = {u v}`.
   - Every vertex fixed by `L` is fixed by the subgroup `u L u^-1`, so `v ∈ Fix(u L u^-1) = {u v}`.
   - Hence `u v = v`, and `L, u ≤ Stab(v) = g Delta_(±) g^-1`.  ∎

## Step 2. Hilbert-Schmidt transfer (Theorem 2)

Let `rho : Lambda -> U(d)`, `(L, u)` a compression pair, `(S, kappa)` a Kazhdan pair of `L`, `c ∈ Lambda`, `l ∈ L`.
Put `eta = max_(s ∈ S) ||rho([s, c]) - 1||_2`.

1. **The commutant is Ad-invariant.** Let `A = span_C rho(L)`. It is a unital `*`-subalgebra of `M_d`, because `L` is
   a group. Then `rho(u) A rho(u)^* = span rho(u L u^-1) ⊆ A`. The two spaces have the same finite dimension, so they
   are equal. Taking commutants gives `rho(u) A' rho(u)^* = A'`, where `A' = rho(L)'` is the commutant in `M_d`.
2. **Kazhdan approximation.** `pi(g) X = rho(g) X rho(g)^*` is a unitary representation of `L` on `M_d` with the inner
   product `tr(Y^* X)`. Its invariant vectors are exactly `A'`. For `s ∈ S`:

   ```text
   ||pi(s) rho(c) - rho(c)||_2 = ||rho(s c s^-1) - rho(c)||_2 = ||rho(s c s^-1 c^-1) - 1||_2 = ||rho([s, c]) - 1||_2 <= eta.
   ```

   By the Kazhdan inequality, `X = Q rho(c) ∈ A'` has `||rho(c) - X||_2 <= eta/kappa`.
3. **Transport.** Put `Y = rho(u) X rho(u)^*`. By Step 2.1, `Y ∈ A'`. With `W = rho(u c u^-1) = rho(u) rho(c) rho(u)^*`,
   we get `||W - Y||_2 = ||rho(c) - X||_2 <= eta/kappa`.
4. **Commute.** `Y` commutes with `rho(l)`. So

   ```text
   ||rho([u c u^-1, l]) - 1||_2 = ||(W rho(l) - rho(l) W) W^* rho(l)^*||_2 = ||W rho(l) - rho(l) W||_2
                               = ||(W - Y) rho(l) - rho(l)(W - Y)||_2 <= 2 eta/kappa.   ∎
   ```

No bound on `d` is used, nor any property of `Lambda` beyond the exact relation `u L u^-1 <= L` and (T) for `L`.

## Step 3. Head bound (Theorem 3)

1. `Delta_+` is a vertex group of `Gamma`, and `p` restricted to it is the inclusion `Delta_+ <= Delta`. So `(L, u)`
   is a compression pair in `Gamma`, and `L <= Gamma` is Kazhdan with the same pair `(S, kappa)`.
2. Choose `c ∈ Gamma` with `p(c) = c̄`, using surjectivity of `p`. For `s ∈ S`, `p([s, c]) = [s, c̄] = 1`, so
   `[s, c] ∈ K`. Fix expressions `[s, c] = prod_(a=1)^(m_s) y_a k_(i_a)^(±1) y_a^-1`, and put `m = max_s m_s`.
3. Put `ĝ = [u c u^-1, l] ∈ Gamma`. Then `p(ĝ) = [u c̄ u^-1, l] ≠ 1`. `Delta` is simple, so `z` lies in the normal
   closure of `p(ĝ)`: `z = prod_(j=1)^N h_j p(ĝ)^(ε_j) h_j^-1`. Lift each `h_j` to `ĥ_j ∈ Gamma`. Since `z ∈ Delta_0 <= Gamma`,

   ```text
   k_0 := z^-1 · prod_(j=1)^N ĥ_j ĝ^(ε_j) ĥ_j^-1  ∈ K,
   ```

   and we fix an expression of `k_0` as a product of `m_0` conjugates of the `k_i^(±1)`.
4. Let `rho` be a finite-dimensional unitary representation of `Gamma`, and `delta = max_i ||rho(k_i) - 1||_2`.
   - By the norm facts above, `||rho([s, c]) - 1||_2 <= m delta` and `||rho(k_0) - 1||_2 <= m_0 delta`.
   - By (HT), `||rho(ĝ) - 1||_2 <= 2 m delta / kappa`.
   - Hence

   ```text
   ||rho(z) - 1||_2 <= N ||rho(ĝ) - 1||_2 + ||rho(k_0) - 1||_2 <= (2 N m / kappa + m_0) · delta.
   ```

   This is `(QC)` with `eps = C delta`, `C = 2Nm/kappa + m_0`. The last sentence of Theorem 3 is the imported Theorem 1
   of `leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding`.  ∎

## Step 4. Theorem 4

- (=>) Let `(L, u)` be a lift in `Gamma` of `(L̄, ū)`, a compression pair with `L` Kazhdan. `L` is infinite because
  `L̄ = p(L)` is. By Step 1, `L, u ≤ g Delta_ε g^-1`. Then `h = p(g)^-1` conjugates `L̄` and `ū` into `Delta_ε`,
  and the compression relation persists under the homomorphism `p`.
- (<=) Suppose `h L̄ h^-1` and `h ū h^-1` lie in `Delta_ε` and form a compression pair there. Let `ĥ ∈ Gamma` lift `h`.
  Pull `(h L̄ h^-1, h ū h^-1)` back to the vertex group `Delta_ε <= Gamma` and conjugate it by `ĥ^-1`. This gives a
  compression pair in `Gamma` mapping onto `(L̄, ū)`. `p` is injective on `ĥ^-1 Delta_ε ĥ`, so the lifted group is
  isomorphic to `L̄`, hence Kazhdan.
- The mirror automorphism exchanges `Delta_+` with `Delta_-` and preserves compression pairs, (T) and nontriviality of
  defects.  ∎

## Scope

- (HT) is the finite-dimensional, quantitative companion of Theorem 3 in
  `kazhdan-cover-actor-models-normalize-vertex-commutants`, and it is proved by the same two moves.
- What is new here:
  - the explicit inequality;
  - the localization (Step 1), which says that in this cover the compressed Kazhdan lift required there exists only
    inside one Cuntz half;
  - the reduction of `(QC)` to `(HEC)`.
- Nothing here decides `(HEC)`.

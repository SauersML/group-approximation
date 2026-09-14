# sk-cstar-genericity part 1: pigeonhole commutators, the exponent of B_4, and infinite-order elements in confined subgroups with Laurent-linear confining sets (2026-09-14)

Lane sk-cstar-genericity. Context: the idempotent route to C*-simplicity of `G_X = EL_3(LC(X,F_2) ⋊_T Z)` still lacks (L3), the exclusion of confined subgroups `K ⊆ B_4 ∪ {1}` (plan artifact `sk-cstar-genericity-plan-2026-09-14.md`). This part proves three statements. The third settles the special case (L3) raises for the constant units Lemma B flagged.

Convention: `H ≤ Γ` is *confined* by a finite `P ⊆ Γ ∖ {1}` if `gHg^{-1} ∩ P ≠ ∅` for every `g ∈ Γ`. We write `[a,b] = aba^{-1}b^{-1}`.

## 1. Lemma R: pigeonhole commutators (any group)

**Lemma R.**
- **Statement.** Let `H ≤ Γ` be confined by `P`, `|P| = r`, and let `g_1, …, g_{r+1} ∈ Γ`. Then there are `p ∈ P` and `i ≠ j` with `g_i^{-1}[p, g_ig_j^{-1}]g_i ∈ H`.
- **Proof.**
  - For each `i`, confinement at `g_i` gives `p_i ∈ P ∩ g_iHg_i^{-1}`, so `h_i = g_i^{-1}p_ig_i ∈ H`.
  - Two of the `r+1` indices share a value `p_i = p_j = p`.
  - Put `k = g_ig_j^{-1}`. Then `g_j = k^{-1}g_i`, so `h_j^{-1} = g_j^{-1}p^{-1}g_j = g_i^{-1}kp^{-1}k^{-1}g_i`.
  - So `h_ih_j^{-1} = g_i^{-1}(p·kp^{-1}k^{-1})g_i = g_i^{-1}[p,k]g_i ∈ H`. ∎

**Corollary R′.** Suppose that for every finite `P ⊆ Γ ∖ {1}` and every `n` there are `g_1, …, g_n ∈ Γ` with `[p, g_ig_j^{-1}]` of infinite order for all `p ∈ P` and all `i ≠ j`. Then every confined subgroup of `Γ` contains an element of infinite order. ∎

**Corollary R″ (bounded exponent).** If `e ≥ 1`, and for every finite `P ⊆ Γ∖{1}` there are `g_1, …, g_{r+1}` with `[p, g_ig_j^{-1}]^e ≠ 1` for all `p ∈ P`, `i ≠ j`, then no nontrivial subgroup of `Γ` of exponent dividing `e` is confined. ∎

## 2. Units in B_4 have order dividing 420 (any unital F_2-algebra)

**Lemma X.**
- **Statement.** Let `M` be a unital `F_2`-algebra and `σ ∈ M^×` with `1 ∈ span_{F_2}(σ, σ^{-1}, σ^2, σ^{-2})`. Then `σ^{420} = 1`.
- **Proof.**
  - Write `1 = c_1σ + c_{-1}σ^{-1} + c_2σ^2 + c_{-2}σ^{-2}` and multiply by `σ^2`. So `σ` is a root of `Q(t) = c_2t^4 + c_1t^3 + t^2 + c_{-1}t + c_{-2}`, which is nonzero because its `t^2` coefficient is `1`.
  - So `A = F_2[σ]` is a commutative `F_2`-algebra of dimension at most 4, a finite product of finite local algebras `A_i` with residue fields `F_{2^{f_i}}`, `Σ dim A_i ≤ 4`.
  - The unit group of `A_i` is an extension of `F_{2^{f_i}}^×` (order `2^{f_i}−1 ∈ {1,3,7,15}`) by `1 + 𝔪_i`. Since `𝔪_i^4 = 0`, `(1+x)^4 = 1 + x^4 = 1` for `x ∈ 𝔪_i`, so `1 + 𝔪_i` has exponent dividing 4.
  - So the exponent of `A^×` divides `4·lcm(3,7,15) = 420`. ∎

**Consequence for (L3).** Every `K ⊆ B_4 ∪ {1}` that is a group has exponent dividing 420. By Corollary R″, (L3) follows once, for every finite `P ⊆ G_X∖{1}`, there are conjugators `g_1..g_{r+1}` with `[p, g_ig_j^{-1}]^{420} ≠ 1`.

## 3. Theorem L: Laurent-linear confining sets force infinite-order elements

Let `A = F_2[u^{±1}]` and `Λ = SL_3(A)`. We have `Λ = EL_3(A)`, since `A` is a localization of the Euclidean domain `F_2[u]`. So `Λ ≤ EL_3(S)` for every ring `S ⊇ A`; in particular `Λ ≤ G_X` for every `X`, since `u ∈ LC(X,F_2)⋊Z`.

**Theorem L.**
- **Statement.** Let `Γ` be a group containing `Λ`, and let `H ≤ Γ` be confined by a finite `P ⊆ Λ ∖ {1}`. Then `H` contains a `Γ`-conjugate of an element of `Λ` of infinite order.
- **Corollary L′.** No nontrivial torsion subgroup of `G_X` is confined by a subset of `EL_3(F_2)∖{1}`, or of `Λ∖{1}`. This covers the constant units Lemma B excludes from configurations: all involutions of `EL_3(F_2)`, `I+E_12+E_23`, the Singer cycles.

**Proof of Theorem L.**
1. **The loxodromic element and the invariant `Φ_p`.**
   - Let `d = diag(u,1,u^{-1}) ∈ Λ`, with exponents `(d_1,d_2,d_3) = (1,0,−1)`.
   - Let `K` be an algebraic closure of `F_2(u)`. For `p ∈ SL_3(K)` and `h ∈ SL_3(K)` put `p′ = h^{-1}ph`, `q′ = h^{-1}p^{-1}h`, and `Φ_p(h) = p′_{31}·q′_{13}`.
   - `Φ_p` is a regular function on the irreducible variety `SL_3`, since `h^{-1}` is polynomial in `h` when `det h = 1`.
2. **`Φ_p ≢ 0` for `p ≠ 1`.**
   - Over `F_2(u)`, the only scalar in `SL_3` is `1`, because `F_4 ⊄ F_2(u)`. So `p ≠ 1` is not scalar, and there is `v ∈ F_2(u)^3` with `pv ∉ F_2(u)v`.
   - Complete `v, pv` by a vector `w` to a basis, and let `h` have columns `(v, λw, pv)` with `λ` chosen so that `det h = 1`.
   - Then `p′e_1 = h^{-1}pv = e_3`, so `p′_{31} = 1`, and `q′e_3 = h^{-1}p^{-1}pv = e_1`, so `q′_{13} = 1`. So `Φ_p(h) = 1`.
3. **A generic conjugating element in `Λ`.**
   - `Z = ⋃_{p∈P} {Φ_p = 0}` is a finite union of proper closed subsets of the irreducible `SL_3`, hence proper.
   - `Λ ⊇ SL_3(F_2[u])` contains the root groups `e_ij(F_2[u])`. `F_2[u]` is infinite, so each root group is Zariski dense in `U_ij(K)`, and the Zariski closure of `Λ`, a closed subgroup containing all `U_ij`, is `SL_3`.
   - So some `h ∈ Λ ∖ Z` exists. Fix it, and put `k = hdh^{-1} ∈ Λ`.
4. **The trace at scale `m`.**
   - Let `D` bound the absolute `u`-degrees of all entries of `p′, q′`, `p ∈ P`; these now lie in `A`.
   - For `m ∈ Z`, `[p,k^m] = h[p′,d^m]h^{-1}`, and since `A` is commutative,
     `tr[p′,d^m] = Σ_{i,l} p′_{il}q′_{li} u^{m(d_l−d_i)}`.
   - The terms with `d_l − d_i = δ` have degrees in `[δm−2D, δm+2D]`. For `|m| > 4D` these ranges are disjoint for distinct `δ ∈ {−2,…,2}`.
   - The class `δ = 2` is the single term `p′_{31}q′_{13}u^{2m} = Φ_p(h)u^{2m}`, which is nonzero. So the trace is a non-constant Laurent polynomial.
5. **Finite order is impossible.**
   - If `c ∈ SL_3(A)` has finite order, its eigenvalues in `K` are roots of unity, hence algebraic over `F_2`. So `tr c ∈ F_2(u)` is algebraic over `F_2`, which forces `tr c ∈ F_2`.
   - So `[p,k^m]` has infinite order for every `p ∈ P` and `|m| > 4D`.
6. **Pigeonhole.**
   - Choose `N_1 < … < N_{r+1}` with gaps `> 4D` and put `g_i = k^{N_i}`, so `g_ig_j^{-1} = k^{N_i−N_j}` with `|N_i − N_j| > 4D`.
   - Lemma R gives `g_i^{-1}[p,k^{N_i−N_j}]g_i ∈ H` for some `p ∈ P` and `i ≠ j`, and this element has infinite order. ∎

**Model tests.**
- `p = e_12(1)`: `v = e_2`, `pv = e_1 + e_2`, `h = (e_2, e_3, e_1+e_2)` up to sign. Then `p′_{31} = 1` and `q′_{13} = 1`.
- For comparison, the untwisted `[e_12(1), d^m] = e_12(1+u^m)` has order 2, so the generic twist `h` is necessary.
- `p` diagonal with `p = diag(u,u^{-1},1) ∈ Λ`: `Φ_p(h) ≠ 0` for generic `h`, while `[p,d^m] = 1`. Again the twist matters.

## 4. Where the general case stands (recorded as Attempt 9 on the open node)
- **Why the trace argument stops at `Λ`.** Theorem L uses commutativity of the coefficients, for the trace formula and for "finite order ⇒ constant trace". For `p ∈ G_X` with non-constant coefficients, `u` does not commute with `LC(X,F_2)`, and `M_3(R)` has no trace detecting torsion.
- **Degree criterion (valid, but insufficient).** If `c ∈ GL_3(R)` has top `u`-degree `a > 0` with top coefficient `A ∈ M_3(LC(X,F_2))`, and the cocycle products `A·(A∘T^{-a})···(A∘T^{-(n−1)a})` are nonzero for all `n` (or for `n ≤ 420`, which suffices for (L3)), then `c^n ≠ 1`.
- **Why it can fail.** For commutators of locally constant `p` with shears or diagonal elements, the top coefficient involves products of different coefficient functions of `p` and `p^{-1}` along an arithmetic progression of translates. For Sturmian `X`, two arcs at offset about `1/2` show that alternating-support products can vanish for every progression step. So a proof of (L3) for general `P` needs either conjugators adapted to the coefficient supports, or a torsion invariant finer than degree.
- **The shear commutator is dihedral.** In characteristic 2, `[p, e_ij(s)] = (1 + pXp^{-1})(1 + X)` with `X = sE_ij`, a product of two involutions. For commutative coefficients its trace is `3 + s²p_{ji}q_{ji}`, which is `1 + s²p_{ji}q_{ji}` in characteristic 2 — the same mechanism as Theorem L.

## 5. Status
- ESTABLISHED (unreviewed): `confined-subgroup-pigeonhole-commutator-lemma` (Lemma R, R′, R″); `polynomially-small-units-have-order-dividing-420` (Lemma X); `laurent-linear-confining-sets-force-infinite-order-elements` (Theorem L, L′).
- OPEN: (L3) for general `P ⊆ G_X∖{1}`; (L4); C*-simplicity of `G_X`.
- Recalled, not re-read at source: `SL_n = E_n` over localizations of Euclidean domains; Zariski density of `SL_3(F_2[u])` in `SL_3`, by the root-group argument given above.

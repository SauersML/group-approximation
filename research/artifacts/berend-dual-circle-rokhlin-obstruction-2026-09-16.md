---
title: Dual circle actions on the Berend group algebra have infinite Rokhlin dimension
date: 2026-09-16
---

## Scope

This artifact kills one natural route to STW LXXXVI in the Berend case
(`stw99-lxxxvi-berend-groups-decomposition-rank`). The route would take a
closed one-dimensional subgroup `S` of the dual torus of `Z^2` with finite
Rokhlin dimension (commuting towers) and then apply the
Gardella--Hirshberg--Santiago decomposition-rank bound for crossed
products. Here we prove that **every** infinite closed subgroup `S`, and
every finite `S` whose order is divisible by `2` or `3`, acts with
infinite Rokhlin dimension, on `A` and on each nonzero invariant ideal.

The artifact does **not** prove or disprove `dr(C*(G)) = ∞`. Lemmas 1 and 2
are elementary. They are in the spirit of the standard principle that finite
Rokhlin dimension excludes inner, or fixed-point-like, behaviour. No novelty
is claimed for them, and no specific statement of Gardella's arXiv:1407.1277
is used. Lemma 4 is a rank-two local Leopoldt-type injectivity. For
`p = 2, 3` it is certified here by exact computation rather than cited.

## Setup

- **The ring.** Let `a` be a root of `f(t) = t^3 + t^2 - 2t - 1` and let
  `L = Z[a]`. This is the ring of integers of the totally real cyclic cubic
  field `Q(a)`; `disc f = 49`. Use the basis `1, a, a^2`, so
  `a^3 = -a^2 + 2a + 1`. Multiplication by `a` has matrix
  `M_a = ((0,0,1),(1,0,2),(0,1,-1))`, whose columns are `a·1`, `a·a` and
  `a·a^2`.
- **The unit group.** Let `Γ ≤ L^×` be any subgroup with `Γ ≅ Z^2`.
  Eckhardt's `Σ = <a, b>`, with `b` multiplicatively independent of `a`, is
  one such group.
- **The algebra.** Put `G = L ⋊ Γ` and `X = dual(L) ≅ T^3`. Then
  `A = C*(G) = C(X) ⋊ Γ`, and `γ` acts on characters by
  `(γ·χ)(w) = χ(γ^{-1} w)`. Stabilizers do not depend on the choice between
  `γ` and `γ^{-1}`.
- **The dual action.** `\hat α` of `\hat Γ ≅ T^2` on `A` is defined by
  `\hat α_χ(f u_γ) = χ(γ) f u_γ`. For a closed subgroup `S ≤ \hat Γ`, put
  `S^⊥ = {γ : χ(γ) = 1 for all χ ∈ S}`. By Pontryagin duality
  `S = (S^⊥)^⊥` and `\hat S ≅ Γ/S^⊥`.
- **Remark.** If `a ∈ Γ`, then `a - 1` is a unit, because `f(1) = -1`. Hence
  `[G,G] ⊇ (a-1)L = L` and `G^ab = Γ`. So `\hat α` is then the canonical
  action of the character group of `G` on `C*(G)`.

**Rokhlin dimension.** We use Gardella--Hirshberg--Santiago
(arXiv:1709.00222, Definition 1.3, text read on ar5iv 2026-09-16; the referee
re-read Definition 1.3, Remark 1.4 and Theorem 3.17 in the arXiv v2 LaTeX
source on 2026-09-16). Let `K` be a compact group acting by `α` on a
C*-algebra `B`.

- For a σ-unital invariant `D`, put `F(D,B) = (B_∞ ∩ D')/Ann(D, B_∞)`, and
  let `F_α(D,B)` be its continuous part under the induced action `F(α)`.
- `dim_Rok(α) ≤ d` means: for every such `D` there are equivariant
  completely positive contractive order-zero maps
  `φ_0, ..., φ_d : (C(K), Lt) → (F_α(D,B), F(α))` with `Σ_j φ_j(1) = 1`.
- `dim^c_Rok` additionally asks that the ranges commute. By their Remark 1.4,
  `dim_Rok ≤ dim^c_Rok`.

**Established inputs.** Both are already used in
`berend-proper-quotient-decomposition-rank-proof`. After the referee's
Lemma 3′ below, only (E2) is used in the Proposition.

- **(E1) Berend.** For Eckhardt's `Σ`, every proper closed invariant subset of
  `X` is finite. This is Eckhardt, arXiv:1309.2205, Lemma 2.2, from Berend,
  Trans. AMS 280 (1983). See `berend-torus-actions-give-strongly-qd-polycyclic-groups`.
- **(E2) Ideal intersection.** The action is topologically free, so every
  nonzero ideal `I ⊆ A` satisfies `I ∩ C(X) ≠ 0`. Indeed, for `γ ≠ 1` the
  fixed characters are those trivial on `(γ-1)L`, a subgroup of finite index
  `|N(γ-1)|`; so they form a finite set. Then use Archbold--Spielberg (BPP1).

## Lemma 1 (fixed central sequences on a unital quotient)

**Statement.** Let `K` be a compact group, `I` a σ-unital C*-algebra (for
example separable, or unital) with a
continuous action `α`, and `B` a nonzero unital C*-algebra with an action `β`
of `K`. Let `π : I → B` be a surjective equivariant *-homomorphism. Suppose
some `s ∈ K \ {e}` satisfies `β_{∞,s}(x) = x` for every `x ∈ B_∞ ∩ B'`. Then
`dim_Rok(α) = dim^c_Rok(α) = ∞`.

*Proof.* Suppose `dim_Rok(α) ≤ d < ∞`. Apply Definition 1.3 with `D = I`,
which is σ-unital and invariant. This gives maps `φ_0, ..., φ_d`
as above.

**Step 0: a unital equivariant comparison map.**

1. *The componentwise map lands in the commutant.* Let
   `π_∞ : I_∞ → B_∞` be componentwise. If `x ∈ I_∞ ∩ I'` and `d ∈ I`, then
   `[π_∞(x), π(d)] = π_∞([x,d]) = 0`. Since `π(I) = B`, this gives
   `π_∞(x) ∈ B_∞ ∩ B'`.
2. *The annihilator is killed.* Choose `d_0 ∈ I` with `π(d_0) = 1_B`. If
   `x ∈ Ann(I, I_∞)`, then `π_∞(x) = π_∞(x)π(d_0) = π_∞(x d_0) = 0`.
3. *The induced map.* Hence `π_∞` induces a *-homomorphism
   `\bar π : F(I,I) → B_∞ ∩ B'`. It is equivariant, because
   `π_∞ ∘ α_{∞,g} = β_{∞,g} ∘ π_∞`.
4. *The unit of `F(I,I)`.* Let `(e_n)` be a sequential approximate unit of
   `I` and `e = [(e_n)]`. Then `e ∈ I_∞ ∩ I'` and `ed = de = d` for `d ∈ I`.
   For `x ∈ I_∞ ∩ I'` and `d ∈ I` we get
   `(ex - x)d = e d x - x d = dx - xd = 0`, and similarly `d(ex - x) = 0`.
   So `κ(e)` is the unit of `F(I,I)`.
5. *`\bar π` is unital.* Since `e d_0 = d_0`, we have
   `\bar π(κ(e)) = π_∞(e) = π_∞(e)·1_B = π_∞(e d_0) = π(d_0) = 1_B`.

**Step 1: pushing the towers forward.** Put `ψ_j = \bar π ∘ φ_j`. Each
`ψ_j : C(K) → B_∞ ∩ B'` is equivariant, completely positive contractive and
order zero. Moreover `Σ_j ψ_j(1) = 1_B`.

**Step 2: a partition of unity moved off itself by `s`.** Since `s ≠ e`,
every `g ∈ K` satisfies `sg ≠ g`. Compact Hausdorff spaces are regular, so
there is an open `W_g ∋ g` with `\bar W_g ∩ s\bar W_g = ∅`. Take a finite
subcover `W_1, ..., W_k` and a partition of unity `f_1, ..., f_k` with
`supp f_i ⊆ W_i`. Since `(Lt_s f)(h) = f(s^{-1}h)`, the support of
`Lt_s f_i` lies in `s\bar W_i`. Hence `f_i · Lt_s f_i = 0`.

**Step 3: the contradiction.**

- By equivariance, and because `ψ_j(f_i) ∈ B_∞ ∩ B'` is fixed by `β_{∞,s}`,
  we get `ψ_j(Lt_s f_i) = β_{∞,s}(ψ_j(f_i)) = ψ_j(f_i)`.
- The functions `f_i` and `Lt_s f_i` are positive and orthogonal, so order
  zero gives `ψ_j(f_i)^2 = ψ_j(f_i)ψ_j(Lt_s f_i) = 0`. A positive element
  with zero square is zero, so `ψ_j(f_i) = 0`.
- Summing over `i` gives `ψ_j(1) = 0`. Summing over `j` gives `1_B = 0`,
  which contradicts `B ≠ 0`.

Therefore `dim_Rok(α) = ∞`, and `dim^c_Rok(α) = ∞` by Remark 1.4. ∎

## Lemma 2 (the stabilizer annihilator acts innerly on a finite-orbit quotient)

**Statement.** Let `Y ⊆ X` be a finite `Γ`-orbit with stabilizer `Λ`. The
stabilizer is the same at every point of `Y`, because `Γ` is abelian. Put
`B_Y = C(Y) ⋊ Γ`, with the dual action `\hat β` of `\hat Γ`. For every
`χ ∈ Λ^⊥` there is a unitary `c_χ ∈ C(Y) ⊆ B_Y` with `\hat β_χ = Ad(c_χ)`.
Consequently `\hat β_{∞,χ}` fixes `(B_Y)_∞ ∩ B_Y'` pointwise. The same holds
for `B_Y ⊗ D`, where `D` is unital and the action is `\hat β ⊗ id`, with
`c_χ ⊗ 1` in place of `c_χ`.

*Proof.*

1. *Definition of `c_χ`.* Fix `y_0 ∈ Y` and set `c_χ(γ y_0) = χ(γ)`. This is
   well defined: if `γ y_0 = γ' y_0`, then `γ^{-1}γ' ∈ Λ`, so
   `χ(γ) = χ(γ')`.
2. *Agreement on `C(Y)`.* Both `\hat β_χ` and `Ad(c_χ)` fix `C(Y)`, since
   `C(Y)` is commutative.
3. *Agreement on the unitaries.* With `u_γ g u_γ^* = α_γ(g)` and
   `α_γ(g)(y) = g(γ^{-1}y)`, we have
   `Ad(c_χ)(u_γ) = c_χ α_γ(\bar c_χ) u_γ`. At the point `γ' y_0` the
   coefficient is `χ(γ') \bar χ(γ^{-1}γ') = χ(γ)`. So
   `Ad(c_χ)(u_γ) = χ(γ) u_γ = \hat β_χ(u_γ)`.
4. *Conclusion.* The two automorphisms agree on generators, so they are equal.
   On `(B_Y)_∞`, `\hat β_{∞,χ} = Ad(c_χ)` with `c_χ ∈ B_Y`, and this fixes
   every element that commutes with `B_Y`. The tensor case is identical. ∎

## Lemma 3 (explicit torsion points and their stabilizers)

For `N ≥ 2` define `ξ_N ∈ X` by `ξ_N(w) = exp(2πi w_2/N)`, where
`w = w_0 + w_1 a + w_2 a^2`. Then:

- (i) `ξ_N` has order exactly `N`;
- (ii) `Stab_Γ(ξ_N) = Γ ∩ (1 + NL)`;
- (iii) the orbits `Γ·ξ_N` are finite, and are pairwise disjoint for distinct
  `N`.

*Proof.*

- **(i)** `ξ_N^k = 1` iff `N | k w_2` for all `w`, iff `N | k`.
- **(ii)**
  1. `γ` fixes `ξ_N` iff `ξ_N((γ^{-1} - 1)w) = 1` for all `w ∈ L`.
  2. Put `x = γ^{-1} - 1 = x_0 + x_1 a + x_2 a^2`. The `a^2`-coordinates of
     `x`, `ax` and `a^2 x` are `x_2`, `x_1 - x_2` and `x_0 - x_1 + 3x_2`. For
     example `ax = x_2 + (x_0 + 2x_2)a + (x_1 - x_2)a^2`.
  3. This system is unitriangular, so the condition holds iff `x ∈ NL`.
  4. Now `L^× ∩ (1 + NL)` is the kernel of `L^× → (L/NL)^×`, hence a group.
     So `γ^{-1} ∈ 1 + NL` iff `γ ∈ 1 + NL`.
- **(iii)** The action is by group automorphisms, so it preserves orders.
  Moreover `X[N] ≅ (Z/N)^3` is finite. ∎

**Lemma 3′ (every point of exact order `p^j`; added by the referee).** Let
`p ∈ {2,3}` and `j ≥ 1`. If `χ ∈ X` has exact order `p^j`, then
`Stab_Γ(χ) = Γ ∩ (1 + p^j L)`.

*Proof.* As in (ii), `γ` fixes `χ` iff the ideal `J = (γ^{-1} - 1)L` lies in
`ker χ`. Since `χ^{p^j} = 1`, `p^j L ⊆ ker χ`, so `J ⊆ ker χ` iff
`J + p^j L ⊆ ker χ`. The ideal `J + p^j L` contains `p^j L`, and the ideals of
`L/p^j L ≅ L_p/p^j L_p` are the `p^i L_p/p^j L_p`, `0 ≤ i ≤ j`, because `p` is
inert (Lemma 4(a)). So `J + p^j L = p^i L` for some `i ≤ j`. If `i ≤ j - 1`
then `p^{j-1} L ⊆ ker χ`, i.e. `χ^{p^{j-1}} = 1`, contradicting exactness of
the order. Hence `γ` fixes `χ` iff `J ⊆ p^j L`, iff `γ^{-1} ∈ 1 + p^j L`, iff
`γ ∈ 1 + p^j L`. ∎

Points of exact order `p^j` are `2p^{-j}`-dense in `X ≅ T^3` (take coordinates
in `p^{-j}Z/Z` with at least one numerator prime to `p`), so every nonempty
open subset of `X` contains such a point once `j` is large.

In the integer-matrix picture `ξ_N` is `v = (0,0,1)` modulo `N`, and `γ` fixes
it iff `M_γ^T v ≡ v mod N`. The scripts in
`experiments/stw99-lxxxvi-berend-dual-circle-rokhlin-2026-09-16/` compute
both sides exactly and find agreement:

- `padic_certificate.py` compares the ring-side and matrix-side stabilizers,
  for `j ≤ 5` when `p = 2` and `j ≤ 2` when `p = 3`.
- `stabilizers.py` finds the first torsion points, ordered by `N`, whose
  stabilizer lies in `p Z^2`, for `Γ_± = <a, ±(a+1)>`.

| sign | `p` | `N` | HNF basis of `Stab(v)` | orbit size |
|---|---|---|---|---|
| both | 2 | 4 | `(2,8), (0,14)` | 28 |
| `b = a+1` | 3 | 9 | `(3,48), (0,78)` | 234 |
| `b = -(a+1)` | 3 | 9 | `(3,9), (0,39)` | 117 |

`certificate.py` prints a hand-checkable certificate for each case:
`(M^T)^L ≡ I mod N`, together with the images of `v` under the powers
`(L/p)·ε`, `ε ∈ {0,...,p-1}^2 \ {0}`, all different from `v`. The values of
`L` are `14, 14, 78, 39`.

## Lemma 4 (stabilizers eventually lie in `Γ^p`, for `p = 2, 3`)

Let `p ∈ {2,3}`, and put `m = 2` if `p = 2` and `m = 1` if `p = 3`. For every
subgroup `Γ ≤ L^×` with `Γ ≅ Z^2` there is `j_0` such that
`Γ ∩ (1 + p^j L) ⊆ Γ^p := {γ^p : γ ∈ Γ}` for all `j ≥ j_0`.

*Proof.*

**(a) `p` is inert.**

- `f` has no root mod `2`: `f(0) ≡ f(1) ≡ 1`.
- `f` has no root mod `3`: `f(0) ≡ f(1) ≡ 2` and `f(2) = 7 ≡ 1`.
- A cubic with no root over `F_p` is irreducible. So `p` is inert, and
  `L_p = L ⊗ Z_p = Z_p[t]/(f)` is the ring of integers of the unramified cubic
  extension of `Q_p`.
- `L_p` is a DVR with uniformizer `p`. Let `v` be its valuation, with
  `v(p) = 1`.

**(b) The logarithm.** The map
`log(1+y) = Σ_{n ≥ 1} (-1)^{n+1} y^n/n` is an isomorphism
`1 + p^m L_p → p^m L_p`, with inverse `exp`. It preserves valuations:
`v(y^n/n) = n v(y) - v_p(n) > v(y)` for `n ≥ 2` and `v(y) ≥ m`, since
`(n-1)m > v_p(n)` in both cases. Hence for every `j ≥ m` it restricts to a
bijection `1 + p^j L_p → p^j L_p`.

**(c) The subgroup `E`.** Put `E = L^× ∩ (1 + p^m L)`.

- `E` has finite index in `L^×`.
- `E` is torsion-free. The torsion of `L^×` is `{±1}`, and `-1 ∉ 1 + p^m L`
  because `2 ∉ 4L` and `2 ∉ 3L`.
- By Dirichlet, `L^× ≅ {±1} × Z^2`, so `E ≅ Z^2`.

**(d) Certificate** (`padic_certificate.py`, precision `p^40`, exit 0). Put
`ε_1 = a^e` and `ε_2 = (a+1)^e`, with `e = 14` for `p = 2` and `e = 26` for
`p = 3`. Both lie in `1 + p^m L`. The coordinates of `log ε_i` modulo `p^40`,
in the basis `1, a, a^2`, are:

- **`p = 2`.**
  - `log ε_1 = (825550089956, 417712771088, 687724128020)`.
  - `log ε_2 = (145726323712, 687724128020, 270011356932)`.
  - The three `2×2` minors all have 2-adic valuation `4`.
- **`p = 3`.**
  - `log ε_1 = (8549362065164825496, 4242931307523858858, 7876634481462805275)`.
  - `log ε_2 = (621928023608333997, 7876634481462805275, 3633703173938946417)`.
  - The minors have 3-adic valuations `2, 2, 3`.

A minor of valuation `< 40` is nonzero in `Z_p`, so `log ε_1` and `log ε_2`
are `Z_p`-linearly independent. The series computation is cross-checked two
ways, and both checks agree modulo `p^40`:

- by additivity, `log(ε_1 ε_2) = log ε_1 + log ε_2`;
- by the independent formula `log ε ≡ (ε^{p^K} - 1)/p^K mod p^K`. This holds
  because `ε^{p^K} - 1 ∈ p^{K+m} L_p` and the higher series terms are
  divisible by `p^{2K}`.

**(e) `log` is injective on `Z_p ⊗ E`.** Nonvanishing of the minor also shows
that `a` and `a+1` are multiplicatively independent. Hence
`Φ = <ε_1, ε_2>` has finite index `n` in `E`. Extend `log` `Z_p`-linearly to
`Z_p ⊗ E → L_p`.

- Suppose `ξ` is in the kernel. Then `nξ` lies in the image of `Z_p ⊗ Φ`,
  which is injective in `Z_p ⊗ E` by flatness.
- `log` is injective on `Z_p ⊗ Φ` by (d). So `nξ = 0`.
- `Z_p ⊗ E ≅ Z_p^2` is torsion-free, so `ξ = 0`.

**(f) Saturation.** Now let `Γ ≅ Z^2` be given, and put `Γ' = Γ ∩ E`.

- `Γ` has finite index in `L^×`, so `Γ'` has finite index in `E` and
  `Γ' ≅ Z^2`.
- By flatness `Z_p ⊗ Γ' → Z_p ⊗ E` is injective. So `λ = log` is injective on
  `Z_p ⊗ Γ'`, and `Λ = λ(Z_p ⊗ Γ')` is free of rank 2 in `L_p ≅ Z_p^3`.
- Let `Λ^sat = Q_p Λ ∩ L_p`. It is a direct summand of `L_p`, and
  `p^c Λ^sat ⊆ Λ` for some `c`.
- Consequently, for `j ≥ c`:
  `Λ ∩ p^j L_p ⊆ Λ^sat ∩ p^j L_p = p^j Λ^sat ⊆ p^{j-c} Λ`.

**(g) Conclusion.** Put `j_0 = max(m, c+1)` and let `j ≥ j_0`. Suppose
`γ ∈ Γ ∩ (1 + p^j L)`.

1. Since `j ≥ m`, `γ ∈ E`, so `γ ∈ Γ'`.
2. By (b), `log γ ∈ p^j L_p`, so `λ(γ ⊗ 1) ∈ Λ ∩ p^j L_p ⊆ p^{j-c} Λ`.
3. By injectivity, `γ ⊗ 1 ∈ p^{j-c}(Z_p ⊗ Γ')`.
4. In a `Z`-basis `g_1, g_2` of `Γ'`, write `γ = g_1^{k_1} g_2^{k_2}`. Then
   `p^{j-c}` divides each `k_i` in `Z_p`, hence in `Z`.
5. So `γ ∈ (Γ')^{p^{j-c}} ⊆ Γ^p`. ∎

**Exact data for `Γ_± = <a, ±(a+1)>`** (exponent coordinates, from
`padic_certificate.py`). For both signs and both primes, `j_0 = 2` works.

- **`p = 2`, both signs.** The indices of `Γ ∩ (1 + 2^j L)` for
  `j = 1, ..., 8` are `7, 28, 112, 448, 1792, 7168, 28672, 114688`. The
  subgroup lies in `2Z^2` exactly from `j = 2`.
- **`p = 3`, `b = a+1`.** The indices for `j = 1, ..., 4` are
  `26, 234, 2106, 18954`, with `3Z^2` from `j = 2`.
- **`p = 3`, `b = -(a+1)`.** The indices are `13, 117, 1053, 9477`, again
  from `j = 2`.

The proof above does not use these numbers.

## Proposition

**Statement.** Let `Γ = Σ` be Eckhardt's unit group, or more generally any
`Γ ≅ Z^2` in `L^×` (after the referee's Lemma 3′, (E1) is not used). Let `S ≤ \hat Γ ≅ T^2` be a closed
subgroup that is either infinite, or finite of order divisible by `2` or `3`.
Then for every nonzero closed ideal `I ⊆ A` with `\hat α_s(I) = I` for all
`s ∈ S`, in particular for `I = A`,

`dim_Rok(\hat α|_S on I) = dim^c_Rok(\hat α|_S on I) = ∞`.

Also, for every unital `D`, the action `\hat α|_S ⊗ id` on `A ⊗ D` has
infinite Rokhlin dimension.

*Proof.*

1. **Choice of `p`.** Put `H = S^⊥ ≤ Γ`, so `S = H^⊥` and `Γ/H ≅ \hat S`.
   Choose `p ∈ {2,3}` with `p | |S|` if `S` is finite; any `p` works if `S` is
   infinite.
2. **`H Γ^p ≠ Γ`.**
   - If `S` is infinite, `Γ/H` is infinite, so `rank H ≤ 1`. Its image in
     `Γ/Γ^p ≅ (Z/p)^2` is cyclic, hence proper.
   - If `S` is finite, `|Γ/H| = |S|` is divisible by `p`. So
     `Γ/(HΓ^p) ≅ (Γ/H)/(Γ/H)^p ≠ 0`.

   Hence `(HΓ^p)^⊥ ≠ {1}`. Pick `s ≠ 1` in it; then `s ∈ S ∩ (Γ^p)^⊥`.
3. **A finite orbit inside the ideal.** By (E2), `I ∩ C(X) = C_0(U)` for a
   nonempty open invariant `U`.
   - Since `U` is open and nonempty, it contains a point `χ` of exact order
     `p^j` for some `j ≥ j_0` (density remark after Lemma 3′).
   - Let `Y = Γ·χ`. It is finite, since `X[p^j]` is finite, and `Y ⊆ U`
     because `U` is invariant.
   - By Lemmas 3′ and 4 its stabilizer is `Λ = Γ ∩ (1 + p^j L) ⊆ Γ^p`, so
     `s ∈ (Γ^p)^⊥ ⊆ Λ^⊥`.
   - (The solver's original version used (E1) to put one of the orbits
     `Γ·ξ_{p^j}` of Lemma 3 inside `U`; that works too, but Lemma 3′ removes
     the dependence on the Berend invariant-set property.)
4. **The quotient.** Let `q_Y : A → B_Y = C(Y) ⋊ Γ` be restriction. It is
   surjective and equivariant for the dual actions.
   - Since `C_0(U)` is invariant, `I ⊇ C_0(U) ⋊ Γ`.
   - Choose `g ∈ C_0(U)` with `g|_Y = 1`. Then `q_Y(I)` is an ideal of `B_Y`
     containing `q_Y(g) = 1`, so `q_Y(I) = B_Y ≠ 0`.
5. **Conclusion.** By Lemma 2, `\hat β_s = Ad(c_s)` with `c_s ∈ B_Y`. So
   `\hat β_{∞,s}` fixes `(B_Y)_∞ ∩ B_Y'`. Lemma 1, applied with `K = S`,
   `π = q_Y|_I` and `B = B_Y`, gives the claim.
6. **The tensor case.** For `A ⊗ D` (minimal tensor product; `A` is nuclear),
   use `π = q_Y ⊗ id` onto `B_Y ⊗ D` and the tensor form of Lemma 2;
   `A ⊗ D` is unital, hence σ-unital, as Lemma 1 needs. For `I = A`, neither
   (E1) nor (E2) is needed. ∎

## Corollary (the dual-action Rokhlin transfer is dead)

Let `S ≤ \hat Γ` be closed with `dim S = 1`. Then `\hat S ≅ Γ/S^⊥` has rank
one, so `H = S^⊥ ≅ Z`, generated by a unit `h ≠ ±1`.

**What the route would give.**

1. Averaging over `S` maps `f u_γ` to `1_{γ ∈ H} f u_γ`. So
   `A^S = C(X) ⋊ H = C*(L ⋊ H)` with `L ⋊ H ≅ Z^3 ⋊_{M_h} Z`.
2. This group is not virtually nilpotent. A unit of the totally real cubic
   field other than `±1` has a real conjugate of absolute value `> 1`.
3. By Eckhardt, arXiv:1309.2205, Theorem 3.3, `C*(L ⋊ H)` is not strongly
   quasidiagonal. Then Kirchberg--Winter, Theorem 5.3, gives `dr(A^S) = ∞`.
4. GHS Theorem 3.17(4): for a compact group of finite covering dimension with
   `dim^c_Rok = d < ∞`, `dr(A^S) = dr(A ⋊ S) ≤ (d+1)(dr(A)+1) - 1`. It would
   therefore give `dr(A) = ∞`.

**Why it fails.** The Proposition shows that the hypothesis
`dim^c_Rok(\hat α|_S) < ∞` fails for every such `S`. It even fails on each
nonzero invariant ideal and after tensoring with a unital `D`. So this transfer
gives no lower bound for `dr(A)`, whether it is applied to `A`, to an invariant
ideal, or to `A ⊗ D` with `D` unital. Non-unital stabilizations such as
`A ⊗ K` are not treated here.

## Remarks and non-claims

**The mechanism.**

- On every finite-orbit quotient, the finite group `Λ^⊥` acts by inner
  automorphisms implemented inside `C(Y)`.
- Finite orbits accumulate everywhere (Lemmas 3 and 4 give infinitely many
  orbits whose stabilizers lie in `Γ^p`).
- Any `S` that meets `(Γ^p)^⊥` nontrivially is therefore non-free in the
  strongest possible sense on some unital quotient of every invariant ideal.

**Finite `S` of order prime to 6.**

- The same argument works for a prime `ℓ ≥ 5` dividing `|S|`, as soon as
  `Z_ℓ ⊗ E → L_ℓ` is injective. This is a local Leopoldt statement for
  `Q(a)`.
- It should follow from the Ax--Brumer theorem (Leopoldt's conjecture for
  abelian number fields), or from Chevalley's 1951 congruence theorem for
  units. **Both references are unverified here and are not used.**
- The finite case is not needed for the Corollary.

**Not claimed.**

- Nothing is claimed about compact group actions on `A` other than the dual
  action.
- Nothing is claimed about transfer principles that do not go through
  Rokhlin dimension. Examples are a direct bound for `dr(A ⋊ S)` in terms of
  `dr(A)`, imprimitivity arguments relating `A ⋊ S` and `A^S`, and Rokhlin
  dimension for `Z`-actions in the decomposition `A = (C(X) ⋊ H) ⋊ Z`.
- Nothing is claimed about the positive direction (`dr(A) < ∞`).

## Literature

Checked 2026-09-16 via the arXiv API and ar5iv:

- **Gardella--Hirshberg--Santiago, arXiv:1709.00222v2.** Definition 1.3,
  Remark 1.4 and Theorem 3.17(4) were read in the text.
- **Eckhardt, arXiv:1309.2205v1.** Theorem 2.4, Lemma 2.2 and Theorem 3.3, as
  used in `berend-torus-actions-give-strongly-qd-polycyclic-groups`.
- **Gardella, arXiv:1407.1277v2.** Background only.
- **Hirshberg--Winter--Zacharias, arXiv:1209.1618v2.** Background only.
- **Kirchberg--Winter, Theorem 5.3.** Cited as in the root node; not
  re-fetched today.
- **Berend, Trans. AMS 280 (1983), and Archbold--Spielberg.** Used only
  through the established nodes cited above.

Unverified and not relied on: Chevalley (1951) on congruence subgroups of
units; Ax (1965) and Brumer (1967) on Leopoldt's conjecture for abelian
fields.

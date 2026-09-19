---
rg: 2
id: pro-p-route-cannot-see-amenability-in-cd-two-proof
kind: route
title: Count cells of the quotient of the 2-adic building, kill b_1 with property (T), and use the congruence subgroup property to make every pro-p completion a finite-by-analytic group; a p-good infinite completion would be an analytic pro-p group of cd 2 with positive Euler characteristic, which does not exist
target: pro-p-route-cannot-see-amenability-in-cd-two
requires:
  - pgl3-nonarchimedean-lattices-have-property-t
  - amenable-cd-two-pro-p-completions-not-golod-shafarevich
---

Notation as in the target: `E = Q(√−7)`, `h` the standard definite hermitian form on `E³`,
`G = SU(h)` over `Q`, `S = {∞, 2}`, and `Γ <= G(Z[1/2])` torsion-free of finite index. For an odd
prime `ℓ`, `G(Z_ℓ)` means the `O_E ⊗ Z_ℓ`-points of the unimodular lattice `O_E³`. `Δ` is the
Bruhat–Tits building of `SL_3(Q_2)`, and `V = |Γ\Δ^{(0)}|`.

## 0. Imports (recalled)

- **(I1) Arithmetic lattices.** Borel–Harish-Chandra: `G(Z[1/2])` is a lattice in
  `G(R) × G(Q_2)`, and it is cocompact because `G` is `Q`-anisotropic. Here `h` is definite, so it
  has Witt index 0 over `E`.
- **(I2) Property (T).** Every lattice in `PGL_3(Q_2)` has (T) (`pgl3-nonarchimedean-lattices-have-property-t`).
  `Γ` maps injectively onto a lattice there, because `μ_3(Q_2) = 1` and the image of `SL_3(Q_2)` in
  `PGL_3(Q_2)` is open of finite index. (T) passes to finite-index subgroups (BdHV Thm 1.7.1). By
  Bekka–Valette (1997), a (T) group has `b_1^{(2)} = 0`.
- **(I3) Buildings.** `Δ` is a contractible (CAT(0)) 2-dimensional simplicial complex.
  `SL_3(Q_2)` acts on it with compact stabilizers and preserves vertex types. The link of every
  vertex is the incidence graph of the Fano plane `P²(F_2)`, with 14 vertices and 21 edges.
- **(I4) Congruence subgroup property.** For `S`-arithmetic subgroups of `G` (type `²A_2`, a
  hermitian form over a quadratic extension, `S`-rank `rank_{Q_2} SL_3 = 2`), the congruence kernel
  `C = ker(\widehat{G(Z[1/2])} → \overline{G(Z[1/2])})` is finite. The bar denotes closure in
  `G(A_f^S) = ∏'_{ℓ ≠ 2} G(Q_ℓ)`. (Rapinchuk; Tomanov; Prasad–Rapinchuk survey 2010, §6.)
  Strong approximation (Kneser, Platonov) holds because `G` is simply connected and absolutely
  almost simple, and `G(Q_2)` is noncompact. So the closure `Γ̄` is open in `∏_{ℓ ≠ 2} G(Z_ℓ)`.
- **(I5) Finite groups.** `G` is smooth reductive over `Z_ℓ` for `ℓ ∉ {2, 7}`. The reduction
  `G(F_ℓ)` is `SL_3(F_ℓ)` if `ℓ` splits in `E` and `SU_3(F_ℓ)` if `ℓ` is inert, and both are
  perfect for `ℓ >= 3`. The kernel `G(Z_ℓ)^{(1)}` of `G(Z_ℓ) → G(F_ℓ)` is pro-ℓ.
- **(I6) Analytic pro-p groups** (Lazard; Dixon–du Sautoy–Mann–Segal, Ch. 3, 4, 8).
  - A pro-p group is p-adic analytic iff it has finite rank. So quotients of analytic groups,
    closed subgroups of analytic groups, and extensions of analytic groups by finite ones (or of
    finite groups by analytic ones) are analytic.
  - A torsion-free analytic pro-p group of dimension `n` has `cd_p = n` and is a Poincaré duality
    group of dimension `n`. It has an open uniform subgroup `U` with `d(U) = n`.
- **(I7) Golod–Shafarevich.** A GS pro-p group is infinite (Golod–Shafarevich). It contains a
  closed free pro-p subgroup of rank 2 (Zelmanov 2000). A free pro-p group of rank 2 has infinite
  rank, since by Schreier its open subgroups need unboundedly many generators. So a GS pro-p group
  is neither finite nor analytic. (Lubotzky, Ann. Math. 118 (1983), proves directly that analytic
  groups are not GS.)
- **(I8) Euler characteristics of pro-p groups** (Serre, *Galois cohomology*, I.4.1; Brumer). If
  `cd_p G < ∞` and every `H^i(G; F_p)` is finite, then `χ(U) = [G:U] χ(G)` for open `U`.
  `cd_p G <= n` iff `H^{n+1}(G; F_p) = 0`. Finite `cd_p` forces torsion-freeness.
- **(I9)** Atiyah's formula `χ = Σ (−1)^i b_i^{(2)}` for groups with a finite `K(Γ,1)`. Lück
  approximation for residually finite groups of type F. Lubotzky–Weiss (1993): an infinite
  amenable group has no infinite family of finite quotients whose Cayley graphs are expanders.
  (T) implies (τ).

## 1. The group; item 1

`2` splits in `E`, because `−7 ≡ 1 mod 8`. So `E ⊗ Q_2 ≅ Q_2 × Q_2`, and the special unitary
group of `h` over this split algebra is `SL_3(Q_2)`. `G(R) = SU(3)` is compact. By (I1),
`G(Z[1/2]) ⊂ G(Q) ⊂ G(Q_2)` is a cocompact lattice. Discreteness holds because
`G(Z[1/2]) ∩ (G(R) × U)` is finite for compact open `U`. Torsion-free subgroups of finite index
exist by Selberg's lemma. For level 3 in particular: `3` is inert in `E`, since `−7 ≡ 2` is a
non-square mod 3. So `O_E ⊗ Z_3 = Z_9` is unramified, and the first congruence subgroup of
`GL_3(Z_9)` is torsion-free, because the ramification index is `1 < 3 − 1`.

`Γ` is discrete and torsion-free, and stabilizers are compact, so point stabilizers of `Γ` on `Δ`
are finite and hence trivial. Because the action is type-preserving, an element that stabilizes a
simplex fixes it pointwise. So `Γ` acts freely, and `Γ\Δ` is a finite 2-dimensional CW complex.
Since `Δ` is contractible, `Γ\Δ` is a `K(Γ,1)`. Cells are counted by (I3):

- `14V` half-edge orbits pair into `7V` edge orbits;
- `21V` corner orbits give `7V` triangle orbits.

So `χ(Γ) = V − 7V + 7V = V >= 1`. `cd Γ <= 2`. If `cd Γ <= 1`, then `Γ` would be free
(Stallings–Swan), and an infinite free group has infinite abelianization, contradicting (T). So
`cd Γ = 2`.

Contracting a maximal tree (`V − 1` edges) gives a one-vertex complex with `6V + 1` loops and `7V`
2-cells, which is again aspherical. Its cellular chain complex over the universal cover is the
resolution `0 → Z[Γ]^{7V} → Z[Γ]^{6V+1} → Z[Γ] → Z → 0`. The first map is injective because
`H_2` of a contractible space is 0. So the relation module is free of rank `7V`, and `D(P) = 0`.

## 2. Item 2

By (I2) every finite-index `N` has (T), so `H_1(N; Q) = 0`. `N` has the finite `K(N,1)` given by
the `[Γ:N]`-sheeted cover, so `χ(N) = V[Γ:N]` and `b_2(N; Q) = V[Γ:N] − 1`. By (I9) and (I2),
`b_2^{(2)}(Γ) = χ(Γ) + b_1^{(2)} − b_0^{(2)} = V`.

## 3. Item 3: every pro-p completion is finite or analytic

Fix `N <= Γ` of finite index and a prime `p`. Put `H = N̄`, the closure in `∏_{ℓ ≠ 2} G(Z_ℓ)`. By
(I4) it is open.

*Step 1: `H_(p)`, the maximal pro-p quotient of `H`, is finite if `p = 2` and analytic if `p` is odd.*

Since `H` is open, there are a finite set `T` of odd primes and open normal pro-ℓ subgroups
`W_ℓ ⊴ G(Z_ℓ)` for `ℓ ∈ T` such that

> `O := ∏_{ℓ ∈ T} W_ℓ × ∏_{ℓ ∉ T ∪ {2}} G(Z_ℓ) ⊆ H`.

Take `T ⊇ {7}`, and `T ∋ p` if `p` is odd. The group `O` is normal in `∏ G(Z_ℓ)`, hence in `H`,
and `[H:O] < ∞`. Let `π : H → Q` be a continuous surjection onto a pro-p group. Then:

- for `ℓ ∈ T ∖ {p}`, `π(W_ℓ)` is a pro-p quotient of a pro-ℓ group, so it is trivial;
- for `ℓ ∉ T ∪ {2}`, `π` kills the pro-ℓ group `G(Z_ℓ)^{(1)}`, so `π|G(Z_ℓ)` factors through the
  perfect group `G(F_ℓ)` (I5). Its image is a perfect p-group, which is trivial.

The subgroup generated by the factors is dense in `O`, and `π(W_p)` is compact. So `π(O) = π(W_p)`
if `p` is odd, and `π(O) = 1` if `p = 2`, since then `p ∉ T` and there is no factor at 2. The group
`W_p` is open in `G(Z_p)`, so it is p-adic analytic, and so is its quotient `π(W_p)` (I6). Since
`π(O)` has finite index in `Q`, `Q` is analytic, or finite when `p = 2` (I6). Apply this to
`Q = H_(p)`.

*Step 2: from `H` to `N_p̂`.* `N` is finitely generated and residually finite, so `N_p̂` is the
maximal pro-p quotient of `N̂`. By (I4), `N̂ → H` is surjective with finite kernel `C_N ⊆ C`. The
induced map `N_p̂ = (N̂)_(p) → H_(p)` is surjective, and its kernel is the image of `C_N`, which is
finite. A finite-by-analytic pro-p group is analytic, and a finite-by-finite group is finite (I6).

So `N_p̂` is finite for `p = 2` and analytic for odd `p`. By (I7) it is not GS. Items 1 and 2 of
`amenable-cd-two-pro-p-completions-not-golod-shafarevich` use about `K` only four things:

- `K` is finitely generated;
- `cd K <= 2`;
- `b_2(K) < ∞`;
- no `N_p̂` is GS.

Amenability enters there only through the last. `Γ` satisfies all four, and it is of type F, so the
Euler identity is immediate. The proof of item 2 there then gives
`b_1(N; F_p) <= 2 + 2√(V[Γ:N])` for `Γ` as well.

## 4. Item 4: no p-good infinite completion

Suppose `N` is p-good and `N_p̂` is infinite. Then `p` is odd by §3, and
`H^i(N_p̂; F_p) ≅ H^i(N; F_p)` for all `i`. So `H^3(N_p̂; F_p) = 0`, and `cd_p N_p̂ <= 2` (I8).
Hence `N_p̂` is torsion-free and analytic (§3) of dimension `n = cd_p ∈ {1, 2}`, since it is
infinite (I6). Take the uniform open `U` of (I6), which has `d(U) = n`:

- if `n = 1`, then `U ≅ Z_p` and `χ(U) = 1 − 1 = 0`;
- if `n = 2`, then `U` is a Poincaré duality group of dimension 2, so `H^2(U; F_p) ≅ F_p` and
  `χ(U) = 1 − 2 + 1 = 0`.

By (I8), `χ(N_p̂) = χ(U)/[N_p̂:U] = 0`. But p-goodness gives
`χ(N_p̂) = Σ (−1)^i dim H^i(N; F_p) = χ(N) = V[Γ:N] > 0`, a contradiction.

## 5. Items 5 and 6

*Item 5.* `Γ` satisfies every hypothesis listed in item 5. It is finitely generated, residually
finite (it is linear), of type F, with `cd = 2` (§1), and it has no GS completion (§3). Every
further input listed there, namely Euler identities, Bass/Swan structure over finite quotients,
cohomology rings with their operations, and degree-refined GS inequalities, is a consequence of
these hypotheses that holds for all groups satisfying them. So the argument would prove
`χ(Γ) <= 0`, contradicting `χ(Γ) = V >= 1`.

- (a) By §2 and §3, `Γ` has `b_1(N; F_p) <= 2 + 2√(V[Γ:N])` and `b_2(N; Q) = V[Γ:N] − 1` in every
  finite cover, which are the two inputs of the cup-product step.
- (b) By §4, the hypothetical positive answer to the pro-p question would give, for a
  counterexample `K`, exactly the conclusion "no p-good finite-index subgroup has infinite pro-p
  completion", and `Γ` satisfies it for every `p`.

*Item 6.* For `Γ`, `b_2^{(2)} = V` (§2). By (I9), Lück approximation gives
`b_2(N_i)/[Γ:N_i] → V` along any residual chain of normal subgroups. This is consistent with §2.
For an amenable `K`, Cheeger–Gromov gives `b_*^{(2)}(K) = 0`. So `dim_U P = n − 1`, and
`D(P) = χ(K)` (`amenable-cd-two-bass-defect-equals-euler-characteristic`). For `Γ`, the relation
module is free with `D = 0` (§1). Finally, `Γ` has (T), hence (τ), while an infinite amenable `K`
has no family of expanding finite quotients (I9). These are the two known consequences of amenability that separate `K` from `Γ`: vanishing `L²`-Betti numbers,
and the failure of (τ) (Følner sets surviving in finite quotients). An argument that sees neither
cannot separate them. Which of the two can be used without type `FP_2` is the open question behind
`rf-weak-bass-defect-is-degree-two-approximation-defect`.

## 6. Scope, honestly

The obstruction covers arguments whose only use of amenability is the non-GS property of pro-p
completions. It does not rule out a profinite argument that uses non-expansion of finite quotients,
or any Følner or `L²` argument. The dependence on (I4) is confined to §3–§4. Without the congruence
subgroup property, §1–§2 still show that `Γ` has the rational profile of a counterexample
(`b_1 = 0`, `b_2 = χ·index − 1`) at every finite index.

---
rg: 2
id: thompson-f-hosts-have-infinite-hochschild-dimension-proof
kind: route
title: Eilenberg--Rosenberg--Zelinsky upper bound against the Koszul top class of a polynomial subalgebra, induced from the fraction field; diagonal induction for Cantor crossed products
target: thompson-f-hosts-have-infinite-hochschild-dimension
requires: [universal-localizations-of-quasi-free-algebras-are-quasi-free]
---

Unmarked tensor products are over the base field `k`. `A^e = A ⊗ A^op`. The only imported node is used
in part 4(a).

## Step 1. Upper bound (ERZ)

**Lemma 1.** If `hd_k A = d` and `U` is a `k`-algebra, then `l.gl.dim(A ⊗ U) <= d + l.gl.dim U`.

*Proof.* Let `M` be a left `A ⊗ U`-module, and let `0 -> Q_d -> ... -> Q_0 -> A -> 0` be a projective
`A^e`-resolution.
- It splits as a sequence of right `A`-modules, since `A` is right projective. So `Q_• ⊗_A M -> M` is exact.
- Each `Q_i` is a summand of a sum of copies of `A^e`, and `A^e ⊗_A M = A ⊗ M`. Here `A` acts on the
  left factor, and `U` acts through `M`.
- Tensor a projective `U`-resolution of `M` with `A` over `k`. This gives `pd_(A⊗U)(A ⊗ M) <= pd_U M`.
- Dimension shifting finishes the proof. ∎

With `U = K = k(y_1..y_n)`, a field, this gives `l.gl.dim(A ⊗ K) <= d`, and so `w.gl.dim(A ⊗ K) <= d`.

## Step 2. Lower bound (Koszul, induced from the fraction field)

**Lemma 2.** If `A` has a commuting independent family `a_1..a_n`, then `w.gl.dim(A ⊗ K) >= n`, where
`K = k(y_1..y_n)`. No flatness of `A` over `k[a]` is assumed.

*Setup.*
- `C = k[a_1..a_n] ⊆ A` is a polynomial ring, by independence.
- `R = A ⊗ K`, and `S = C ⊗ K ⊆ R`, which is commutative and equal to `K[a_1..a_n]`.
- `z_i = a_i ⊗ 1 - 1 ⊗ y_i`. These are a regular sequence in `S`, with `S/I ≅ K` via `a_i ↦ y_i`, where
  `I = Σ z_i S`.
- Restricted to `C`, the module `S/I` is `C` acting on `k(y)` through `a_i ↦ y_i`. This is `Frac(C)`, which is
  flat over `C`.

*Resolution.*
- Let `K_•` be the Koszul complex of `z` over `S`. It is a free resolution of `S/I` of length `n`.
- Put `F_• = R ⊗_S K_•`, a complex of free left `R`-modules. Its homology is `Tor^S_•(R, S/I)`.
- As a right `S`-module, `R ≅ A ⊗_C S`, by `a ⊗ (c ⊗ κ) ↦ ac ⊗ κ`.
- `S` is free over `C`, so a projective `C`-resolution `P_•` of `A` induces a projective `S`-resolution
  `P_• ⊗_C S`. Hence `Tor^S_i(R, S/I) = Tor^C_i(A, Frac C) = 0` for `i >= 1`.
- So `F_•` resolves `Q = R / Σ R z_i` in length `n`.

*Top class.*
- As a left `S`-module, `R ≅ S ⊗_C A`. So `Q' = R / Σ z_i R ≅ Frac(C) ⊗_C A`.
- The class `q` of `1` is nonzero, because `c · 1 = c ≠ 0` for every `c ∈ C ∖ 0`.
- `Tor^R_n(Q', Q) = ker(Q' -> Q'^n, u ↦ (± u z_i))`. This kernel contains `q ≠ 0`, since `q z_i` is the class
  of `z_i ∈ z_i R`.
- Hence `w.gl.dim R >= n`. ∎

**Non-unital maps.** Let `φ : k[x_1..x_n] -> A` be injective, not necessarily unital, and let `P = c + G ≠ 0`,
where `c ∈ k` and `G(0) = 0`.
- If `c = 0`, then `P(φ(x)) = φ(G) ≠ 0`.
- If `c ≠ 0` and `P(φ(x)) = 0`, then `1_A = φ(h)` with `h = -G/c`. So `φ(h^2) = φ(h)`, and `h^2 = h` in the
  domain `k[x]`. Since `h(0) = 0`, this forces `h = 0`, and then `A = 0`.

So `φ(x_1..x_n)` is a commuting independent family.

**Part 1.** Combine Lemmas 1 and 2. A family of size `d + 1` gives `d + 1 <= w.gl.dim(A ⊗ K) <= d`, which is
impossible.
- For `M_r(A)` and `p M_r(A) p`, the inclusion `p M_r(A) p ⊆ M_r(A) = A ⊗ M_r(k)` is a non-unital injective
  map, and `hd_k(A ⊗ M_r(k)) <= hd_k A + hd_k M_r(k) = hd_k A`. (Tensor the two bimodule resolutions over `k`.
  `M_r(k)` is separable, so `hd = 0`.)
- For `k[Z^(d+1)] ⊇ k[x_1..x_(d+1)]`, restrict the map. ∎

## Step 3. Part 2 (central base change)

**Lemma 3.** Let `K_0 ⊆ K ⊆ Z(L)` be fields. Then `hd_(K_0) L <= hd_K L + hd_(K_0) K`.

*Proof.* Put `E_0 = L ⊗_(K_0) L^op`, `E = L ⊗_K L^op` and `K^e = K ⊗_(K_0) K`.
- `K^e` maps centrally into `E_0`, because `K` is central in `L`, and `E = E_0 ⊗_(K^e) K`.
- `L` is free over `K`. So `E_0 = ⊕_(i,j) K b_i ⊗ b_j K` is free over `K^e`, where `(b_i)` is a `K`-basis of
  `L`.
- Base-change a projective `K^e`-resolution of `K` of length `c = hd_(K_0) K` to an `E_0`-resolution of `E`.
  This gives `pd_(E_0) E <= c`, and hence `pd_(E_0) P <= c` for every projective `E`-module `P`.
- Take a projective `E`-resolution of `L` of length `hd_K L`. Dimension shifting gives the bound. ∎

**Lemma 4.** If `K ⊇ Q` is finitely generated of transcendence degree `e`, then `hd_Q K <= e`.

*Proof.* Pick a transcendence basis, so that `K ⊇ K_0 = Q(t_1..t_e)` is finite separable (char 0).
- *The separable step.* `K ⊗_(K_0) K` is semisimple, so `hd_(K_0) K = 0`.
- *The polynomial ring.* `P = Q[t_1..t_e]` has `hd_Q P = e`. The Koszul complex of `t_i ⊗ 1 - 1 ⊗ t_i`, a
  regular sequence in `P ⊗ P = Q[t, t']`, resolves `P`.
- *Localization.* `K_0 = S^(-1) P` with `S = P ∖ 0`. Then `K_0 ⊗ K_0 = (S ⊗ S)^(-1)(P ⊗ P)` is flat over
  `P ⊗ P`, and `K_0 ≅ (K_0 ⊗ K_0) ⊗_(P⊗P) P`, since `s ⊗ s'` acts on `P` as `ss'`. So `hd_Q K_0 <= e`.
- Lemma 3, with `L = K` and central subfield `K_0`, gives `hd_Q K <= 0 + e`. ∎

Lemmas 3 and 4 with `K_0 = Q` give Part 2.

## Step 4. Part 3 (hosts)

- Let `φ : Z[H] -> L` be unital injective, and let `Q ⊆ Z(L)`.
- Then `Q[H] = Q ⊗ Z[H] -> L` is injective: if `x/N` maps to `N^(-1) φ(x) = 0`, then `x = 0`.
- Hence `Q[Z^m] ⊆ Q[H] ⊆ L`, and Part 1 over `k = Q` gives `hd_Q L >= m`. Part 2 then gives
  `hd_K L >= m - e`.

**Thompson's `F`.**
- It is finitely presented (Cannon--Floyd--Parry) and has solvable word problem (normal forms).
- The elements supported in `[0, 1/2]` and those supported in `[1/2, 1]` form a copy of `F × F`. Iterating
  gives `F^m ≤ F`, and so `Z^m ≤ F` for every `m`.
- `F ≤ T ≤ V ≤ nV`. ∎

## Step 5. Part 4 (the host classes)

Throughout, `k = K`. Tensor products are covered because a tensor product over `K` of bimodule resolutions is
a bimodule resolution, so `hd(A ⊗ B) <= hd A + hd B`.

**(a) Quasi-free algebras.**
- The free algebra `T(V)` has `hd <= 1`, via `0 -> T ⊗ V ⊗ T -> T ⊗ T -> T -> 0`.
- `L_K(1,n)` is its universal localization at the row `T^n -> T`.
- Apply `universal-localizations-of-quasi-free-algebras-are-quasi-free`.

**(b) Cantor crossed products.** Let `A = LC(X, K)` and `B = A ⋊ G = ⊕_g A u_g`.

*`hd A <= 1`.*
- `A^e = LC(X × X, K)`, and `A = A^e / I`, where `I` is the ideal of functions vanishing on the diagonal `Δ`.
- `X` is metrizable, so there are clopen neighbourhoods `W_1 ⊇ W_2 ⊇ ...` with `∩ W_n = Δ`. Take
  `W_n = ∪ U × U` over clopen partitions of mesh `< 1/n`, each refining the previous one.
- Every `f ∈ I` has compact clopen support disjoint from `Δ`, so that support misses some `W_n`.
- So `I = ∪_n e_n A^e`, where `e_n = 1 - 1_(W_n)` are increasing idempotents. Then
  `I = ⊕_n (e_n - e_(n-1)) A^e` is projective, and `pd_(A^e) A <= 1`.

*Diagonal induction.*
- In `B^e`, let `C` be generated by `A ⊗ A^op` and `w_g = u_g ⊗ (u_(g^-1))^op`.
- `w_g w_h = w_(gh)`, and `(A ⊗ A^op) w_h = A u_h ⊗ (A u_(h^-1))^op`.
- So `C = ⊕_h (A ⊗ A^op) w_h ≅ A^e ⋊ G`, where `G` acts diagonally. It is free over `A^e` on both sides.
- `B^e = ⊕_(g,h) A u_g ⊗ (A u_h)^op = ⊕_g (u_g ⊗ 1) C`. Each summand `(u_g ⊗ 1) C` is the sum of the pieces
  indexed by `(gh, h^(-1))`, `h ∈ G`. So `B^e` is a free right `C`-module.
- `A ⊆ B` is a `C`-submodule: `w_g · a = g(a)`, and `(a ⊗ b^op) · x = a x b`.
- `B^e ⊗_C A -> B`, `(u_g ⊗ 1) ⊗ a ↦ u_g a`, is a bijection onto `⊕_g u_g A = B`, and it is
  `B^e`-linear. So `pd_(B^e) B <= pd_C A`.

*`pd_C A <= 1 + cd_Q G`.*
- Let `P_•` be a projective `K[G]`-resolution of `K` of length `cd_K G <= cd_Q G`. (Base-change a
  `Q[G]`-resolution.)
- `A ⊗_K P_•`, with `C` acting by `(a ⊗ b^op)(x ⊗ p) = a x b ⊗ p` and `w_g(x ⊗ p) = g(x) ⊗ g p`, is an exact
  complex of `C`-modules over `A`.
- `A ⊗ K[G] ≅ C ⊗_(A^e) A`, via `w_h ⊗ x ↦ h(x) ⊗ h`. This is a direct check on both kinds of generators.
- `C` is free over `A^e`, so `pd_C(C ⊗_(A^e) A) <= hd A <= 1`. Summands and sums preserve this bound.
- Dimension shifting gives `pd_C A <= 1 + cd_Q G`. ∎

**Corners and matrices.** For every `B` in (a) or (b), and every tensor product of such, `hd_K B < ∞`.
- A unital `Z[F] -> p M_r(B) p` is a non-unital injection `Q[Z^m] -> M_r(B)`, for every `m`.
- This contradicts Part 1 with `A = B`. ∎

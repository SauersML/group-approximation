---
rg: 2
id: sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational-proof
kind: route
title: Expansivity gives the clopen sets, harmonic elimination gives Q, compression gives simplicity, the Haar-conjugate measure gives Fuglede–Kadison, blocks give matrix units, and the vanishing transfer turns block units into signs
target: sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational
requires:
  - harmonic-elimination-puts-q-in-odometer-crossed-products
  - sl3-congruence-transfer-kills-abelianization
  - matricial-divisibility-kills-rational-k2-symbols
  - q-algebra-elementary-quotients-contain-gl-n-q
---

Lane proof (gq-deep-adelic-1), not independently reviewed. Notation as in the target; conventions
`u_g h u_g^(-1) = h ∘ g^(-1)` and `u_g χ_W = χ_(gW) u_g`.

**Part 1.**
- **Clopen sets.** `u_γ χ_[a] u_γ^(-1)` is the indicator of `{x : x(γ^(-1)) = a}`. Every cylinder is a
  finite product of these, and every clopen subset of `X` is a finite disjoint union of cylinders, so
  `LC(X, Z) ⊆ R_T`.
- **Q.** `Q ⊆ R_T` by `harmonic-elimination-puts-q-in-odometer-crossed-products`. Its hypotheses hold: the
  chain `Γ((n+1)!)` is strictly decreasing and normal, `π` is equivariant, and `u_γ^(±1) ∈ R_T`.

**Part 2.**
- **Freeness.** `γx = x` forces `γπ(x) = π(x)`, hence `γ = 1`.
- **Minimality.** Toeplitz subshifts are minimal.
- **Local constancy.** Every coefficient `b` of an element `Σ b_g u_g` lies in `C(X, Q)`, and is locally
  constant on a dense open set. Given a nonempty clopen `W`, `b(W)` is compact and countable, so it has
  an isolated point `q`, and `b^(-1)(q) ∩ W` is a nonempty open set on which `b` is constant.
- **Compression.** With these three facts, the argument of steps (c)–(d) of
  `tracial-harmonic-ring-keeps-rational-scalars-proof` applies verbatim. Pick
  `x = Σ_(g∈J) b_g u_g ∈ I` with `b_e != 0`, and a clopen `W` on which `b_e = r ∈ Q^x` and with
  `gW ∩ W = ∅` for `g ∈ J ∖ {e}`. Then `χ_W x χ_W = r χ_W`, so `χ_W ∈ I`. Finitely many translates of
  `W` cover `X`, which gives `1 ∈ I`.
- **Centre.** Freeness forces the coefficients of a central element off `e` to vanish, and minimality
  forces the remaining coefficient to be constant. So the centre is `Q`.

**Part 3.**
- **The factor.** `(X, ν) ≅ (K, Haar)` as `Γ`-systems, so the action is essentially free and ergodic, and
  `ν` has no atoms. So `M = L^∞(X, ν) ⋊ Γ` is a II_1 factor, and `C(X,Q) ⋊_alg Γ -> M` is a unital
  `*`-preserving ring map.
- **The determinant.** As in step 3(b) of `matrix-corner-laurent-rings-block-fp-elementary-groups-proof`,
  `ψ(X) = Δ_N(X)^N` defines a homomorphism `K_1(R_T) -> R_(>0)` with `ψ([λ]) = |λ|`. So the kernel of
  `Q^x -> K_1(R_T)` lies in `{±1}`.
- **Scalars.** If `λ I_N ∈ E_N(R_T)`, then `|λ|^N = ψ(λ I_N) = 1`.
- **The rest.** Use parts 2 and 4 of `q-algebra-elementary-quotients-contain-gl-n-q`, with the centre
  `Q` from part 2.

**Part 4.**
- **Matrix units.** Let `C_d = π^(-1)(closure of Γ(d))`. It is clopen, since `Γ(d) ⊇ Γ_n` for large `n`.
  Its translates `tC_d`, `t ∈ Γ/Γ(d)`, partition `X`, and translates are equal or disjoint.
  - So `e_(ts) = u_t χ_(C_d) u_s^(-1) ∈ R_T` are matrix units with `Σ_t e_(tt) = 1`, as in step 6 of
    `matrix-corner-laurent-rings-block-fp-elementary-groups-proof`.
  - This gives `R_T ≅ M_(n_d)(χ_(C_d) R_T χ_(C_d))`.
- **Divisibility.** `SL_3(Z) -> SL_3(Z/d)` is onto (strong approximation), so
  `n_d = |SL_3(Z/d)| = d^8 Π_(p | d) (1 - p^(-2))(1 - p^(-3))`. Its `p`-part is at least
  `p^(8k-5)` when `p^k || d`, so `d | n_d`.
- **Conclusion.** The matricial divisibility node applies.

**Part 5.** Lee–Szczarba, as quoted in the transfer node: every `Γ(d)^ab` is finite, so no `Γ(d)`
surjects onto `Z`.

**Part 6.**
1. **Monomial form.**
   - Let `C'` be a block of level `d^2` inside `C`, with stabilizer `Γ(d^2)`. `C` is the union of the
     `k = [Γ(d) : Γ(d^2)]` sub-blocks `sC'`, for `s` in a set of representatives `T'` of
     `Γ(d)/Γ(d^2)`.
   - With the level-`d^2` matrix units of part 4, `R_T ≅ M_(n_(d^2))(S')` with `S' = χ_(C') R_T χ_(C')`.
   - Under this isomorphism `v` is a monomial matrix. On the sub-blocks outside `C` its entries are
     `1_(S')`. On the sub-blocks of `C` it maps `sC'` to `γsC' = t_s C'` with entry
     `χ_(C') u_(h_s)`, where `h_s = t_s^(-1) γ s ∈ Γ(d^2)`.
2. **K_1 of a monomial matrix.** Its class is the class of its permutation part plus the sum of the
   classes of its entries. A permutation matrix over `S'` has the class of `diag(sgn, 1, ..., 1)`, i.e.
   `ε·[1_(S')]` with `ε = sgn ∈ K_1(Z)`. Under the Morita isomorphism `K_1(S') ≅ K_1(R_T)` this is
   `ε·[χ_(C')]` (the `K_1(Z)`-multiple of the `K_0` class of `χ_(C')`).
3. **The entries.** `h ↦ χ_(C') u_h` is a group homomorphism `Γ(d^2) -> (S')^x`, since
   `χ_(C') u_h χ_(C') = χ_(C') u_h` for `h ∈ Γ(d^2)`. So the entries contribute `[χ_(C') u_(V(γ))]`,
   where `V(γ) = Π_s h_s` in `Γ(d^2)^ab` is the transfer of `γ`.
4. **The transfer vanishes.** `V(γ) = 0` by `sl3-congruence-transfer-kills-abelianization`. So
   `[v] = ε·[χ_(C')]`.
5. **Symbols.** Loday: the product `K_1(Q) ⊗ K_1(R_T) -> K_2(Q ⊗ R_T) = K_2(R_T)` sends
   `[λ] ⊗ [v]` to `±{λ, v}`, and the products are natural and associative (Weibel, *The K-book*,
   IV.1.10, number unconfirmed; the noncommutative form `[a] ⊗ [b] ↦ {a⊗1, 1⊗b}` is Loday's, unread:
   trust surface T3). So `{λ, v} = ±x·[χ_(C')]` with `x = {λ, ε} ∈ K_2(Q)`, which is the image of
   `x` under `K_2(Q) -> K_2(χ_(C') R_T χ_(C')) ≅ K_2(R_T)`. The corner `χ_(C') R_T χ_(C')` is itself
   matricially divisible: the blocks of level `e` inside `C'`, for `d^2 | e`, give
   `χ_(C') R_T χ_(C') ≅ M_([Γ(d^2):Γ(e)])(...)`, and these indices are divisible by every integer. So
   `matricial-divisibility-kills-rational-k2-symbols` makes that image `0`.
6. **The rest.**
   - `[u_γ]` lies in the image of `Γ^ab = 0`, since `SL_3(Z)` is perfect.
   - Classes add under products, and so do the symbols `{λ, ·}` through the Loday product. So every
     product of these units has trivial rational symbols.

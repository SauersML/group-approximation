# Fock-local rank models of the Leavitt unit groups

Lane `w4-fock-model`, 2026-09-12. Directive: build a nontrivial rank model of
`G_3 = L_(F_3)(1,2)^x` or `R^x = L_(F_2)(1,2)^x` through the Fock-locality idea of
`research/artifacts/char-three-level-factoring-and-hnn-models-2026-09-12.md`, Section 3, or land where it
fails.

## 0. Setting and verdict

* `q` is a power of the prime `p` (`p = 2` for `R^x`, `p = 3` for `G_3`). `X = {0,1}^N` is the Cantor set.
* `U_j = F_q^(2^j)` is the space of functions on `X` constant on depth-`j` cylinders. The inclusions
  `U_j ⊆ U_(j+1)` exhaust `U_∞ = LC(X, F_q)`.
* The Leavitt algebra acts on `U_∞` by `(s_0 f)(0w) = f(w)`, `(s_0 f)(1w) = 0` and `(t_0 f)(w) = f(0w)`,
  and similarly for `s_1, t_1`. So the unit group `G` acts invertibly on `U_∞`.
* The level group `L_j = GL_(2^j)(F_q)` (depth-`j` matrix units) preserves `U_j`, and `L = ∪_j L_j`.
* For a clopen `A`, `U_A^(j)` is the subspace of functions in `U_j` supported on `A`. When `A` is a union
  of depth-`j` cylinders, `U_j = U_A^(j) ⊕ U_(A^c)^(j)`.
* **Fock spaces.** `S_j = Λ(U_j)` has dimension `2^(2^j)`. The linear isomorphism
  `ω_A ∧ ω_B -> ω_A ⊗ ω_B` identifies `Λ(U_A^(j) ⊕ U_(A^c)^(j))` with `Λ(U_A^(j)) ⊗ Λ(U_(A^c)^(j))`,
  compatibly with `Λ(a_A ⊕ a_(A^c)) = Λ(a_A) ⊗ Λ(a_(A^c))`.

**Verdict.** No nontrivial rank model of `G_3` or `R^x` is built. What lands:
1. **Theorem 1:** exterior tensor powers are asymptotically free over every finite linear group. This
   proves the step the char-3 artifact left open ("non-projective proportion over 3-subgroups"), in
   every characteristic and without Brauer characters.
2. **Theorem 2:** the Fock tower on `L` extends to letters acting on single Fock factors, with EXACT
   commutation of disjointly supported letters (Section 2).
3. **Proposition 3:** the natural Fock quantization of the forced truncated compressors fails the
   Toeplitz commutator by exactly `1/4` (Section 3), and the multi-letter relations stay open.

## 1. Asymptotic freeness of exterior tensor powers

**Lemma 1.1 (free seed).** Let `Γ ≤ GL(W)` be finite, `W` over `F_q`, `w = dim W`. Then `F_qΓ` is a
direct summand of `(F_q ⊕ W)^(⊗ r)` for some `r <= w^3 (q − 1)`, hence of `Λ(W)^(⊗ r)`.

*Proof.*
1. **Free orbit.** Let `e_1, ..., e_w` be a basis of `W*` and `v = (e_1, ..., e_w) ∈ (W*)^(⊕w)`. Its
   stabilizer is trivial, because `Γ` acts faithfully on `W*`. So `Γ·v` is a free orbit, and the
   permutation module `F_q[Γ·v]` is isomorphic to `F_qΓ`.
2. **Polynomial functions.** Put `Z = (W*)^(⊕w)`. Polynomial functions on `Z` of degree `<= D` form the
   `Γ`-module `⊕_(n<=D) S^n(Z*)`, with `Z* ≅ W^(⊕w)`. Over `F_q` every function on a finite set of
   points is a polynomial of degree `<= D = w^2 (q−1)`: the indicator of `a` is `∏_i (1 − (x_i − a_i)^(q−1))`.
   Restriction to the orbit is `Γ`-equivariant and onto, so `⊕_(n<=D) S^n(W^(⊕w)) -> F_qΓ` is onto.
3. **Splitting.** `S^n(Y)` is a quotient of `Y^(⊗n)`, and `(F_q ⊕ Y)^(⊗D) = ⊕_n C(D,n) Y^(⊗n)` contains every
   `Y^(⊗n)` with `n <= D`. So some `Γ`-map `(F_q ⊕ W^(⊕w))^(⊗D) -> F_qΓ` is onto. `F_qΓ` is projective,
   so the map splits.
4. **Back to `W`.** `F_q ⊕ W^(⊕w)` is the total-degree-`<= 1` summand of `(F_q ⊕ W)^(⊗w)`, so
   `(F_q ⊕ W^(⊕w))^(⊗D)` is a summand of `(F_q ⊕ W)^(⊗wD)`. And
   `(F_q ⊕ W)^(⊗r)` is the summand of `Λ(W)^(⊗r) = Λ(W ⊗ F_q^r)` of multidegree `<= 1` in each copy. Take
   `r = wD`. QED

**Theorem 1.2 (asymptotic freeness).** With `Γ, W, r` as in Lemma 1.1, put `η = |Γ| 2^(−wr) ∈ (0,1]`.
For every `m >= 0`,

`Λ(W)^(⊗m) ≅ F_qΓ^c ⊕ N`, with `dim N <= (1 − η)^⌊m/r⌋ · 2^(wm)`.

*Proof.* Write `Λ(W)^(⊗r) = F_qΓ ⊕ R`, so `dim R = (1 − η) 2^(wr)`. With `s = ⌊m/r⌋`,
`Λ(W)^(⊗m) = (F_qΓ ⊕ R)^(⊗s) ⊗ Λ(W)^(⊗(m − rs))`. Every term of the expansion containing an `F_qΓ` factor is
free, since `F_qΓ ⊗ Y ≅ F_qΓ^(dim Y)`. What remains is `R^(⊗s) ⊗ Λ(W)^(⊗(m−rs))`, of dimension
`(1−η)^s 2^(wm)`. QED

**Corollary 1.3 (rank-close actions).** Let `ρ, ρ'` be two actions of `Γ` on one space `S` of dimension
`D`, each of the form `F_qΓ^(c_i) ⊕ N_i` with `dim N_i <= δD`. Then some `X ∈ GL(S)` has
`rk(X ρ(a) X^(−1) − ρ'(a)) <= δD` for all `a ∈ Γ`.

*Proof.* Both free parts have at least `c = min(c_1, c_2) >= (1−δ)D/|Γ|` copies. Let `X` map a free
`F_qΓ^c ⊆ ρ` isomorphically onto `F_qΓ^c ⊆ ρ'`, and a complement onto a complement. Then
`X ρ(a) X^(−1) − ρ'(a)` vanishes on `F_qΓ^c ⊆ ρ'`, so its rank is at most `D − c|Γ| <= δD`. QED

**Corollary 1.4 (Fock level tower).** Let `σ_Λ(a) = Λ(a)` on `S_j` for `a ∈ L_j`, and `1` otherwise. Then
`σ_Λ = lim_ω σ_j` is an injective rank model of `L` over `F_q`. On every finite subgroup it is
asymptotically free: for `Γ ≤ L_i` and `j >= i`, `S_j|_Γ = Λ(U_i)^(⊗ 2^(j−i))` is free up to proportion
`(1−η)^⌊2^(j−i)/r⌋`. In characteristic three, `z` acts by parity. Asymptotic freeness over tori is the
Haar law on the signed diagonal, up to vanishing error.

*Proof.* `U_j|_(L_i) = U_i ⊗ F_q^(2^(j−i))`, so `Λ(U_j) = Λ(U_i)^(⊗2^(j−i))`, and Theorem 1.2 applies to
the image of `Γ` in `GL(U_i)`. For injectivity, `a ≠ 1` acts on `F_qΓ` with fixed space of dimension
`|Γ|/ord(a) <= |Γ|/2`, so `rk(σ_j(a) − 1)/dim S_j -> >= 1/2` along the free part. QED

**Remark 1.5 (what this settles).** The char-3 artifact's gap was that the "non-projective part of
`Λ(U)^(⊗m)` [needs] vanishing proportion over 3-subgroups". Theorem 1.2 gives vanishing NON-FREE
proportion over every finite subgroup, in every characteristic. So the intertwiner step of the Fock idea
holds. Section 2 builds the letters. Section 3 shows what locality does not give.

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

## 2. Fock-local letters

**Support.** `g ∈ G` is *supported on* a clopen `A` if `g` preserves `LC(A)` and acts as the identity on
`LC(A^c)`. Examples: elements of `V` fixing `A^c` pointwise, and level elements that mix only
cylinders inside `A`. For such `g` put `B_g^A = {a ∈ L : a preserves LC(A) and LC(A^c), g a g^(−1) ∈ L}` and
`φ_g(a) = g a g^(−1)`. Then `φ_g(a)` also preserves both, and it agrees with `a` on `LC(A^c)`.
- *Correction 2026-09-12 from w3-vf-linear (Section 28).* The first version only required that `a`
  preserve `LC(A)`. That admits block upper triangular level elements such as
  `a = 1 + δ_(c1) ⊗ δ_(c2)*` with `c1 ⊆ A` and `c2 ⊆ A^c`.
  - For `g ∈ V` supported on `A`, `g a g^(−1) = 1 + δ_(g c1) ⊗ δ_(c2)* ∈ L`.
  - But `φ_g(a)` does not agree with `a` on `LC(A^c)`, and `Λ(a)` is not a product `ρ(a) ⊗ Λ(a|)`.
  - Such elements move mass across the support. They belong to case (b) of Consequence 2.4.

**Definition 2.1.** Let `I ⊆ G` be countable, and fix a support `A_g` for each `g ∈ I`. The group
`𝒢_loc(I)` has generators `L ∪ {t_g : g ∈ I}` and relations:
* **(R1)** the relations of `L`;
* **(R2)** `t_g a t_g^(−1) = φ_g(a)` for `a ∈ B_g^(A_g)`;
* **(R3)** `[t_g, a] = 1` for `a ∈ L` supported on `A_g^c`;
* **(R4)** `[t_g, t_h] = 1` whenever `A_g ∩ A_h = ∅`.

`t_g -> g` defines a homomorphism `𝒢_loc(I) -> G`. For (R3) and (R4), elements with disjoint supports
act blockwise on `LC(A) ⊕ LC(A^c)` and commute. `G` acts faithfully on `U_∞`, because `R` is simple.

**Theorem 2.2 (Fock-local extension).** For every countable `I`, the Fock tower `σ_Λ` of Corollary 1.4
extends to a homomorphism `𝒢_loc(I) -> M^x`, injective on `L`, with `σ(t_g) = [X_(g,j) ⊗ 1]_ω` and
`X_(g,j) ∈ GL(Λ(U_(A_g)^(j)))`. The relations (R3) and (R4) hold exactly at every stage. In odd
characteristic each `X_(g,j)` is even, meaning it preserves the parity grading of `Λ(U_(A_g)^(j))`, and
(R4) needs this.

*Proof.* Fix `g ∈ I`, `A = A_g`, and stages `j` at least the depth of `A`, so that
`S_j = S_A^(j) ⊗ S_(A^c)^(j)` with `S_A^(j) = Λ(U_A^(j))`.
1. **Exhaustion.** Put `Γ_i = B_g^A ∩ L_i`. These are finite and increasing, with union `B_g^A`. Let `c(i)`
   be the least level containing `Γ_i ∪ φ_g(Γ_i)` and at least the depth of `A`.
2. **Two actions on one factor.** For `j >= c(i)` and `a ∈ Γ_i`, put `ρ(a) = Λ(a|_(U_A^(j)))` and
   `ρ'(a) = Λ(φ_g(a)|_(U_A^(j)))`.
   - For `a ∈ L_c` preserving `LC(A)`, `U_A^(j)|_a = U_A^(c) ⊗ F_q^(2^(j−c))`. So
     `ρ ≅ Λ(W)^(⊗2^(j−c))` with `W = U_A^(c)`, and the same holds for `ρ'`.
   - Both actions factor through `Γ_i/K` with the same kernel `K`: `a` acts trivially on `LC(A)` iff
     `φ_g(a)` does, since `g|_(LC(A))` is invertible.
   - Theorem 1.2, applied to the two faithful images, bounds the non-free proportions by some
     `δ_(i,j) -> 0` as `j -> ∞` with `i` fixed.
3. **Local intertwiners.** Corollary 1.3 gives `X_(g,j) ∈ GL(S_A^(j))` with
   `rk(X ρ(a) X^(−1) − ρ'(a)) <= δ_(i,j) · dim S_A^(j)` for all `a ∈ Γ_i`.
   - Choose `i(j) = max{i <= j : c(i) <= j, δ_(i,j) <= 1/i}`, or `0` if there is none, with `X_(g,j) = 1`
     in that case. For fixed `i_0` both conditions hold once `j` is large, so `i(j) -> ∞`.
   - **Even letters in odd characteristic.**
     - `z_A` (`−1` on `LC(A)`, `+1` on `LC(A^c)`) is a level element preserving `LC(A)` and `LC(A^c)`, and
       it commutes with `g`. So `z_A ∈ Γ_i` for large `i`.
     - It is central in `Γ_i`, because every element of `Γ_i` is block diagonal.
     - `ρ(z_A) = ρ'(z_A)` is the parity operator.
     - Matched free parts of equal rank are `z_A`-stable, with equal parity eigenspace dimensions. Since
       `p` is odd, `z_A`-stable complements exist, and they have equal eigenspace dimensions too.
     - Matching inside each parity makes `X_(g,j)` even.
4. **(R2).** Let `a ∈ B_g^A`. For `ω`-almost all `j`, `a ∈ Γ_(i(j))`, and
   `Λ(a) = ρ(a) ⊗ Λ(a|_(U_(A^c)))`, `Λ(φ_g(a)) = ρ'(a) ⊗ Λ(a|_(U_(A^c)))`. So
   `(X ⊗ 1) Λ(a) (X ⊗ 1)^(−1) − Λ(φ_g(a)) = (X ρ(a) X^(−1) − ρ'(a)) ⊗ Λ(a|)`, of normalized rank
   `<= 1/i(j) -> 0`.
5. **(R3).** If `a ∈ L` is supported on `A^c`, then `Λ(a) = 1 ⊗ Λ(a|)`, which commutes with `X ⊗ 1` exactly.
6. **(R4).** If `A_g ∩ A_h = ∅`, then `S_j = S_(A_g) ⊗ S_(A_h) ⊗ S_rest` through one associative wedge
   isomorphism, and `X_(g,j) ⊗ 1 ⊗ 1` commutes with `1 ⊗ X_(h,j) ⊗ 1` exactly.
   - Each letter was defined in its own identification, with its support first. Reordering wedge
     factors multiplies `ω_g ∧ ω_h` by `(−1)^(|ω_g||ω_h|)`, which commutes with even operators.
   - So in odd characteristic the even letters of step 3 are `X_(g,j) ⊗ 1 ⊗ 1` and `1 ⊗ X_(h,j) ⊗ 1` in
     one identification. In characteristic two the sign is `1`.
   - (Precision added after w3-vf-linear, Section 28.)
7. **Injectivity** on `L` is Corollary 1.4. QED

**Remark 2.3 (characteristic three, anti-central).** Restrict to `S_j^odd`, the `−1`-eigenspace of
`σ_Λ(z)` (parity). The letters can be chosen even, so they preserve `S_j^odd`.
- The letters are even by step 3 of the proof, and even `X` commutes with the global parity
  `parity_A ⊗ parity_(A^c)`.
- So `𝒢_loc(I)` has an injective-on-`L` anti-central rank model, with the Haar law up to vanishing error.
- In characteristic two no grading is needed.

**Consequence 2.4 (sharpening the "no" direction).** Every relation of `G` that follows from (R1)–(R4)
holds in a rank model injective on `L`, which is anti-central in characteristic three. Consequence 2.6
of `research/artifacts/char-three-level-factoring-and-hnn-models-2026-09-12.md` listed "commutation of
disjointly supported depth-changing elements" among the relations a triviality proof might use. On its
own, together with support-preserving partial conjugations, that relation forces nothing. A proof that
every rank model of `G_3` (or of `R^x`) is trivial must use at least one of:
* **(a)** a multiplication-table relation `t_g t_h = t_(gh)` between letters with overlapping supports;
* **(b)** a partial conjugation `t_g a t_g^(−1) = φ_g(a)` by a level element `a` that moves mass between
  `A_g` and `A_g^c`. Such elements lie in `B_g ∖ B_g^(A_g)`. The HNN model of Theorem 2.3 there realizes
  these, but without locality;
* **(c)** a Steinberg commutator among non-level root elements with overlapping supports, such as
  `[x_12(t0), x_23(s0)] = x_13(1)`.

No single model realizing (R1)–(R4) together with the full-domain partial conjugations is known.

## 3. The compressor pair and where locality stops

**Proposition 3.1 (natural Fock quantization of the compressors).** Take the forced solution of
Proposition 7 of `research/artifacts/el3-rank-model-compressor-extension-2026-09-12.md` on `W_N = V_N^3`:
`X^ = 1 + T_N E_12`, `Y^ = 1 + S_N E_23`, `Z^ = 1 + E_13`, with `Z^^(−1)[X^, Y^] = u_13(N−1, N−1)`. Then
`Λ(Z^)^(−1) [Λ(X^), Λ(Y^)] = Λ(u_13(N−1, N−1))` on `Λ(W_N)`, and
`rk(Λ(u_13(N−1,N−1)) − 1) = dim Λ(W_N) / 4`. The same proportion `1/4` holds on `Λ^even` and `Λ^odd`.

*Proof.*
1. **Functoriality.** `Λ : GL(W) -> GL(Λ(W))` is a homomorphism, so it carries the commutator identity
   over unchanged.
2. **Transvections.** Let `u = 1 + v ⊗ φ` with `φ(v) = 0`. On `w_1 ∧ ... ∧ w_k`,
   `Λ(u) = ∧_i (w_i + φ(w_i) v)`. Terms containing `v` twice vanish, so `Λ(u) − 1 = v ∧ i_φ`, where `i_φ` is
   contraction.
3. **Rank.** Choose a basis `e_1 = v`, `e_2` with `φ(e_2) = 1`, and `e_3, ..., e_n` spanning the rest of
   `ker φ`. Then `v ∧ i_φ` sends `e_2 ∧ ω'` to `e_1 ∧ ω'` for `ω' ⊆ {e_3, ..., e_n}` and kills every other
   basis monomial. Its rank is `2^(n−2)`, and it preserves parity. On `Λ^odd` the rank is
   `2^(n−3) = dim Λ^odd / 4` for `n >= 3`. QED

**Reading.**
- **The error does not decay.** Second-quantizing the forced truncated shifts turns the one-transvection
  defect of Corollary 8 there into a Fock defect of normalized rank exactly `1/4`, at every `N`.
- **Such models are excluded anyway.** They factor through `Λ(GL)`, where transvections are displaced by
  `1/4`. So `transvection-displacement-forces-exact-local-embedding` (characteristic two) and
  `char-three-level-factoring-models-of-leavitt-units-are-trivial` rule them out.
- **What the compressors need.** They must be abstract non-level letters. Their supports overlap, so
  Theorem 2.2 gives them nothing, and the Toeplitz commutator is a relation of type (c).

**3.2 Where the construction stops.**
* **Coherence is untouched.** On an asymptotically free factor, each local intertwiner is unique up to
  the commutant of `ρ'(Γ_i)`. That commutant is rank-close to `GL_c(F_qΓ_i^op)`, which is large. The
  cocycle `X_g X_h X_(gh)^(−1)` for overlapping supports lies approximately in it, and locality says
  nothing about it.
* **Tensor factors do not dilute errors.** An error `E` on a factor `S_A` has
  `rk(E ⊗ 1)/dim S_j = rk(E)/dim S_A`.
  - So a relation that can only be resolved on factors of bounded dimension costs a fixed proportion of
    rank. At stage `j` those are pieces at the finest depth.
  - Example: `τ_(A,B) = τ_(A0,B0) τ_(A1,B1)` for a transposition of cylinders of different depths. The
    deepest pieces are not resolved at depth `j`.
  - Letters built as `X ⊗ 1` over coarse supports avoid this. Letters built by refining down to the
    resolution do not.
* **Exact equivariant locality is impossible.** Suppose finite-dimensional factors `S(A)` satisfied
  `S(A ⊔ B) ≅ S(A) ⊗ S(B)` and `S(gA) ≅ S(A)` for `g ∈ V`. Since `V` moves `c` onto `c0`,
  `dim S(c) = dim S(c)^2`, so every factor is trivial. Letters therefore have to be abstract intertwiners
  over coarse supports, as in Theorem 2.2, never second quantizations of one-particle maps.
* **Not reached.** No rank model of `G_3` or `R^x` is built. The gate
  `ternary-leavitt-units-have-a-nontrivial-char-three-rank-model` is still open, and so is the binary
  gate.

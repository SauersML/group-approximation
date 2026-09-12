# Leavitt tensor hosts for Boone--Higman, 2026-09-12

Lane `boone-higman` (fork relaunched 2026-09-12). Boone--Higman stays open.
This record proves four things.

1. **Host theorem.** Let `B` be a simple unital `F_2`-algebra, let
   `L = L_(F_2)(1,2)`, and put `R = B ⊗ L`.
   - If `K_1(R) = K_2(R) = 0`, then `GL_m(R) = E_m(R)` for `m >= 2`, `H_1` and
     `H_2` of every `GL_r(R)` vanish, and `St_r(R) -> GL_r(R)` is an
     isomorphism for `r >= 3`.
   - If all `K_i(R)`, `i >= 1`, vanish, every `GL_r(R)` is integrally acyclic.
   - If `B` is a finitely presented ring, `R^x` is finitely presented.
   - If `B` is central simple, `R^x` is simple.
2. **A second finitely presented simple Leavitt unit group.** `(L ⊗ L)^x` is
   finitely presented, simple and integrally acyclic.
3. **A new Boone--Higman class.** Every finitely generated linear group over
   a field of characteristic two with transcendence degree at most two embeds
   in `(L ⊗ L)^x`.
4. **Two reductions.**
   - All finitely generated linear groups in characteristic two satisfy
     Boone--Higman once `K_1` and `K_2` of every tensor power `L^(⊗d)` vanish.
   - The conjecture itself follows once every `F_2[G]` with `G` decidable
     embeds unitally in a finitely presented central simple `F_2`-algebra `B`
     with `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`.

## Sources, read from the PDFs

The texts are on MSI in `/projects/standard/hsiehph/sauer354/lit-groups/`.

- **Khanh, arXiv:2609.08428v1** (`khanh-clean.txt`; verified import
  `research/artifacts/khanh-2609-08428-leavitt-gl-verified-2026-09-11.md`).
  - Theorem 2.2, "Suppose that A^2 ≅ A as right A-modules. Assume also that
    (1) ... the standard inclusion Γ_(n+2) -> Γ_(n+3) induces zero on H_n;
    (2) H̃_i(X_r(A)) = 0 for 0 <= i <= r-3 and r >= 4. Then H_n(A^x) = 0 for
    every n > 0." Section 2 is written for "nonzero unital F_2-algebras".
  - Lemmas 2.3 and 2.4, and Theorem 5.1: "Let B be a nonzero unital ring of
    characteristic two, and fix n >= 4. Suppose that (1) GL_(n-1)(B) =
    E_(n-1)(B) and GL_(n-2)(B) = E_(n-2)(B); (2) j_(n-1)(N_(n-1)(B)) = 1 in
    St_n(B); (3) |X_n(B)| is simply connected. Then φ_n is an isomorphism."
  - Lemma 5.2 ("For any unital ring B and m >= 3, j_m(N_m(B)) is central").
  - The Menal--Moncasi remark quoted in the proof of Lemma 5.3. It "applies to
    a simple ring in which each nonzero x admits y,z with yxz = 1, and
    requires no regularity assumption".
  - Voronetsky's refinement as applied in the proof of Theorem 5.4, and
    Krstić--McCool Theorem 3 as used in Theorem 6.1.
- **Ara--Cortiñas, Tensor products of Leavitt path algebras,
  arXiv:1108.0352v3** (`1108.0352.txt`).
  - Lemma 6.1, "Let E be a finite graph. Then L(E) is regular supercoherent."
  - Proposition 6.2, "Let R be regular supercoherent. Then the algebraic
    K-theories of L_2 and of L_2 ⊗ R are both trivial."
  - The abstract: "we have K_*(L_2) = K_*(L_2 ⊗ L_2) = 0".
  - The ground field is an arbitrary field `k`; here `k = F_2`.
- **Ara--Brustenga--Cortiñas, arXiv:0903.0056v2** (`abc-clean.txt`).
  - Theorem 7.6 needs regular supercoherent coefficients.
  - Theorem 8.6 gives the homotopy `KH` sequence "Let A be a ring, and E a
    row-finite quiver". So `KH(A ⊗ L) = 0` for every ring `A`.

## 1. What in Khanh's proof is specific to `L`

- **Theorem 2.2, Lemmas 2.3 and 2.4.** Proved for every nonzero unital
  `F_2`-algebra `A` with `A^2 ≅ A`. The finite fields `F_(2^m)` enter through
  `A ≅ M_m(A)`, not through `L`. Nothing to change.
- **Theorem 5.1 and Lemma 5.2.** Ring-general. Nothing to change.
- **Voronetsky refinement, Krstić--McCool.** They use only the Leavitt
  identities `T_r U_r = I`, `U_r T_r = I` in a ring containing
  `e, f, e*, f*`, and a finite presentation of the ring. Nothing to change.
- **Proposition 3.2.** The compression part uses only `e, f`. The stable
  input `H_n(GL_∞(R)) = 0` came from ABC Theorem 7.6 for `L`. *Replaced by the
  hypothesis on `K_*(R)`* (Section 3).
- **Lemma 4.1, Proposition 4.2, Corollary 4.3.** Leavitt word reduction over
  `F_2`, where a nonzero coefficient is `1`. Over `B ⊗ L` the coefficient is a
  nonzero `c` in `B`. *Repaired in Section 2 using simplicity of `B`.*
- **Lemma 5.3.** GE for simple rings with strong division, plus perfectness.
  *Needs strong division in `R` (Section 2) and `H_1(R^x) = 0` (Section 4).*

## 2. Division and frame extension over `B ⊗ L`

Let `B` be a simple unital `F_2`-algebra and `R = B ⊗_(F_2) L`.
- `B ⊗ 1` commutes with `L`, and every element of `R` is a finite sum of
  `b ⊗ αβ*` with `α, β` positive words.
- Positive words are linearly independent in `L`, so
  `B ⊗ F_2<e,f> -> R` is injective.

**Lemma 2.1 (normalization).** For nonzero `a_1, ..., a_s` in `R` there are
`x` in `R`, nonempty positive words `η_i` and nonzero `c_i` in `B` with
`η_i* a_i x = c_i ⊗ 1` for every `i`.

*Proof.* This is Khanh's proof of Lemma 4.1 with coefficients in `B`.
1. Choose `N` at least every `|β|` occurring in expressions of the `a_i`, and
   let `γ_1, ..., γ_t` be the words of length `N`.
   - Each `a_i γ_j` lies in `B ⊗ F_2<e,f>`.
   - Since `a_i = Σ_j (a_i γ_j) γ_j*`, some `a_i γ_j` has a nonzero
     coefficient in `B`.
2. Let `Λ` bound all word lengths, put `t_j = e^(j(Λ+1)) f` and
   `x_0 = Σ_j γ_j t_j`.
   - The words of `(a_i γ_j) t_j` have lengths in
     `[j(Λ+1)+1, j(Λ+1)+1+Λ]`. These intervals are disjoint for distinct `j`,
     and concatenation with a fixed `t_j` is injective.
   - So no coefficients combine, and `P_i = a_i x_0` has a nonzero coefficient.
3. Take `M` larger than every word length in the `P_i` and `x = x_0 e^M f`.
   - The support of `P_i e^M f` is a prefix antichain (Khanh (4.1)).
   - Let `η_i` be a support word with coefficient `c_i != 0`. Since `η_i* ν`
     is `1` for `ν = η_i` and `0` for every other support word,
     `η_i* a_i x = c_i ⊗ 1`. `∎`

**Lemma 2.2 (simultaneous strong division).** For nonzero `a_1, ..., a_s` in
`R` there are `X` and `u_1, ..., u_s` in `R` with `u_i a_i X = 1` for every
`i`, together with explicit isomorphisms of right modules `ker u_i ≅ R`.

*Proof.*
1. **Normalize.** Take `x, η_i, c_i` from Lemma 2.1. Since `B` is simple, for
   each `i` there are finitely many `y_(ik), z_(ik)` in `B` with
   `Σ_k y_(ik) c_i z_(ik) = 1`.
2. **Separate the indices.** Choose pairwise distinct positive words `β_(ik)`
   of one common length, so `β_(ik)* β_(i'k') = δ`. Put
   `Z = Σ_(i,k) z_(ik) ⊗ β_(ik)` and `Y_i = Σ_k y_(ik) ⊗ β_(ik)*`. Then
   `Y_i (c_i ⊗ 1) Z = Σ_k y_(ik) c_i z_(ik) ⊗ 1 = 1`, because every cross term
   carries `β_(ik)* β_(i'k') = 0`.
3. **Define `u_i`, `X`.** With `u_i = Y_i η_i*` and `X = x Z`,
   `u_i a_i X = Y_i (c_i ⊗ 1) Z = 1`.
4. **The kernel.** `η_i* η_i = 1` splits `R = η_i R ⊕ ker η_i*`, so
   `ker u_i = η_i ker Y_i ⊕ ker η_i*`.
   - By Khanh (4.2), `ker η_i* ≅ R^h` through the sibling row, with
     `h = |η_i| >= 1`.
   - `Y_i W_i = 1` for `W_i = (c_i ⊗ 1) Z`, so `R = W_i R ⊕ ker Y_i` with
     `W_i R ≅ R`, that is, `R ⊕ ker Y_i ≅ R`.
   - Hence `ker u_i ≅ ker Y_i ⊕ R ⊕ R^(h-1) ≅ R^h ≅ R`, using leaf
     coordinates for the last step.
   Every isomorphism is a composite of the displayed maps. `∎`

**Corollary 2.3.** `R` is simple, and every nonzero `x` admits `a, b` with
`a x b = 1`. If `B` is central, the centre of `R` is
`Z(B) ⊗ Z(L) = F_2`, since `Z(L) = F_2` (`leavitt-center-is-coefficient-field`).

**Proposition 2.4 (Khanh Proposition 4.2 over `R`).** Each finite family of
simplices of `X_r(R)` with at most `r-2` vectors has one vector `v` extending
every frame, and each extended frame has a nonzero complement of the right
formal size.

*Proof.* Follow Khanh's proof, replacing `(x, η_i*)` from his Lemma 4.1 by
`(X, u_i)` from Lemma 2.2.
- The decomposition `R^r = W_i ⊕ vR ⊕ σ_i ker u_i` needs only `u_i y_i = 1`
  for `y_i = ρ_i v = a_i X`.
- The complement `σ_i ker u_i` is identified with `R^(q_i - 1)` through
  `ker u_i ≅ R ≅ R^(q_i - 1)`, since `q_i >= 2`. `∎`

**Corollary 2.5.** `H̃_d(X_r(R)) = 0` for `0 <= d <= r-3`, and `|X_4(R)|` is
simply connected. These are Khanh's coning argument (Corollary 4.3) and the fan
argument of his Theorem 5.4, which use only Proposition 4.2.

## 3. The standard inclusions

**Proposition 3.1.** Fix `n >= 1`. If `H_n(GL_∞(R), Z) = 0`, then every standard
inclusion `GL_r(R) -> GL_(r+1)(R)` induces zero on `H_n`.

*Proof.* Khanh's proof of Proposition 3.2 with its first paragraph replaced by
the hypothesis. The steps use only `e, f` in `R`.
1. The compression `c(u) = e u e* + f f*` is a group endomorphism of `R^x`.
2. Leaf coordinates give `Φ_(s+1)(c(u)) = diag(Φ_s(u), I)`, so `(R^x, c)` is
   the dyadic cofinal subsystem of the standard system, and
   `colim(H_n(R^x), c_*) = H_n(GL_∞(R)) = 0`.
3. The unit `w = e e e* + e f (fe)* + f (ff)*` gives `w c(u) w^-1 = c(c(u))`.
   So `c_*` is idempotent. Being locally nilpotent, it is zero on `H_n`.
4. The comb recurrence (3.7) identifies the standard inclusions with `c`. `∎`

**Remark 3.2.** By the plus construction and Hurewicz, `H_n(GL_∞(R)) = 0` for
`1 <= n <= N` exactly when `K_i(R) = 0` for `1 <= i <= N`. With `K_1 = 0`,
`H_2(GL_∞(R)) = K_2(R)`.

## 4. Transfer of Khanh's conclusions

**Theorem 4.1 (acyclicity by degree).** Let `N >= 1` and suppose `K_i(R) = 0`
for `1 <= i <= N`. Then `H_n(GL_r(R), Z) = 0` for `1 <= n <= N` and every
`r >= 1`. If every `K_i(R)`, `i >= 1`, vanishes, every `GL_r(R)` is integrally
acyclic.

*Proof.* Khanh's proof of Theorem 2.2 is an induction on `n`. Step `n` uses:
- `H_t(R^x) = 0` for `0 < t < n`;
- hypothesis (1) in degree `n` only, through the stabilizer inclusion
  `J_(1,n+2) -> Γ_(n+3)` of Lemma 2.4;
- hypothesis (2) at `r = n+3` only.

Proposition 3.1 and Remark 3.2 give (1) in degrees `<= N`. Corollary 2.5 gives
(2) at every `r`. The ranks are then transported by leaf coordinates
`GL_r(R) ≅ R^x`. `∎`

**Theorem 4.2.** Suppose `K_1(R) = K_2(R) = 0`.
1. `GL_m(R) = E_m(R)` for every `m >= 2`.
2. `St_r(R) -> GL_r(R)` is an isomorphism for every `r >= 3`.
3. If `B` is a finitely presented ring, then `R^x` is finitely presented.

*Proof.*
1. This is Khanh's proof of Lemma 5.3.
   - Menal--Moncasi GE applies by Corollary 2.3: every invertible matrix is a
     product of elementary and invertible diagonal matrices.
   - `H_1(R^x) = 0` by Theorem 4.1, so every unit is a product of commutators
     and `diag(u,1) ∈ E_2(R)`.
2. This is Khanh's proof of Theorem 5.4.
   - `St_3(R)` is perfect. With `H_2(GL_3(R)) = 0`, the five-term sequence
     gives `N_3 = [St_3, N_3]`, and Lemma 5.2 gives `j_3(N_3) = 1` in `St_4`.
   - Corollary 2.5 makes `|X_4(R)|` simply connected, and part 1 gives
     hypothesis (1) of Theorem 5.1. So `φ_4` is an isomorphism.
   - Voronetsky's refinement uses only the Leavitt identities, so it carries
     rank four to every `r >= 3`.
3. Write `B = Z<b_1, ..., b_p>/(finitely many relators)`. Then `R` is the ring
   with the following generators and relators:
   - generators `b_1, ..., b_p, e, f, s, t`;
   - the relators of `B`;
   - `2, se-1, tf-1, sf, te, es+ft-1` (Khanh (6.1));
   - the commutators of each `b_j` with `e, f, s, t`.

   Krstić--McCool Theorem 3 makes `St_5(R)` finitely presented. Part 2 and leaf
   coordinates give `R^x ≅ GL_5(R) ≅ St_5(R)`. `∎`

## 5. Simplicity

**Theorem 5.1.** Let `B` be central simple.
- For every `n >= 3`, `E_n(R)` is a simple group.
- If `K_1(R) = K_2(R) = 0`, then `R^x ≅ GL_3(R) = E_3(R)` is simple, infinite
  and nonabelian.

*Proof.* The Lean theorem `rootDetection_of_leavittFamily` in
`GroupApproximation/Leavitt/RootDetectionBinary.lean` is stated for an
arbitrary ring with three inputs:
- a Leavitt family, here `e, f, e*, f*`;
- the division property `x != 0 -> ∃ a b, a x b = 1`, here Corollary 2.3;
- the condition that every central unit is `1`. Here a central unit lies in
  `Z(R) = F_2` (Corollary 2.3), so it is `1`.

Then `isSimpleGroup_of_rootDetection` in
`GroupApproximation/Leavitt/ElementarySimplicity.lean` gives simplicity of
`E_n(R)`, `n >= 3`. The second assertion uses Theorem 4.2(1). The roots
`x_12(s_0^k)` are distinct, and `[x_12(1), x_23(1)] = x_13(1)`. `∎`

## 6. The square `L ⊗ L`

**Theorem 6.1.** `(L ⊗ L)^x` is a finitely presented, simple, infinite and
integrally acyclic group, and `St_r(L ⊗ L) -> GL_r(L ⊗ L)` is an isomorphism
for `r >= 3`.

*Proof.* Take `B = L`.
- `L` is central simple (`leavitt-center-is-coefficient-field`, and Corollary
  2.3 with `B = F_2`) and a finitely presented ring (Khanh (6.1)).
- Ara--Cortiñas Lemma 6.1 makes `L` regular supercoherent, and their
  Proposition 6.2 gives `K_*(L ⊗ L) = 0`.
- Apply Theorems 4.1, 4.2 and 5.1. `∎`

Ara--Cortiñas Example 5.2 shows `L ⊗ L` is not Morita equivalent to `L`.
Whether the unit groups `(L ⊗ L)^x` and `L^x` are isomorphic is not settled
here.

## 7. Linear groups of characteristic two

**Lemma 7.1 (Laurent realization).** Let `d >= 1` and let
`h ∈ F_2[t_1, ..., t_d]` be nonzero. There is a unital injective ring map
`F_2[t_1, ..., t_d][1/h] -> L^(⊗d)`.

*Proof.* Induction on `d`.
- **`d = 1`.** Put `f = t h`, which is monic over `F_2`. Steps 3--4 of
  `char-two-curve-linear-groups-proof` give
  `F_2[t][1/h] ⊆ F_2[t][1/f] -> M_(deg f)(F_2[g^±]) -> M_(deg f)(L) ≅ L`.
- **`d >= 2`.**
  - Write `h ∈ C_0[t_d]` with `C_0 = F_2[t_1, ..., t_(d-1)]` and leading
    coefficient `c != 0`. Put `C = C_0[1/c]` and `f = t_d h / c ∈ C[t_d]`,
    monic of degree `>= 1`. Then `1/h = t_d/(c f)`, so
    `F_2[t_1, ..., t_d][1/h] ⊆ C[t_d][1/f]`.
  - `T |-> t_d`, `g |-> f(t_d)` identifies `C[g^±][T]/(f(T) - g)` with
    `C[t_d][1/f]`. Since `f(T) - g` is monic in `T`, this is a free
    `C[g^±]`-module with basis `1, T, ..., T^(deg f - 1)`. Multiplication gives
    a unital injection `C[t_d][1/f] -> M_(deg f)(C[g^±])`.
  - `C[g^±] = C ⊗ F_2[g^±]` embeds in `L^(⊗(d-1)) ⊗ L`. Use induction for `C`,
    the Thompson-unit embedding `F_2[g^±] -> L` of
    `char-two-laurent-linear-groups-proof`, and injectivity of tensor products
    of injective maps over a field.
  - Finally `M_k(L^(⊗d)) ≅ L^(⊗d)` through leaf coordinates in one factor. `∎`

**Theorem 7.2.** Let `K` be a field of characteristic two, and let
`H <= GL_n(K)` be finitely generated.
- `H` embeds in `(L^(⊗max(d,1)))^x`, where `d` is the transcendence degree of
  the field generated by the entries of the generators and their inverses.

*Proof.*
1. If `d = 0`, the entries lie in a finite field, `H` is finite, and it embeds
   in `GL_N(F_2) <= L^x`.
2. Otherwise the entry field is finite, of degree `m`, over `F_2(t_1, ..., t_d)`
   for a transcendence basis. The regular representation gives
   `H <= GL_(nm)(F_2(t_1, ..., t_d))`.
3. Clearing denominators gives `H <= GL_(nm)(F_2[t_1, ..., t_d][1/h])`.
4. Apply Lemma 7.1 and leaf coordinates. `∎`

**Corollary 7.3.** Every finitely generated linear group over a field of
characteristic two with transcendence degree at most two embeds in the finitely
presented simple group `(L ⊗ L)^x`, so it satisfies Boone--Higman.
- Examples: the finitely generated subgroups of `GL_n(F_q(t_1, t_2))`,
  `SL_n(F_q[t_1, t_2])` for `n >= 3` (finitely generated by Suslin's
  `SL_n = E_n`), and `Z/2 wr Z^2 <= GL_2(F_2[t_1^±, t_2^±])`.
- Finite products of such groups embed through block-diagonal matrices.

**Corollary 7.4 (conditional).** If `K_1(L^(⊗d)) = K_2(L^(⊗d)) = 0` for every
`d >= 3`, then every finitely generated linear group in characteristic two
satisfies Boone--Higman.

*Proof.* `L^(⊗d) = L^(⊗(d-1)) ⊗ L`. A tensor product of central simple algebras
over a field is central simple, and a tensor product of finitely presented
algebras is finitely presented. Apply Theorems 4.2, 5.1 and 7.2. `∎`

## 8. What stays open

### 8.1 Tensor powers
- **`KH` vanishes.** ABC Theorem 8.6 gives `KH(A ⊗ L) = hofiber(-1) = 0` for
  every ring `A`, so `KH(L^(⊗d)) = 0` for every `d`.
- **Sufficient conditions for `K_1 = K_2 = 0`.** Either of these suffices:
  - `K_2`-regularity of `L^(⊗d)` (ABC Section 8, Vorst);
  - regular supercoherence of `L^(⊗(d-1))` (Ara--Cortiñas Proposition 6.2).
- **Transferring Lemma 6.1.** Its proof uses two ingredients: flatness of the
  universal localization `P(E) -> L(E)`, and regular coherence of
  `P(E)[t_1, ..., t_n]`.
  - Flatness passes to `P(E) ⊗ S -> L(E) ⊗ S` by base change.
  - The missing lemma is regular coherence of the free algebras
    `S[t_1, ..., t_n]<e,f>` for `S = L^(⊗(d-2))`. It may already be in Gersten,
    *K-theory of free rings* (1974), or Waldhausen (1978); neither was read.

### 8.2 The universal reduction
**Proposition 8.1.** Let `G` be finitely generated, and suppose `F_2[G]`
embeds unitally in a finitely presented central simple `F_2`-algebra `B` with
`K_1(B ⊗ L) = K_2(B ⊗ L) = 0`. Then `G <= B^x <= (B ⊗ L)^x`, which is finitely
presented and simple by Theorems 4.2 and 5.1. So `G` satisfies Boone--Higman.

- **Sufficient condition.** Regular supercoherence of `B` suffices for the
  `K`-theory condition (Ara--Cortiñas Proposition 6.2).
- **Complexity.** The complexity wall
  (`complexity-bounded-host-classes-are-not-universal`) is respected: `B` may
  have arbitrarily hard word problems.
- **What changes from the old ring lane.** `boone-higman-via-projective-ring-host`
  must finitely normally generate an unstable Steinberg kernel over an
  arbitrary host (`projective-elementary-fp-kernel-criterion`). After
  tensoring with `L`, that kernel is trivial once `K_1` and `K_2` vanish. What
  remains is an existence problem for algebras.
- **Literature.** Evans--Mandelberg--Neff (1975) give the algebra analogue of
  the classical weak half (a simple algebra embedded in a finitely presented
  one), not finitely presented simple hosts.

### 8.3 Limits and trust
- **Odd characteristic.** Khanh's Section 2 is written for `p = 2` (the weights
  of Lemma 2.3, and `w_ij^2 = 1` in Theorem 5.1). Not attempted.
- **Novelty.** The Belk--Bleak--Matucci--Zaremsky survey arXiv:2306.16356v3
  lists `GL_n(Z)` as known and `GL_n(Q)` as open. Zaremsky arXiv:2405.09722
  settles `GL_n(Q)`. A web search on 2026-09-12 found no positive-characteristic
  linear class. This is a bounded check.
- **Trust surface.** Khanh's preprint is unrefereed. The transfer here rereads
  its general criteria and replaces the two `L`-specific steps. It does not
  re-derive his spectral sequence.

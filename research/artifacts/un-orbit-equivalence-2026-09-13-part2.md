# Does S_X ≅ S_Y force orbit equivalence? Part 2: the K_0 group of the subshift crossed product

Lane `un-orbit-equivalence`, 2026-09-13. Status:
- §1 is a verbatim import of ABC arXiv:0903.0056 (extracted text on MSI; lost glyphs marked [·]).
- §2 (Theorem K) is proved here and UNREVIEWED.
- §3 records what is still owed for the order cone and for Giordano–Putnam–Skau.
Part 1 (`un-orbit-equivalence-2026-09-13-part1.md`) has step (a): Zel'manov, Theorem G, and firewalls F-PE1/F-PE2.

## 1. Ara–Brustenga–Cortiñas, verbatim

P. Ara, M. Brustenga, G. Cortiñas, *K-theory of Leavitt path algebras*, Münster J. Math. 2 (2009),
arXiv:0903.0056v2. Source: `/projects/standard/hsiehph/sauer354/lit-groups/abc-clean.txt` on MSI. The extraction
drops Greek letters, ⊗, ± and arrows. Those glyphs are restored from context and marked [·]; all words are verbatim.

(A1) Theorem 3.6 (l.389–398):
> "Theorem 3.6. Let R be a unital ring and let A be a ring. Let [σ] : R → pRp be a corner-isomorphism. Assume that
> R[⊗]A is H-unital. Then there is a homotopy fibration of nonconnective spectra K(R[⊗]A) → K(R[⊗]A) [⊕]
> NK(R[⊗]A;[σ⊗1])[_+] [⊕] NK(R[⊗]A;[σ⊗1])[_−] → K((R[⊗]A)[t+;t−;σ⊗1]). In other words, K((R[⊗]A)[t+;t−;σ⊗1]) =
> NK(R[⊗]A;[σ⊗1])[_+] [⊕] NK(R[⊗]A;[σ⊗1])[_−] [⊕] hocofiber(K(R[⊗]A) [→(1−σ⊗1)] K(R[⊗]A))."

(A2) Proof of Theorem 3.6, Step 1 (l.399–401):
> "Step 1: Assume that [σ] is a unital isomorphism and A = Z. In this case the skew Laurent polynomial ring is the
> crossed product by Z; R[t+;t−;σ] = R[t;t^{−1};σ]. Let i[_±] : R → R[t[_±];σ] and j[_±] : R[t[_±];σ] →
> R[t+;t−;σ] be the inclusion maps. By the proof of [34, Theorem 2.1], there is a homotopy fibration
> K(R)[⊕]K(R) → K(R[t+;σ])[⊕]K(R[t−;σ]) → K(R[t+;t−;σ]) and K(R[t[_±];σ]) = K(R)[⊕]NK(R;σ)[_±]."

(A3) Lemma 7.2 (l.1017–1020):
> "Lemma 7.2. Let R be a regular supercoherent ring and let [α] be an automorphism of R. Extend [α] to an automorphism
> of R[t_1;t_1^{−1};...;t_p;t_p^{−1}] by [α](t_i) = t_i. Then NK_n(R[t_1;t_1^{−1};...;t_p;t_p^{−1}];[α]) = 0 for every
> p ≥ 0 and every n ∈ Z."

(A4) §7 definitions (l.943–949):
> "Recall that a unital ring R is said to be coherent if its finitely presented modules form an abelian subcategory of
> the category of all modules. We say that R is regular coherent if it is coherent and in addition any finitely
> presented module has finite projective dimension. Equivalently R is regular coherent if any finitely presented module
> has a finite resolution by finitely generated projective modules. The ring R is called supercoherent in case all
> polynomial rings R[t_1;...;t_p] are coherent".

(A5) Proof of Lemma 3.5:
> "the fact that K-theory preserves filtering colimits (see [31, IV.6] for the unital case [...])".

## 2. Theorem K

**Theorem K.** Let `X` be a Cantor set, `T` a homeomorphism, `q` a prime power, `A = LC(X,F_q)` and
`R_X = A ⋊_T Z = A[t,t^(−1);σ]` with `σ(f) = f ∘ T^(−1)`. Then the inclusion `A ⊆ R_X` induces
`K_0(R_X) ≅ C(X,Z)/(1 − T_*)C(X,Z)`, with `[χ_U] ↦ [χ_U]` and `[1] ↦ [χ_X]`.

*Proof.*
1. **A is a directed union.** `A` is the directed union of the subrings `A_P ≅ F_q^P` over finite clopen partitions
   `P`, under refinement.
2. **Regular supercoherent.** Over a finite product of fields every module is projective, so the transition maps
   `A_P[t_1..t_p] → A_(P')[t_1..t_p]` are flat. Each stage is a finite product of polynomial rings over `F_q`,
   Noetherian and regular.
   - A finitely presented module over `A[t_1..t_p]` is induced from one at a finite stage.
   - Its finite resolution by finitely generated projectives there stays exact after flat base change.
   - Kernels of maps between finitely presented modules are computed at a finite stage, so finitely presented modules
     form an abelian subcategory.
   Hence `A` is regular supercoherent in the sense of (A4).
3. **The fibration.** `A` is unital, so `A ⊗ Z = A` is H-unital, and `σ` is a unital isomorphism. By (A1)–(A2) there
   is a homotopy fibration whose `NK(A;σ)_±` terms vanish by (A3), with `p = 0`. So
   `K(R_X) = hocofiber(1 − σ_*: K(A) → K(A))`, and the maps from `K(A)` are induced by the inclusions `i_±, j_±`
   of (A2). That gives the exact sequence
   `K_0(A) →(1−σ_*) K_0(A) → K_0(R_X) → K_(−1)(A) →(1−σ_*) K_(−1)(A)`.
4. **K_0 and K_{−1} of A.** By (A5), `K_0(A) = colim_P K_0(A_P) = colim_P Z^P = C(X,Z)`, with `[χ_U] ↦ χ_U`.
   `K_(−1)(A) = colim K_(−1)(F_q^P) = 0`, since negative K-theory of a field vanishes. This is Bass's theorem,
   recalled and not re-read.
5. **Conclusion.** `K_0(R_X) ≅ coker(1 − σ_*)`. Because `σ_*` is bijective and `1 − σ_*^(−1) = −σ_*^(−1)(1 − σ_*)`,
   the images of `1 − σ_*` and `1 − T_*` coincide (`T_* = σ_*`). The unit maps to `[χ_X]`. ∎

**Model test.** For `T = id`, the theorem says `K_0(A[t,t^(−1)]) = C(X,Z) = K_0(A)`. Bass's fundamental theorem gives
`K_0(A[t,t^(−1)]) = K_0(A) ⊕ K_(−1)(A)`, which agrees since `K_(−1)(A) = 0`. For a periodic `T` of period `k` on the
Cantor set, coinvariants keep one copy per orbit class of clopens, as expected.

## 3. What remains for steps (b) and (c)

- **(b2) The order cone.** `K_0^+(R_X)` means the classes of idempotents in `M_∞(R_X)`.
  - **One inclusion is known.** Ara–Claramunt (`cantor-z-crossed-product-embeds-in-continuous-factor`, established)
    give, for every full ergodic invariant `μ`, a faithful Sylvester matrix rank function with `rk_μ(χ_U) = μ(U)`. So
    every nonzero idempotent class is strictly positive on every ergodic `μ`, hence on every invariant measure. In
    the other direction, every class of a nonnegative function is a sum of idempotent classes `[χ_U]`.
  - **What is owed.** The Herman–Putnam–Skau fact that, for minimal `(X,T)`, a coinvariant class strictly positive
    on every invariant measure has a nonnegative representative. Fetching HPS (Internat. J. Math. 3, 1992) and GPS
    (J. reine angew. Math. 469, 1995) on MSI failed (paywall, empty response).
- **(c) Giordano–Putnam–Skau.** Their verbatim statement is still owed. The expected form: strong orbit equivalence ⟺
  isomorphism of `(K^0(X,T), K^0(X,T)^+, [1])`.
  - After Theorem G the unit is `3[1]`, so the conclusion concerns the height-3 Kakutani towers.
  - The anti-isomorphism case uses `R_X^op ≅ R_(X,T^(−1))`, whose coinvariant group and cone are unchanged.
- **Assembled target for q odd (still open):** `GL_3(R_X) ≅ GL_3(R_Y)` ⇒ `(K^0(X,T), K^0(X,T)^+, 3[1]) ≅
  (K^0(Y,T), K^0(Y,T)^+, 3[1])`. The inputs are Theorem G, Theorem K, the HPS cone and GPS. The projective version
  `S_X` also needs F-PE1/F-PE2 closed.

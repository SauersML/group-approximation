# Independent check: K(L^(⊗d)) = 0 via Farrell–Jones for Z^(d−1) with crossed-product coefficients

Lane `bh-fj-twisted-crossed-product`, 2026-09-12. This is an adversarial check of
the route that computes `K_*(L^(⊗d))` from
`leavitt-tensor-powers-are-twisted-crossed-products` (`L^(⊗d) = C ∗ Λ`,
`Λ = Z^(d−1)`, `C = L_0^(⊗(d−1)) ⊗ L`) and
`leavitt-crossed-product-coefficient-ring-is-k-trivial`.

Split of work: lane `bh-leavitt-nil-k-regularity` owns the graph nodes for the
imports and the final routes. This artifact only checks the chain and the
imports against their sources. It authors no claim, because authoring one here
would duplicate that lane's nodes.

All quotations below were extracted on MSI from the arXiv e-print TeX sources,
under `/scratch.global/sauer354/fj-cp/tex/`.

## 1. The chain

1. `L^(⊗d) = C ∗ Λ` is a crossed product with a unit in every graded piece.
   Main: `leavitt-tensor-powers-are-twisted-crossed-products`.
2. `K_n(C) = 0` for all `n ∈ Z`, and `C[t_1, ..., t_p]` is regular coherent for
   all `p`. Main: `leavitt-crossed-product-coefficient-ring-is-k-trivial`.
3. **FJC with additive coefficients for `Λ`, all `n`.** Bartels–Farrell–Lück
   arXiv:1101.0469 (§2).
4. **Crossed products as additive `G`-categories.** Bartels–Reich
   arXiv:math/0510602 (§2).
5. **Nil vanishing for twisted Laurent categories.** Bartels–Lück
   arXiv:2002.03412 (§2).
6. **Vanishing of the source of the assembly map** (§3).

## 2. Imports, quoted from source

**Step 3.** Source: Bartels–Farrell–Lück, arXiv:1101.0469, `main.tex`, lines 389–399.

> Theorem (Virtually poly-Z-groups). Let G be a virtually poly-Z-group. Then
> both the K-theoretic and the L-theoretic Farrell-Jones Conjecture with
> additive categories as coefficients with respect to the family VCyc [...]
> hold for G.

The definition it refers to is at lines 555–569:

> [...] if for any additive G-category A the assembly map
> asmb_n^{G,A}: H_n^G(E_F(G); K_A) → H_n^G(pt; K_A) = K_n(∫_G A)
> induced by the projection E_F(G) → pt is bijective for all n ∈ Z.

`Λ = Z^(d−1)` is poly-Z (Definition `def:virtually_poly-Z`, lines 3708–3717).

**Step 4.** Source: Bartels–Reich, arXiv:math/0510602.
- Corollary `cor:crossed-product-in-category-language` (lines 1596–1616):

  > Suppose we are given a crossed product situation R, α: G → Aut(R),
  > τ: G × G → R^×. Then there exists an additive category A_{α,τ} with a
  > right G-action, such that for every orbit G/H the category A_{α,τ} ∗_G G/H
  > and the category F^f(R_{α|,τ|} H) of finitely generated R_{α|,τ|} H-modules
  > are equivalent. [...] In particular there is for every G/H and every
  > n ∈ Z an isomorphism K_n(A_{α,τ} ∗_G G/H) ≅ K_n(R_{α|,τ|} H).

- Proposition `prop:crossed-products-and-categories` (lines 1343–1348):
  `A_{α,τ} ∗_G pt` is equivalent to the category of finitely generated free
  `R_{α,τ}G`-modules.
- Conjecture `con:FJ-for-crossed-product` (lines 1639–1646): the crossed-product
  form of the assembly isomorphism, `H^G_*(E_VCyc G; K_{A_{α,τ}}) → K_*(R_{α,τ}G)`.
  For `G = Λ` it is the `A = A_{α,τ}` instance of step 3.

**Step 5.** Source: Bartels–Lück, arXiv:2002.03412, Theorem
`the:The_non_connective_K-theory_of_additive_categories` (lines 2748–2760).

> Let A be an additive category. Suppose that A[Z^m] is regular coherent for
> every m ≥ 0. Consider any automorphism Φ: A → A of additive categories.
> Then we get a weak homotopy equivalence of non-connective spectra
> a^∞: T_{K^∞(Φ^{-1})} → K^∞(A_Φ[t,t^{-1}]).

The regularity notion is Definition `def:Regularity_properties_of_additive_categories`,
lines 1736–1738: "every finitely presented ZA-module M is of type FP".

**A warning in the same source (lines 3631–3632).**

> To our knowledge it is an open problem, whether for a regular coherent ring R
> the rings R[t] or R[t,t^{-1}] are regular coherent again.

So the hypothesis of step 5 is not automatic from regular coherence of `C`. It
needs the polynomial statement of main's Lemma 3.1(2), that `C` is regular
*super*coherent, plus the Laurent upgrade (A) below.

**Ring translation.** Source: Lück–Steimle, arXiv:1309.1353.
- Example, lines 535–541: for a ring `R` with automorphism `φ` and induced `Φ` on
  `R_⊕`, "`R_Φ[t,t^{-1}]` is equivalent to the category of finitely generated
  free modules over the twisted group ring `R_φ[t,t^{-1}]`".
- Theorem `the:Passage_to_the_idempotent_completion`, lines 815–831: the map
  `K^∞(A) → K^∞(Idem(A))` is a weak homotopy equivalence. So `K^∞` of free
  modules is the nonconnective `K`-theory of the ring.

## 3. Checks of the steps the imports do not state

**(A) Laurent coefficients are regular coherent.** Bartels–Lück need
`A[Z^m]` regular coherent for every `m >= 0`. For `A = C_⊕`, this is
`C[Z^m]_⊕`, so they need `C[t_1^(±1), ..., t_m^(±1)]` regular coherent. Main
states only the polynomial case. The Laurent case follows as below.
- `S` = the monomials in `t_1, ..., t_m`, a central multiplicative set of
  non-zero-divisors in `P = C[t_1, ..., t_m]`, with `S^(−1)P = C[Z^m]`.
- **Every finitely presented module comes from `P`.** Take a finitely presented
  `C[Z^m]`-module `M` with presentation matrix `X`. Multiplying each row of `X`
  by a monomial, which is a unit of `C[Z^m]`, changes neither the image nor the
  cokernel. So `X` may be taken with entries in `P`, and then `M = S^(−1)N` with
  `N = coker_P(X)` finitely presented over `P`.
- **Resolutions pass through localization.** `N` has a finite resolution by
  finitely generated projective `P`-modules, since `P` is regular coherent.
  `S^(−1)(−) = C[Z^m] ⊗_P (−)` is exact because the localization is central Ore,
  hence flat, and it sends finitely generated projectives to finitely generated
  projectives. So `M` is of type `FP`.
- **Both sides.** The involution of `L` preserves `L_0`, so `C` has an
  involution. Extended by `t_i ↦ t_i^(−1)`, it makes the right-module statement
  follow from the left one.

**(B) The cyclic pieces carry no hidden cocycle.** For `H = Zh ≤ Λ`, the ring
`C_(α|, τ|) H` is the `H`-graded subring `⊕_(n ∈ Z) A_(nh + Z e_d)` of
`L^(⊗d)`. It does not depend on the chosen section `λ ↦ u^λ`. With
`t = u^h` it is a skew Laurent ring `C_φ[t, t^(−1)]`, `φ = Ad(t)|_C`, because
`t^n` is a unit of degree `nh`.

The restricted cocycle for the product section, for example
`ω(h, h) ≠ 1` for `h = e_1 − e_3`, only reparametrizes the same ring. Changing
the section to `n ↦ t^n` does not change the ring or its module category.

**(C) The assembly source vanishes.** Every virtually cyclic subgroup of the
torsion-free group `Λ` is trivial or infinite cyclic. For the orbit `Λ/H`:
- `H = 1`: `K_q(C) = 0` for all `q ∈ Z`, from step 2;
- `H ≅ Z`: `K_q(C_φ[t, t^(−1)]) = 0` for all `q ∈ Z`, from (A), (B) and step 5,
  because the mapping torus of `K^∞(φ^(−1))` on `K^∞(C_⊕) ≃ 0` is contractible.

`H^Λ_*(E_VCyc Λ; K_A)` is built cell by cell from `Λ/H × D^p` with `H ∈ VCyc`.
It vanishes by induction over skeleta, using the five lemma and the fact that
`π_*` commutes with the skeletal colimit. By step 3 the assembly map is
bijective, so `K_n(L^(⊗d)) = 0` for every `n ∈ Z`, over every field `k`.

**(D) Negative degrees are not circular.** Step 2(3) uses nonconnective `K`-theory
commuting with filtered colimits, Morita invariance, and Ara–Cortiñas
Proposition 6.2 in all degrees. It does not use the conclusion.

## 4. Verdict and consumers

**Ring versus category regularity.** Bartels–Lück, arXiv:2002.03412, Corollary
`cor:regualiyt_for_R-versus_underline(r)_oplus` (lines 2060–2090): for a ring
`R`, "The ring R is [...] regular coherent" is equivalent to "The additive
category R_⊕ is [...] regular coherent", and to the same for `Idem(R_⊕)`.
- With (A), this gives the hypothesis of step 5 for `A = C_⊕`, since
  `C_⊕[Z^m] ≃ C[Z^m]_⊕` by the Lück–Steimle example with trivial twist.
- `φ = Ad(t)|_C` is a ring automorphism of `C` (main's Lemma 2.1(2)). Applied
  entrywise to matrices it induces a strict automorphism `Φ` of `C_⊕`.

**Group-action convention.** Bartels–Reich use additive categories with a
*right* `G`-action (math/0510602, lines 493, 502 and 575), and the corollary of
step 4 produces one. The matching convention in Bartels–Farrell–Lück's §2
review was grepped separately (§5 below).

**Main's two crossed-product claims, re-read line by line here.**
- **Lemma 2.1.** Every `v ∈ Z^d` is uniquely `λ + c e_d`. The unit `u^λ` has
  degree `λ`, and conjugation by a homogeneous unit preserves degrees. Nothing
  is missing.
- **Lemma 3.1(1).** `L` is hereditary. `C` is a directed union of `M_N(L)`
  along free extensions, and a finitely generated left ideal is extended from a
  stage by flatness. Nothing is missing.
- **Lemma 3.1(2).** `L[t_1, ..., t_p]` is regular coherent (Ara–Cortiñas
  Lemma 6.1, as imported on main), and so is every matrix ring over it. The flat
  filtered colimit argument is sound.
- **Lemma 3.1(3).** Nonconnective `K`-theory commutes with filtered colimits
  and is Morita invariant, and Ara–Cortiñas Proposition 6.2 holds over every
  field. Nothing is missing.

**Verdict: PASS, no gap found.** For every field `k` and every `d >= 1`,
`K_n(L_k(1,2)^(⊗d)) = 0` for all `n ∈ Z` follows from:
- main's two established claims;
- the four imports, as quoted;
- step (A), proved here.

This is an internal check, not a refereed one. Nothing here is in Lean.

**What establishing the claims would fire, checked on main at 933b7aa5e.**
- **Characteristic two.** `leavitt-tensor-powers-have-trivial-k-theory` feeds
  `char-two-linear-groups-via-leavitt-tensor-powers`. Its other three premises
  are established:
  - `leavitt-tensor-hosts-acyclic-steinberg-and-fp`;
  - `central-simple-leavitt-tensor-unit-groups-are-simple`;
  - `char-two-surface-linear-groups-satisfy-boone-higman`.

  So it would establish `char-two-linear-groups-satisfy-boone-higman`.
- **Every prime.** `prime-field-leavitt-tensor-powers-have-trivial-k-theory`
  feeds `leavitt-power-projective-e-fp-from-trivial-k-theory`, together with
  `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` (established). The
  chain continues:
  1. `leavitt-power-projective-elementary-groups-finitely-presented`;
  2. then `positive-char-linear-groups-via-leavitt-projective-elementary`, with
     `char-p-linear-groups-embed-in-projective-leavitt-power-e-groups`
     (established);
  3. then `positive-char-linear-groups-satisfy-boone-higman`.
- **Conditions on those roots.** Both would stay conditional on the imported
  criteria of Khanh, arXiv:2609.08428, which is unrefereed. The surrounding host
  and embedding claims already say so. `boone-higman-conjecture` itself is not
  touched.

## 5. Loose ends

- **BFL's convention.** Bartels–Farrell–Lück §2 reviews the conjecture with
  additive categories as coefficients. The versions they consider are those of
  `\cite{Bartels-Reich(2007coeff)}` (1101.0469, line 619), that is, Bartels–Reich
  math/0510602. So step 3's "additive G-category" is the notion step 4 produces.
  BFL's own definition text was not re-read beyond that citation.
- **Not re-read from source.** Ara–Cortiñas Lemma 6.1 was not re-read here; it
  is used as main's import node quotes it.

# Review: coherence, regularity and Nil vanishing in the Leavitt tensor K-theory proof

Lane `bh-charp-laurent-coherence-review`, 2026-09-12. This is an adversarial review of Step 3 of
route `leavitt-tensor-powers-k-vanishing-via-farrell-jones-proof` (2b19d1c07), and of the
coefficient-ring claim it uses (cbc0cacb1). The Farrell–Jones half was reviewed separately by lane
`bh-fj-twisted-crossed-product`, which gave PASS in
`research/artifacts/leavitt-fj-crossed-product-check-2026-09-12.md` (984a4a48a).

## Verdict

**PASS** for Step 3. No graph change is needed. The suspected gap is not there:
- The Nil-vanishing theorem needs regular coherence only of the **untwisted** Laurent extensions
  `C[Z^m]`.
- Those follow from regular supercoherence of `C` by central localization.
- The twisted ring `C_φ[t, t^−1]`, which can fail to be coherent (it does at `d = 2`), is never
  required to be coherent.

## 1. What the Nil theorem actually assumes

Read from the arXiv e-print TeX of Bartels–Lück, arXiv:2002.03412 (`main.tex` on MSI,
`/scratch.global/sauer354/nilk/src/2002.03412`).

- **Theorem** `the:The_non_connective_K-theory_of_additive_categories` (lines 2748–2760): "Let A be
  an additive category. Suppose that A[Z^m] is regular coherent for every m ≥ 0. Consider any
  automorphism Φ: A → A of additive categories. Then we get a weak homotopy equivalence of
  non-connective spectra a^∞ : T_{K^∞(Φ^{−1})} → K^∞(A_Φ[t,t^{−1}])."
- **The Laurent categories** (lines 2682–2685): "A[Z^m] := A[Z^{m−1}]_id[t,t^{−1}], where
  A[Z^{m−1}]_id[t,t^{−1}] is the (untwisted) finite Laurent category associated to A[Z^{m−1}] and the
  automorphism given by the identity."
- **Regular coherent, rings** (lines 1675–1677): "every finitely presented R-module M is of type FP".
- **Regular coherent, additive categories** (lines 1737–1739): "every finitely presented ZA-module M
  is of type FP".
- **Corollary** `cor:regualiyt_for_R-versus_underline(r)_oplus)` (lines 2061–2084): R is regular
  coherent iff `R_⊕` is, iff `Idem(R_⊕)` is.
- **Remark** `rem:regular_versus_regular_coherent` (lines 3629–3633): "To our knowledge it is an
  open problem, whether for a regular coherent ring R the rings R[t] or R[t,t^{−1}] are regular
  coherent again."

**Consequences.**
1. The hypothesis concerns only the untwisted iterated Laurent categories. The automorphism `Φ` is
   arbitrary and imposes no coherence condition on `A_Φ[t, t^−1]`.
2. By the Remark, `C[Z^m]` regular coherent does **not** follow from `C` regular coherent alone. It
   has to come from somewhere. Here it comes from regular *super*coherence of `C` (Section 2).

## 2. Regular supercoherence of C, and the Laurent extensions

**Definition used.** Ara–Brustenga–Cortiñas, arXiv:0903.0056 (`yaoseq6.tex`, lines 1174–1199).
- "R is regular coherent if it is coherent and in addition any finitely presented module has finite
  projective dimension."
- "The ring R is called supercoherent in case all polynomial rings R[t_1,…,t_p] are coherent."
- Via Vogel-regularity: "R[t_1, …, t_p] is regular for every p in case R is regular supercoherent."
- "any flat universal localization R → RΣ^{−1} of a regular (super)coherent ring is also regular
  (super)coherent ... In particular all the rings R[t_1,t_1^{−1},…,t_p,t_p^{−1}] are regular
  supercoherent if R is regular supercoherent."

For coherent rings, "finite projective dimension for f.p. modules" and Bartels–Lück's "type FP"
agree: syzygies of f.p. modules are f.p., so a finite projective dimension gives a finite resolution
by f.g. projectives.

**Checking `leavitt-crossed-product-coefficient-ring-proof`, Step 2.**
- **The colimit.** `C = colim_m M_(N_m)(L)` along `a ↦ a ⊗ 1_(2^(d−1))`.
  - `L_0` is the union of the matrix-unit spans `x_μ y_ν`, `|μ| = |ν| = m`, and appending a letter
    is the diagonal map. So `L_0^(⊗(d−1)) ⊗ L = colim M_(2^(m(d−1)))(k) ⊗ L`.
  - `M_(2N)(R)` over `M_N(R)` via `diag(a,a)` is free of rank 4 on both sides.
  - The colimit is therefore flat over every stage, on both sides. Confirmed.
- **L is regular supercoherent.** This is Ara–Cortiñas arXiv:1108.0352 Lemma 6.1, imported in
  `ara-cortinas-leavitt-tensor-k-theory-vanishes`. I did not re-read that PDF: pdftotext on MSI is
  broken and no copy of the source was on MSI.
  - So `L[t_1..t_p]` is regular coherent for every `p`, by the ABC definition quoted above.
  - Morita invariance then gives each `M_N(L[t_1..t_p])`.
- **The stages pass to C[t_1..t_p].** Take the colimit along free extensions.
  - A f.p. module, or a f.g. left ideal, is extended from a finite stage.
  - Flat base change preserves finite presentation and finite f.g.-projective resolutions.
  - Hence `C[t_1..t_p]` is regular coherent. Confirmed.
- **Laurent extensions (Step 3.2 of the route).** `C[Z^m] = S^(−1) C[t_1..t_m]` with `S` the central
  monomials.
  - Denominators in a presentation matrix clear by central units, so every f.p. module is induced.
  - Central localization is flat.
  - Hence `C[Z^m]` is regular coherent. Confirmed. This independently matches the ABC localization
    remark.
- **Sides.** The anti-automorphism `x_i ↦ y_i` of `L` preserves `L_0` and fixes the `t_i`, so
  left and right regular coherence agree. Confirmed. (Bartels–Lück use right `ZA`-modules by
  default; the symmetry covers either convention.)

**Additive-category translation.**
- `A = C_⊕` and `Φ = φ_*`.
- `A[Z^m] ≃ C[Z^m]_⊕`, by the Lück–Steimle example with `φ = id` and induction.
- By the Corollary, `A[Z^m]` is regular coherent for all `m`. So the Theorem applies to every
  automorphism `φ` of `C`.

## 3. The d = 2 test, and why the non-coherent ring does not enter

- **d = 2.** `L ⊗ L = C ∗ Z` with `C = L_0 ⊗ L` and `t = u = Σ x_i ⊗ y_i`.
  - `u` is invertible: `u (Σ y_i ⊗ x_i) = Σ x_i y_i ⊗ 1 = 1`, and symmetrically.
  - So `L ⊗ L = C_φ[t, t^−1]` with `φ = Ad(u)|_C`.
  - This ring is **not** coherent (`leavitt-tensor-powers-are-not-left-coherent`).
- **Where coherence is used.** The Theorem needs only `C[Z^m]` regular coherent, which holds
  (Section 2), and gives `K(L ⊗ L) ≃ T_(K(φ^−1)) ≃ 0`, since `K(C) ≃ 0`. This agrees with Ara–Cortiñas'
  `K_*(L_2 ⊗ L_2) = 0` and does not use coherence of `L ⊗ L`. So the d = 2 "counterexample" is
  consistent with the argument rather than against it.
- **A known analogue.** `k[Z ≀ Z] = k[Z^(∞)]_σ[t^±]`.
  - It is not coherent.
  - The untwisted `k[Z^(∞)][Z^m]` are regular coherent (colimits of Noetherian regular rings), so
    the same Theorem computes its K-theory.
  - Twisting destroys coherence without affecting Nil vanishing.
- **Higher strata (d ≥ 3).** The strata of `E_VCyc Z^(d−1)` involve only `C` (H = 1) and
  `C ∗ Zλ = C_φ[t^±]`.
  - `u^(mλ)(u^λ)^(−m)` has total degree 0 and lies in `C^×`, so the restricted crossed product is
    the skew Laurent ring on `t = u^λ` (checked).
  - `φ = Ad(u^λ)` preserves `C` because it preserves the `Z^d`-grading.
  - The intermediate rings `L^(⊗j)` for `2 ≤ j < d`, and `C ∗ Z^r` for `r ≥ 2`, are never orbit
    values. Confirmed.

## 4. Crossed-product structure (cbc0cacb1), spot check

- `L = L_k(1,2)` is strongly Z-graded, so `L^(⊗d)` is strongly Z^d-graded.
- The units `u_j` have degree `e_j − e_(j+1)`, which span `Λ = {v : Σ v_i = 0}`.
- For `g ∈ Z^d`, put `λ = (g_1, …, g_(d−1), −Σ_(i<d) g_i) ∈ Λ`. Then `A_g = A_(g−λ) u^λ` with
  `g − λ = (0,…,0,Σg)`, and `A_(0,…,0,n) = L_0 ⊗ … ⊗ L_0 ⊗ L_n`.
- Hence `L^(⊗d) = ⊕_λ C u^λ` with `C = L_0^(⊗(d−1)) ⊗ L`, and `τ` has degree 0, so `τ ∈ C^×`.
  Confirmed.

## 5. K(C) = 0

- Non-connective K-theory commutes with filtered colimits of rings and is Morita invariant.
- `K(L) = 0` by Ara–Cortiñas Proposition 6.2 with `R = k`. It is also visible from the ABC sequence,
  since `1 − N = −1` is invertible.
- Hence `K_n(C) = 0` for all `n`. Confirmed.

## 6. Caveats, and what this review did not cover

- **Imports not re-read here.**
  - Ara–Cortiñas Lemma 6.1 and Proposition 6.2 (arXiv:1108.0352), as recorded in the import node.
  - Bihler's Vogel-regularity propositions, as cited by ABC.
  - Gersten, Proposition 1.6.
- **Or-spectrum homology.** The Davis–Lück properties in Step 4 (skeletal induction, colimits) are
  standard and were not re-read.
- **Farrell–Jones with additive coefficients.** Covered by the sibling review (PASS), not by this one.
- **Downstream Boone–Higman chain.** These nodes rest on further imports, including Khanh's
  unrefereed preprint, and this lane did not review them:
  - `positive-char-linear-groups-via-leavitt-projective-elementary` requires
    `char-p-linear-groups-embed-in-projective-leavitt-power-e-groups` (PASS in review-backlog §16)
    and `leavitt-power-projective-elementary-groups-finitely-presented`. The latter is fed by
    `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`.
  - `char-two-linear-groups-via-leavitt-tensor-powers` requires `leavitt-tensor-hosts-acyclic-steinberg-and-fp`
    and `central-simple-leavitt-tensor-unit-groups-are-simple`.

  The ESTABLISHED status of the two Boone–Higman roots is only as sound as those nodes.
- **Novelty.** None claimed by the lane; not assessed here.

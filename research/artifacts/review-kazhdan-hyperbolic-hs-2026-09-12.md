# Independent review: HS stability of Kazhdan hyperbolic groups

Reviewer lane `reviewer`, 2026-09-12. This is an adversarial review of the claims that convert Hilbert–Schmidt stability of a Kazhdan hyperbolic group into a non-hyperlinear hyperbolic group, or into a persistent degree-two class:

- `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` and `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity-proof`;
- `hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class` and `hs-stable-hyperlinear-kazhdan-hyperbolic-persistent-class-proof`;
- the inputs:
  - `hs-stability-forces-nonhyperlinear-central-extension` (Dogon–Vigdorovich import);
  - `hyperlinear-flexibly-hs-stable-group-is-residually-finite`;
  - `finite-kernel-nonrf-has-central-prime-reduction`;
  - `finite-central-extension-rf-iff-virtually-splits`.

## Verdicts

| claim | verdict | trust surface |
| --- | --- | --- |
| `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` | **PASS** | Dogon–Vigdorovich main theorem (arXiv:2506.20843v2) |
| `hs-stability-forces-nonhyperlinear-central-extension` | **PASS**, numbering corrected | statement matches the v2 PDF verbatim, where it is **Theorem 1.3**; the node said Theorem 1.1 |
| `hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class` | **PASS** | inherits Dogon–Vigdorovich |
| `hyperlinear-flexibly-hs-stable-group-is-residually-finite` | **PASS** | none (Malcev) |
| `finite-kernel-nonrf-has-central-prime-reduction` | **PASS** | none |
| `finite-central-extension-rf-iff-virtually-splits` | **PASS** | none (folklore, proof checked) |

**Bottom line.** Flexible HS stability of one hyperbolic Kazhdan group with `b_2 >= 1` would give a non-hyperlinear hyperbolic group, which is nonsofic and not residually finite. If that group is also hyperlinear, the same premise forces a persistent prime class in `H^2` of a finite-index subgroup, so the group is not good. Every step checks. The notion of stability matches the source: Dogon–Vigdorovich define "Hilbert–Schmidt stable" as the flexible notion (`D_n >= d_n`), and they call `D_n = d_n` "strictly Hilbert–Schmidt stable". So the premise these claims need is the weaker, flexible one, consistent with Becker–Lubotzky's exclusion of strict stability for infinite hyperlinear Kazhdan groups.

## 2. Source check: Dogon–Vigdorovich arXiv:2506.20843v2

The PDF was fetched on 2026-09-12 and extracted on MSI with ghostscript `txtwrite`. The arXiv listing shows v1 and v2, and the PDF header reads "arXiv:2506.20843v2 [math.GR]". Ligatures lost in extraction have been restored below.

- **Theorem 1.3.** "Let Γ be a group with property (T;FD). Assume Γ has a central extension of the form 1 → Z → Γ̃ → Γ → 1 where Γ̃ is a group with finite abelianization. If Γ is Hilbert–Schmidt stable, then there exists N ∈ N such that the finite central extension 1 → Z/N → Γ̃/(N·Z) → Γ → 1 is not hyperlinear."
- **(T;FD),** immediately above: "Γ has property (T;FD) of Lubotzky–Zimmer [LZ03] if finite dimensional Γ-representations have uniform spectral gap."
- **Hilbert–Schmidt stability** (the Introduction's definition): "… for every asymptotic representation π_n : Γ → U(d_n), there exists a sequence D_n ≥ d_n and a sequence of honest representations ρ_n : Γ → U(D_n) such that d_2(π_n, ρ_n) → 0. If D_n can be chosen to be d_n, we say Γ is strictly Hilbert–Schmidt stable." Their footnote: "In the literature, the definition we gave for stability is usually referred to as flexible stability …"

**Verdict on the import.** The graph's transcription in `hs-stability-forces-nonhyperlinear-central-extension` is verbatim and its flexible-stability note is correct. The only defect is the number. The claim's opening line and the citation route's title say "Theorem 1.1", but in the v2 PDF this is **Theorem 1.3**. The claim's own transcription note already records that 1.3 is the rendered numbering and that `thm:main-non-hyperlinear` is the TeX label. This review aligns the opening line and the route title with 1.3.

## 3. Step checks

### 3.1 `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity-proof`

1. **(T) ⟹ (T;FD).** A Kazhdan constant applies in particular to finite-dimensional representations without invariant vectors. Correct.
2. **Integral extension with finite abelianization.**
   - Hyperbolic groups have type `F_∞` (Rips complex), so `H_2(Γ;Z)` is finitely generated of rank `b_2 >= 1`.
   - Universal coefficients make `H²(Γ;Z) → Hom(H_2(Γ;Z), Z)` onto, with kernel `Ext(H_1,Z)`. Pick `c` with evaluation `φ ≠ 0`.
   - The five-term sequence of the central extension (coinvariants of a central `Z` are `Z`) is `H_2(Γ) → Z → H_1(Γ̃) → H_1(Γ) → 0`, whose first map is `±φ`.
   - The image of `Z` in `H_1(Γ̃)` is `Z/φ(H_2)`, which is finite, and `H_1(Γ)` is finite by (T). So `H_1(Γ̃)` is finite. Correct.
3. **Dogon–Vigdorovich.** Their hypotheses are (T;FD) of `Γ` (not of `Γ̃`), a central `Z`-extension `Γ̃` with finite abelianization, and flexible HS stability of `Γ`. All three are supplied. Correct application.
4. **Hyperbolicity.** A surjection with finite kernel is a quasi-isometry, and word-hyperbolicity is a quasi-isometry invariant. Correct.
5. **Nonsoficity.** Sofic ⟹ hyperlinear, and finitely generated residually finite ⟹ sofic. Correct.

### 3.2 `hyperlinear-flexibly-hs-stable-group-is-residually-finite-proof`

- **Separating approximation.** One with `‖π_n(g) − I‖_2 → √2` for `g ≠ e` exists by the tensor-power amplification of `(+) 1`.
- **"For every g" in the flexible definition.** For a finitely generated group this follows from the generator form. If `P_n ρ_n(s) P_n` is close to a unitary in normalized 2-norm, then `‖(1 − P_n) ρ_n(s) P_n‖_2 → 0`, so compressions of products are close to products of compressions.
- **Separation.** If `ρ_n(g) = I`, then `P_n ρ_n(g) P_n = I_(d_n)`, which stays at distance `√2 − o(1)` from `π_n(g)`. So `ρ_n(g) ≠ I`.
- **Conclusion.** `Γ` is maximally almost periodic, and by Malcev a finitely generated residually linear group is residually finite. Correct.

### 3.3 `finite-kernel-nonrf-has-central-prime-reduction-proof`

- **The residual sits in the center of the kernel.** `R(E) <= K` because `H` is residually finite, and `R(E) <= ker(E → Aut K)` because that kernel has finite index. So `R <= Z(K)`.
- **Isolating `R`.** `L = ker f ∩ ker c`, with `f` detecting the finite set `K \ R`, gives `L ∩ K = R <= Z(L)`, and `R(L) = R` by finite-index heredity.
- **The prime quotient.** Take `B < R` maximal, so `R/B ≅ C_p`, and `B` is normal in `L` because it is central. `R(L/B) = R/B`: if `x ∈ ∩_N NB` over finite-index normal `N`, finiteness of `B` gives one `b` with `x b⁻¹ ∈ N` for cofinally many `N`, so `x ∈ R(L)B`. Correct.

### 3.4 `finite-central-extension-rf-iff-virtually-splits-proof`

- **(1 ⟹ 3).** A finite-index normal subgroup `L` avoiding the finite kernel maps isomorphically onto a finite-index subgroup, which gives a section.
- **(3 ⟹ 1).** The normal core of the section's image still meets the central kernel trivially.
- **Profinite half.** The pullback of a profinite extension is a subgroup of a residually finite product.
All correct.

### 3.5 `hs-stable-hyperlinear-kazhdan-hyperbolic-persistent-class-proof`

- **Steps 1–4** chain the four inputs with matching hypotheses. `H_0` has finite index, so it is residually finite and hyperbolic.
- **Step 5, not good.** Continuous cohomology of `Γ̂` with finite coefficients is the direct limit over finite quotients. Any class in the image of `H²(Γ̂; C_p) → H²(Γ; C_p)` therefore dies on some finite-index subgroup. Goodness makes that map onto, so `α`, which dies on no finite-index subgroup, witnesses that `H_0` is not good. Goodness passes to finite-index subgroups. Correct.

### 3.6 Known-case tests

- **`Sp_(2g)(Z)`, `g >= 2`.** It is Kazhdan but not hyperbolic, and it carries Deligne's non-residually-finite central extension from a persistent class. That is the same shape as 3.3–3.5, so the criterion behaves as expected on the one classical example.
- **Currently settled hyperbolic Kazhdan groups.** None is known to be flexibly HS-stable, and the claims are conditional on that premise, so there is no conflict with known results.

## 4. Not verified

- The proof of Dogon–Vigdorovich Theorem 1.3 (their Sections 3–4), a published preprint that was not re-derived.
- Whether any explicit hyperbolic Kazhdan group with `b_2 >= 1` is flexibly HS-stable. That is the open premise, and the lanes own it.

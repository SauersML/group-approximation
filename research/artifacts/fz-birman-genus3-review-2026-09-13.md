# Review: genus-3 Birman sequence does not virtually split (fz wave 3)

Lane `b3-verify`, 2026-09-13. Verification only. No Cairn node was edited.

**Under review:**
- **Claim and route.** Claim `birman-sequence-genus-three-does-not-virtually-split`; route `birman-genus-three-no-virtual-splitting-proof`.
- **Artifact.** `research/artifacts/bh-birman-genus3-section-2026-09-12.md`.
- **Earlier review.** `research/artifacts/review-birman-genus3-2026-09-12.md` (PASS). I rechecked it and did not rely on it.

## Verdict: PASS

| Point | Verdict |
|---|---|
| 1. Printed question | **PASS, qualified.** Genus 3 is the unresolved case of a question printed as open. No printed sentence singles it out. |
| 2. Prior answer | **PASS.** No general genus-3 answer was found. Luo–Watanabe answer only the subgroups containing `K_3`. |
| 3. Correctness | **PASS.** Every step of the adaptation checks. There are two minor imprecisions and no gap. |

## Sources read here

- **Chen–Salter, arXiv:1804.11235v1.** The whole text (785 extracted lines). Sections 2.15 to 3 were reread for this review.
- **Chen–Salter, published form.** Author PDF (dated September 3, 2019; Math. Res. Lett. 28(2), 383–413). I read §1 (lines 1–165) and grepped the rest.
- **L. Chen, arXiv:1710.00786v2** (October 9, 2017). The abstract and §1.
- **Luo–Watanabe, arXiv:2502.14343v2** (v1 February 20, 2025; v2 April 21, 2025). §1 and the acknowledgement; the rest grepped.
- **Salter–Tshishiku, Notices AMS, February 2020.** Author PDF (dated October 21, 2019). The passage on sections of tautological bundles; the rest grepped.
- **Citers.** Every citer of Chen–Salter listed by Semantic Scholar (9 papers), grepped for their uses of it. The texts are on MSI in `/scratch.global/sauer354/bh-outfn-mcg`.

## 1. Printed question

- **Chen 2017** (arXiv:1710.00786v2, §1) poses the question as open, in every genus.
  - "We pose the following open question".
  - Problem 1.4: "Does the Birman exact sequence for a finite index subgroup of Mod(Sg) always not split?"
- **Chen–Salter** (both versions):
  - print Question 1.1 for arbitrary subgroups;
  - show that genus 2 virtually splits (Weierstrass points);
  - prove "For g≥ 4, the Birman exact sequence does not virtually split."

  Neither version has a sentence about genus 3. Grepping for g = 3, g > 3, genus 3 and genus three finds only the g ≥ 4 anchors.
- **Salter–Tshishiku.** The survey says "no continuous multisection exists for g≥ 4". It gives the genus-2 multisection from Weierstrass points and does not mention genus 3.
- **Luo–Watanabe** cite Chen–Salter "when g≥ 4" and put genus three in their title. They prove only the case containing `K_3`: "Our results partially extend theirs in certain specific cases".

So from 2018 on, genus 3 is the only genus in which Problem 1.4 is unresolved in print. The question itself is printed as open; the genus-3 case is what is left of it, not a sentence of its own.

**Do not cite** Chen 2017, Remark 1.2 ("The case g = 3 is open."). That remark is about the Birman sequence for the Torelli group `I_3` itself. `I_3` has infinite index in `Mod(Σ_3)`, so the repo claim neither implies that statement nor follows from it. The claim's scope correctly leaves the Torelli level out.

## 2. Prior answer

- **Luo–Watanabe, Theorem 1.**
  - **What it proves.** For a finite-index `Γ ≤ Mod(Σ_g)` "containing Kg", with g ≥ 3, the profinite sequence does not split, and so the discrete one does not either. In genus 3 this covers only subgroups containing the Johnson kernel `K_3`.
  - **Why it does not give the general case.** `Mod(Σ_3)` is residually finite and `K_3 ≠ 1`. So for any `1 ≠ k ∈ K_3`, some finite-index normal subgroup omits `k`, and that subgroup does not contain `K_3`. The authors say themselves that they extend Chen–Salter only in specific cases.
  - **Their other results.** Theorem 2 and Corollary 3 are about graded Lie algebras and Sp-equivariant sections for Torelli, which are different objects.
- **Citers of Chen–Salter** (Semantic Scholar, 9 papers):
  - the list: 1710.00786, 1807.10171, 2001.03227, 2011.05792, 2101.03824, 2407.03248, 2412.07319, the Salter–Tshishiku survey, and 2502.14343;
  - only Luo–Watanabe treat genus 3;
  - the others cite Chen–Salter for g ≥ 4 or generally (2407.03248: "does not even virtually split"; 2011.05792 and 1807.10171: on sections), for terminology (2101.03824), or for their Proposition 2.8 (2412.07319);
  - the 1710.00786 text read is v2, which predates Chen–Salter. Its published form was not read.
- **Citers of Luo–Watanabe** (Semantic Scholar): none.
- **Web search** (five queries, 2026-09-13): nothing beyond Luo–Watanabe.
- **Not searched:**
  - the arXiv API listings: HTTP 429 from both the local host and MSI (the 09-12 review ran an arXiv title search, which found nothing);
  - MathSciNet, zbMATH and Google Scholar;
  - journal literature after 2025.

**Credit wording.** "The genus-3 case of Chen's Problem 1.4, left open by Chen–Salter's Theorem A (g ≥ 4). It extends Luo–Watanabe's Theorem 1, which covers subgroups containing `K_3`, to all finite-index subgroups, by adapting Chen–Salter's proof."

## 3. Correctness

Checked independently against Chen–Salter v1, using v1's numbering. The published version renumbers, for example Corollary 3.4 becomes 3.5.

**Setting, (F) and (R).** Valid.
- **σ.** σ is injective, since `p∘σ = id`.
- **(F).** One representative computes both restrictions. This holds even when doubled curves cobound the punctured annulus `P`, because `P` becomes an annulus once `∗` is forgotten.
- **Pants decompositions.** A pants decomposition of `Σ_3` through a bounding pair (2+2+2 curves), or through a curve bounding a torus (1+4+1), has 6 curves.
- **Centralizer bound.** On a finite-index subgroup, the centralizer maps to the product of the component mapping class groups.
  - The kernel is generated by the twists about `M̃`, so it has rank `≤ |M̃|`.
  - The image is virtually cyclic on each pA component and trivial on pants.
  - So the rank is `≤ |M̃| + j`.

**Lemma A (bounding pairs; replaces Lemma 2.9(1), G1).** Valid.
- **Step 1, Case 2.** It uses a crossing curve `δ ⊂ S_i`, which commutes with `x`.
  - A power of `σ(T_δ^r)` fixes `γ'`.
  - Applying `p` gives `T_δ^{rN}(γ) = γ` although `i(δ, γ) ≠ 0`. Contradiction.
- **Step 2.**
  - **Empty CRS.** `σ(x^k)` is pA, and its virtually cyclic centralizer would contain `Z^6`.
  - **CRS made of lifts of `b`.**
    - If `σ(x^k)` is the identity on `C`, then `x^{kN} = T_b^j`, which is false.
    - If it is pA on `C ≅ Σ_{2,2}` (possibly with `∗`), the rank is `≤ 3 < 6`.
- **Step 3.** McCarthy gives `ψ^j = φ^i`. `forget_∗` sends `φ` to `ρ_S(x^k) = 1` and `ψ` to `T_δ^r`, which has infinite order in `Mod(S^)`. That is a contradiction, also when `i = 0`. This step avoids Claim 2.12, which needs the separating-twist case (G7).

**Lemma B (separating twists; G2).** Valid.
- Every essential separating curve of `Σ_3` bounds a one-holed torus.
- `T = Σ_{1,1}` and `R = Σ_{2,1}` both contain a nonperipheral `δ`, and the pants `P` has no pA.

**Lemma C (single lift; replaces Lemmas 2.15–2.16, G3).** Valid.
- **Restrictions.**
  - `ρ_T̃(σ(h)) = ρ_T(h) = 1` by (F), and `ρ_P = 1` since `P` is a thrice-punctured sphere.
  - The cutting kernel is `⟨T_{c_T}, T_{c_R}⟩`, and `T_{c_R} ∈ Mod(R̃)`.
  - So `σ(D'') ⊆ Mod(R̃)·⟨T_{c_T}⟩`.
- **The product is direct.** The supports are disjoint. For `n ≠ 0`, `T_{c_T}^n` moves a curve in `T̃ ∪ P` that crosses `c_T`, while `Mod(R̃)` fixes that curve.
  - So `ν: D'' → Z` is a homomorphism.
  - `ν(T_c^M) ≠ 0`, where `M` is a multiple of `k` with `T_c^M ∈ D''`.
- **The contradiction.**
  - `D''` is a central extension of a finite-index `Q ≤ π1(Σ_2)`.
  - Its rational Euler class is a nonzero multiple of the restriction of `e(UT Σ_2)`. That restriction is nonzero because `χ(Σ_2) = −2` and restricting to a finite-index subgroup is injective on `H^2(−;Q)`.
  - By the five-term sequence `H_2(Q;Q) → H_1(center;Q) → H_1(D'';Q)`, the center vanishes rationally, so `ν(T_c^M) = 0`.

  This is Chen–Salter's `b_1` criterion from their proof of Lemma 2.15, applied to one side only.

**Lemma D (placing the marked point; G4).** Valid.
- Commuting lifts are disjoint (Prop 2.4).
- Take an essential separating curve of `T̃_1 ≅ Σ_{1,1}` (with or without `∗`). After forgetting `∗` it is parallel to `c̃_1`. So `c̃_2 ⊂ R̃_1` and `c̃_1 ⊂ R̃_2`.
- `T̃_1` is connected, misses `c̃_2`, and meets `R̃_2` near `c̃_1`. So `T̃_1 ⊂ R̃_2`, and `T̃_1 ∩ T̃_2 = ∅`.
- So `∗` lies in some `R̃_i`.

The artifact's "no nesting of tori" line is terse; the argument above is the full version.

**Section 3 with p = 2, q = 1 (G4, G5, G6).** Valid.
- **Support.** `σ(Mod(R) ∩ L)` is supported on `R̃`. This follows from (F) and the cutting kernel `⟨T_{c̃}⟩ ⊂ Mod(R̃)`.
- **Diagram (6) and Lemma 3.1, in Mod instead of Torelli.** `σ(H) ⊆ PB_{1,1}(Σ_2)`, because capping after `p∘σ` equals capping on `H`. Lemma 3.1 needs `σ(T_c^k) = T_{c̃}^k`, which is Lemma C.
- **Lemma 3.2.**
  - **Nonseparating `α`.** The push is a genus-(1,1) bounding pair forming pants with `c`, so Lemma A gives (10)–(11).
  - **Separating `α`.** `α_L` and `α_R` bound one-holed tori in `R`. Lemma C gives single lifts, and after capping `c̃` they cobound an annulus.
  - **Sign.** The artifact writes `s(α^k) ∈ {1, α^{±k}}`. Tracking the sides gives `α^k`. Lemma 3.3 needs only some exponent, so nothing changes.
- **Lemma 3.3 and Corollary 3.4.** The proof conjugates within one curve type, and uses root uniqueness and commensurability in `π1(Σ_p)`. It holds for p = 2, within each type and for mixed pairs.
- **Lemmas 3.5–3.8** are arguments in `π1(Σ_2)`.
  - Lemma 3.7 uses only that the forgetful square commutes, which holds in Mod.
  - The last step of Lemma 3.6 ("Since p≥ 2") holds for p = 2.
- **§3.4.** Write `d` for the degree of the finite cover corresponding to `H̄`.
  - Case (A) gives `χ(Σ_2)·d·[H̄] ≠ 0`.
  - Case (B) gives `i^*[Σ_2] = d·[H̄] ≠ 0`.
  - v1 prints `χ(Σp)[H]` in Case (B) too, where the coefficient should be the degree. It is nonzero either way.

**The written gap in Chen–Salter, confirmed.** Lemma 3.2 covers only nonseparating `α`, but (15) applies Corollary 3.4(B) to `γ_i` conjugate to a separating `d`. Genus 3 has two independent repairs:
- **Lemma C**, as the artifact and the 09-12 review say.
- **Nonseparating `d` in Lemma 3.6**, available in the full-Mod setting.
  - Lemma 3.8 is stated for any Dehn twist.
  - `T_d^k ∈ L`, because `L` has finite index in Mod.
  - The `γ_i` are then nonseparating, and nonseparating curves fill `Σ_2`.
  - Chen–Salter needed a separating `d` only because they work inside Torelli.

**Scope.** `p∘σ = id` on a finite-index `L` is Chen–Salter's definition of virtual splitting (their footnote 1). The genus-3 Torelli-level statement is neither claimed nor proved: Lemma A Step 2 and Lemma B Step 2 use twists outside Torelli.

## 4. Remaining risks

- **Review and Lean.** No expert human review, and no Lean.
- **Imported, not reread:**
  - McCarthy's centralizer theorem;
  - Farb–Margalit Prop 3.20 and Thm 3.18;
  - Kra's theorem;
  - Chen–Salter Props 2.2–2.7 and Lemma 2.8.
- **Novelty search.** It is bounded; §2 lists what was not searched.
- **Stale node line.** The claim node still says "Novelty. Not searched." §2 records the search. The node is read-only for this lane.

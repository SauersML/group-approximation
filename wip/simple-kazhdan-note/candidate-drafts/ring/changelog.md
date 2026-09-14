# sk-draft-ring: changelog against main (rev1, 5b1890ce6c, md5 8e04b341…, 292 lines)

- **Draft:** `sk/drafts/sk-draft-ring/sk-draft-ring.tex`, 352 lines, md5 87372e3a….
- **Compile:** MSI pdflatex, 3 passes: 0 errors, 0 overfull boxes, 0 undefined references; 2 underfull boxes, both in bibliography entries; 4 pages.

## Architecture
- **Headline (Theorem 1).** Let R be a finitely generated simple ring with local annihilation, meaning for every finite F ⊆ R, the s with tFs = 0 for some t ≠ 0 additively span R. Let n ≥ 3.
  - Every normal subgroup of EL_n(R) is central or everything.
  - EL_n(R)/Z is infinite, f.g., simple and Kazhdan.
  - If R is a unital subring of an algebraic ultraproduct of finite rings, then EL_n(R) is LEF, and so is EL_n(R)/Z when Z(R) is finite.
- **Example (Theorem 2).** R_X = LC(X,F_q)⋊Z satisfies all hypotheses for every finite field F_q, and Z(R_X) = F_q. So EL_n(R_X)/Z is infinite, f.g., simple, Kazhdan and LEF for every n ≥ 3. Over F_2 the group G_X itself has these properties.

## Section map (draft lines vs rev1 lines)
| Part | Draft | rev1 | Δ |
|---|---|---|---|
| Front matter, abstract, intro, theorems, credit | 1–95 (95) | 1–71 (71) | +24 |
| Criterion, LEF lemma, proof of Theorem 1 (§1) | 96–184 (89) | — | |
| Subshift algebras (§2) | 185–252 (68) | — | |
| Proof machinery total | 157 | 72–187 (116) | +41 |
| Word problems, origin, bibliography | 253–352 (100) | 188–292 (105) | −5 |
| **Total** | **352** | **292** | **+60 (+21%)** |

Inside the machinery:
- **Simplicity.**
  - rev1: 52 lines, the constant tower.
  - Draft: 67 lines: Lemma (criterion) 38, ring simplicity and centre 20, local annihilation for R_X 9.
- **LEF.**
  - rev1: 30 lines.
  - Draft: 44 lines: definition and the Pestov sentence, Lemma (ultraproduct plus finite central quotient) 17, finite models by ultraproduct embedding 27.

## Text changes
1. Abstract: the ring theorem first, then the subshift example, the answer, and Turing degrees.
2. New definition of local annihilation, and the notation Z_n(R).
3. Theorem 1 is new, as above.
4. Theorem 2 replaces rev1's Theorem. It adds every F_q and every n ≥ 3 modulo the centre; G_X over F_2 stays.
5. Credit paragraph:
   - Removed: "The new step is simplicity. … clopen tower …" and the Matui sentence, since the tower pattern is not used here.
   - Added: "The extraction of an elementary matrix in Lemma 2 follows Stepanov [Lemma 4.3], and local annihilation supplies the noncentral commutators it starts from."
   - GM credit rewritten per sk-citations P1: "as in the proof by Grigorchuk and Medynets that topological full groups of minimal Cantor systems are LEF [Theorem 2.6]".
   - Added the Brown bridge: L(G) ⊆ R^ω [Ozawa, Prop. 7.1], so G ⊆ U(L(G) ⊗̄ R), a separable McDuff factor embeddable in R^ω.
   - The not-f.p. sentence is generalized to the groups of Theorem 2.
6. §1 "Normal subgroups and finite models":
   - notation, (1), generation, the scalar centre;
   - Lemma 2 (criterion), in sk-general-master's additive-span text with the index checks written out;
   - the LEF definition with Vershik–Gordon, and Pestov locators Example 4.5 and Theorem 3.3;
   - Lemma 3: EL_n over an ultraproduct subring is LEF, and so is its quotient by a finite central subgroup (finite model of FF, with ψ(Z) central in ⟨ψ(F)⟩);
   - proof of Theorem 1: (T) from EJZ; R is infinite, since for finite R the choice F = R kills every s; e_12 embeds R modulo the centre.
7. §2 "Subshift algebras":
   - conventions and uniqueness of coefficients;
   - generation (adds a generator of F_q);
   - simplicity of R_X over F_q (e_U r e_U = c e_U, translates cover X);
   - Z(R_X) = F_q (no periodic points and minimality);
   - local annihilation (W missing an orbit segment, V small, refine to a partition);
   - finite models: rev1's periodic words over F_q, assembled into a unital injective φ: R_X → ∏_ω M_{m_ℓ}(F_q).
8. §3 Word problems: unchanged from rev1, including the GMpres credit.
9. Origin paragraph: rev1 wording.
10. Bibliography: Matui removed; everything else as in rev1.
11. Removed from rev1:
    - the constant-tower simplicity section (small sets, ε_ab, ψ, transvection generation, GL_d(F_2) simplicity);
    - "We write the proof for n=3 …";
    - the \PSL macro.

## Status of each piece
- **Lemma 2 (criterion).**
  - The criterion `local-annihilation-makes-projective-el-simple` is reviewed PASS by un-verify and sk-verify-3.
  - sk-proof-minimal-conceptual's variant of this proof text passed sk-review-1 part 6.
  - The draft uses sk-general-master's additive-span variant (route `local-annihilation-el-simplicity-explicit-extraction`), which is UNREVIEWED as text. Every identity was re-derived in this lane.
- **Local annihilation for R_X:** PASS (sk-review-1 part 6 §1, "Local annihilation for R").
- **Ultraproduct embedding (lef-short Replacement A):** PASS (sk-review-1 part 2 §3). Over F_q it is the same argument.
- **Finite central quotient of a LEF group:** new text, self-verified, UNREVIEWED.
- **Simplicity of R_X and Z(R_X) = F_q over F_q:** the frozen note's F_2 argument with a scalar c; self-verified, UNREVIEWED as text.
- **Brown bridge:** sk-operator-algebras (b01d8ea1f5), queued with sk-referee-2, UNREVIEWED.
- **Stepanov Lemma 4.3 locator:** a second-hand quote (un-stepanov-credit read the Springer page images); sk-citations did not re-read it.

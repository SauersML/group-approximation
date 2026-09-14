# sk-draft-ring: a ring-level candidate note (self-assessment, 2026-09-13)

- **Lane:** sk-draft-ring, one of four competing drafters (ROSTER-D, Family P).
- **Draft:** `sk/drafts/sk-draft-ring/sk-draft-ring.tex` (scratchpad only), 352 lines, md5 87372e3a….
- **Compile:** MSI pdflatex 3 passes: 0 errors, 0 overfull boxes, 0 undefined references, 4 pages.
- **Changelog against main:** `sk/drafts/sk-draft-ring/CHANGELOG.md`.
- **Base:** main's rev1 (5b1890ce6c, 292 lines).

## The architecture
**Theorem 1 (headline).** Let R be a finitely generated simple ring with *local annihilation*: for every finite F ⊆ R, the elements s with tFs = 0 for some t ≠ 0 additively span R. Let n ≥ 3.
- Every normal subgroup of EL_n(R) is central or everything.
- EL_n(R)/Z_n(R) is infinite, f.g., simple and Kazhdan.
- If R is a unital subring of an algebraic ultraproduct of finite rings, then EL_n(R) is LEF. EL_n(R)/Z_n(R) is also LEF when Z(R) is finite.

**Theorem 2 (example).** For every infinite minimal subshift X and every finite field F_q, R_X = LC(X,F_q)⋊Z satisfies all hypotheses, and Z(R_X) = F_q. So EL_n(R_X)/Z is infinite, f.g., simple, Kazhdan and LEF for all n ≥ 3, and over F_2 the group G_X itself is.

The proof has two parts.
- **§1 is abstract.**
  - Lemma 2: the explicit two-commutator extraction ρ → v → e_bl(z·unit), then the level ideal.
  - Lemma 3: ultraproduct subrings give LEF groups, and quotients by finite central subgroups stay LEF.
- **§2 checks R_X.** Generation, simplicity, centre, local annihilation, and a unital injective φ: R_X → ∏_ω M_{m_ℓ}(F_q).

§3 (word problems) is rev1 verbatim.

## Honest length comparison
| | Draft | rev1 |
|---|---|---|
| Total | 352 | 292 (+60, +21%) |
| Intro, theorems, credit | 95 | 71 |
| Proof machinery | 157 | 116 |
| Simplicity | 67 | 52 |
| LEF | 44 | 30 |
| Word problems, origin, bibliography | 100 | 105 |

Both typeset to 4 pages.

## Strongest claim
- One theorem gives simplicity modulo centre and (T) for EL_n over every f.g. simple ring with local annihilation, over any field of coefficients that keeps R f.g.
- The subshift example then works over every finite field and every n ≥ 3. rev1 gets n ≥ 3 but only over F_2.
- The binary unit trick (LC(X,F_2)^× = {1}) is not needed. sk-referee-1 warned that this trick fails over F_q, and the criterion has no such case split.
- No simplicity of GL_d(F_2), no clopen towers, no F_q scalar case.

## Weakest point
- **The generality is not exhibited in the note.** The only ring the paper checks is R_X. Free minimal Γ-subshifts with finite models, Steinberg algebras and Leavitt algebras all satisfy the hypotheses, but proving that costs more text.
- **So +60 lines buy only every F_q plus the reusable criterion**, and reusability is claimed, not used.
- **The group-theoretic picture is lost.** rev1 lands the commutator inside one finite simple group GL_d(F_2) on a clopen tower, which parallels Matui's proof for topological full groups and the finite models. The two-commutator extraction here is algebra with no geometry.
- **The simplicity and centre of R re-enter** (20 lines). rev1 avoided them through the covering step.
- **The abstract is heavier:** it defines a hypothesis before naming the group.

## What a referee will attack
1. "Local annihilation looks ad hoc." A referee asks for examples beyond R_X and for its relation to Stepanov's condition (b). Whether local annihilation implies (b) is open (`local-annihilation-implies-stepanov-condition-b`).
2. Lemma 2 compresses three checks, each one line on paper but invisible in the text:
   - v and v^{-1} differ from I only in column l;
   - (v^{-1})_{ll} is a unit;
   - commutators with e_ij(1) move e_bl(c) to every position.
3. Lemma 3's quotient step is four lines. A referee may want the injectivity of fZ ↦ ψ(f)ψ(Z) spelled out: ψ(f') = ψ(f)ψ(z) = ψ(fz) forces f' = fz.
4. The Brown bridge (L(G)⊗̄𝓡 separable McDuff, embeddable in 𝓡^ω) is stated without proof. It is standard but unreviewed here.
5. The Stepanov locator "Lemma 4.3" rests on a second-hand quote.

## Review status
- **PASS:**
  - the criterion node `local-annihilation-makes-projective-el-simple` (un-verify, sk-verify-3);
  - sk-proof-minimal-conceptual's variant of Lemma 2's proof (sk-review-1 part 6);
  - local annihilation for R_X (sk-review-1 part 6);
  - the ultraproduct embedding (sk-review-1 part 2 §3);
  - word problems (rev1).
- **Unreviewed:**
  - Lemma 2 in the additive-span text actually used (re-derived by this lane);
  - the finite central quotient step of Lemma 3;
  - simplicity of R_X and Z(R_X) = F_q written over F_q;
  - the Brown bridge (sk-operator-algebras, queued with sk-referee-2).

## Recommendation for main
- **Do not adopt the ring headline for rev2 as it stands.** At +60 lines it does not pay for itself, because the note shows no second example.
- **The ring architecture wins only together with sk-draft-general.** Theorem 1 plus a 9-line local-annihilation check covers free minimal subshifts over any f.g. group. The RF embedding corollary then needs no second simplicity proof, and the criterion's cost is amortized.
- **Salvageable pieces for rev2 regardless:**
  - Lemma 3's finite-central-quotient sentence, if any F_q statement goes in;
  - the observation that the criterion handles F_q with no scalar case, as a pointer for the F_q remark (rev2-decisions item 23).

# sk-rfd-amalgam part 1: the comb stages are residually finite-dimensional (2026-09-14)

Lane sk-rfd-amalgam, wave 12. Plan artifact: `research/artifacts/sk-rfd-amalgam-plan-2026-09-14.md` (landed e9fce2d93a).

## 0. Verdict
- **Missing input 1 of `weakly-dense-popa-combs-exist-in-property-t-factors` is SETTLED** (established, unreviewed): claim `comb-tooth-tree-stages-are-residually-finite-dimensional`, route `comb-tooth-tree-stages-rfd-via-li-shen`.
- Content: for `U` separable unital RFD, `d ≥ 1`, `r ≥ 2`, the stage `((U ⊕ M_d) *_{C²} M_r) * C(T)` is RFD. Every finite-dimensional representation has `rank e : rank(1−e) = 1 : r−1`. A finite-dimensional representation of `U ⊕ M_d` extends iff it has that ratio.
- It is a citation-level consequence of Li–Shen's criterion. No priority is claimed for the step.
- **Still open:** missing input 2 (scheduling tail representations across stages inside the factor) and missing input 3 (exact translate relations in `M`). The Popa clause of Brown's Question 3 for property (T) factors stays OPEN.

## 1. Sources read at source (2026-09-14)
- **Q. Li and J. Shen**, Illinois J. Math. 56 (2012), no. 2, 647–659, journal PDF, pages 647–659 read in full.
  - Theorem 2 (p. 657): the RFD criterion over a finite-dimensional amalgam, quoted verbatim in `li-shen-amalgamated-rfd-criterion-citation`.
  - Proposition 2 (p. 654): the abelian-amalgam case, proved via Lemmas 2–5.
  - Lemma 6 (p. 657, Brown–Dykema Lemma 2.2): the corner reduction.
  - Example 1 (p. 650): `M_2 *_{C⊕C} M_3` with rank-one amalgam projections is not MF.
  - Remark 2 (p. 650): the Armstrong–Dykema–Exel–Li trace criterion for finite-dimensional factors.
  - Lemma 1 (p. 649): Exel–Loring Theorem 3.2, free products of RFD algebras are RFD.
- **Armstrong–Dykema–Exel–Li**, Proc. Amer. Math. Soc. 132 (2004), 2019–2030, arXiv:math/0210448. Only the abstract was read (arXiv page). The PDF was downloaded to MSI but not text-extracted (no pdftotext there); the criterion is known through Li–Shen Remark 2.
- **Exel–Loring**, Internat. J. Math. 3 (1992), 469–476. Not opened; the statement comes via Li–Shen Lemma 1.
- **Korchagin**, arXiv:1206.4970 (commutative amalgamated free products are RFD). Located, not needed.

## 2. The proof
See route `comb-tooth-tree-stages-rfd-via-li-shen`.
1. A separating sequence `ρ_n` of `U`, with the multiplicity choice `k_n = r d D_n`, gives unital embeddings `q_1: U ⊕ M_d → ∏M_{k_n}` and `q_2: M_r → ∏M_{k_n}` that agree on `C²`.
2. By Li–Shen Theorem 2, the amalgamated free product is RFD.
3. By Exel–Loring, the free product with `C(T)` stays RFD.
4. The rank ratio comes from uniqueness of the irreducible representation of `M_r`.
5. The extension lemma: choose matrix units of `M_r` with `p ↦ σ(e)`, then use the universal property.

## 3. Model tests
- Li–Shen Example 1 fails exactly where our hypothesis holds: there each factor has one irreducible representation, forcing incompatible ratios 1/2 and 1/3. `U ⊕ M_d` has two independent multiplicities.
- `U = C, d = 1, r = 2`: the stage without `C(T)` is `C² *_{C²} M_2 ≅ M_2`, which is RFD.
- `r = 1` is excluded: `C² → M_1` is not an embedding, and the tooth would be the unit.

## 4. What this means for the plan
- **Input 2** is now purely combinatorial. At stage `j`, a tail representation `σ_j` of `U_j` on the tooth `e_j` extends to `U_{j+1}` iff its `(1−e_j)`-part has dimension `r_j − 1` times its `e_j`-part. So the multiplicities on each tooth must be scheduled so that, for every later stage, the realized ranks inside `M` respect all ratios `1 : r_j − 1`.
  - Since `τ(e_j) → 0` and `r_j ≈ 1/τ(e_j)`, the natural choice is `r_j = 1/τ(e_j)` exactly, with the tooth projections of dyadic trace in `M`.
  - The consistency check is on traces of nested teeth.
- **Input 3** is unchanged.
- **Sharpest next target:** input 2. Construct inside a separable II_1 factor a nested family of projections `e_1 ≥ … ` (or disjoint teeth) with traces `1/r_j`, and unitaries `w_j` commuting with all later teeth that permute translates of `e_j`. Then check that the representations σ_j with the forced multiplicities exist and are norming.

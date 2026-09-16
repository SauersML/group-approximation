---
rg: 2
id: characters-living-on-m-plus-one-factors-meinert-citation
kind: route
title: Import Meinert's inequality from Bieri–Geoghegan and induct on the number of living factors
target: characters-living-on-m-plus-one-factors-lie-in-sigma-m
requires: []
---

Citation import, plus a short induction.

**Source.** R. Bieri and R. Geoghegan, "Sigma Invariants of Direct Products of Groups", arXiv:0808.0013v2 (v2 dated
2009-08-05). Read 2026-09-16 from the arXiv LaTeX source (`product21.tex`, SHA-256
`7eb4155df547c21c935a3ebd7254532e96b228944fdb853cf0aa14288af98e90`). The paper numbers theorems by section, so the
statement below is Theorem 1.2. The claim node lists the journal version as Groups Geom. Dyn. 4 (2010); that
reference was not re-checked here.

**Imported statement.** Theorem 1.2 ("Meinert's Inequality"), verbatim up to typesetting, homotopical half:
"Σ^n(G×H)^c ⊆ ∪_{p=0}^n Σ^p(G)^c ∗ Σ^{n−p}(H)^c".

The paper's conventions, all quoted from §1:

- "We denote the complement of any subset A of a sphere by A^c."
- "Again, we have Σ^0(G)=S(G)."
- "Σ^n(G) is only defined when G has the topological finiteness type F_n."
- Hom(G×H, ℝ) is identified with Hom(G, ℝ) ⊕ Hom(H, ℝ). For χ ∈ Hom(G, ℝ) and χ′ ∈ Hom(H, ℝ), "the notations χ+χ′
  and (χ,χ′) both describe the character (g,h) ↦ χ(g)+χ′(h)". This embeds S(G) and S(H) as subspheres of S(G×H).
- For P ⊆ S(G) and Q ⊆ S(H), the join is "P∗Q := {[χ+χ′] | [χ]∈P, [χ′]∈Q} ∪ P ∪ Q".

**Certificate boundary.** Bieri–Geoghegan state Theorem 1.2 as a theorem of H. Meinert and do not prove it. They write:
"Meinert did not publish this, but a proof can be found in [Gehrke2, Section 9]. The paper [Bieri] also contains a
proof of the homotopy version". Here [Gehrke2] is R. Gehrke, *The higher geometric invariants for groups with
sufficient commutativity*, Comm. Algebra 26 (1998), and [Bieri] is R. Bieri, *Finiteness length and connectivity length
for groups* (1999). A footnote adds that matching their formulation to Gehrke's "requires a little work": the case
where one character is zero is their Proposition 5.1 (label `extreme`, the numbering computed from the source
counters), and "The other case is a straightforward exercise." Our induction uses only that other case, where both
components are nonzero. Neither Gehrke nor Bieri 1999 was read. Only the published statement is imported.

## Derivation

Products of finitely many groups of type `F_m` have type `F_m`: the product of `K(G_i, 1)` complexes with finite
`m`-skeleta is a `K(∏ G_i, 1)` with finite `m`-skeleton. So every invariant `Σ^n` used below, with `n <= m`, is
defined.

**Statement P(j).** Let `G_1, ..., G_j` have type `F_m` and let `χ = (χ_1, ..., χ_j)` be a character of
`G_1 × ... × G_j` with every `χ_i != 0`. Then `[χ] ∈ Σ^n(G_1 × ... × G_j)` for every `n <= min(m, j − 1)`.

**Base case, j = 1.** Here `n = 0`, and `Σ^0 = S`.

**Inductive step, j >= 2.** Put `A = G_1`, `B = G_2 × ... × G_j` and `χ′ = (χ_2, ..., χ_j)`, so `χ = χ_1 + χ′`. Here
`χ_1 != 0` and `χ′ != 0`. Suppose `n <= min(m, j − 1)` and `[χ] ∉ Σ^n(A × B)`.

1. Theorem 1.2 gives some `p` in `{0, ..., n}` with `[χ] ∈ Σ^p(A)^c ∗ Σ^{n−p}(B)^c`.
2. `[χ]` is in neither `S(A)` nor `S(B)`: points of `S(A)` have zero `B`-component, points of `S(B)` have zero
   `A`-component, and both components of `χ` are nonzero.
3. By the definition of the join, `[χ] = [ψ + ψ′]` for some `[ψ] ∈ Σ^p(A)^c` and `[ψ′] ∈ Σ^{n−p}(B)^c`, so
   `χ = r(ψ + ψ′)` with `r > 0`.
4. The sum `Hom(A×B, ℝ) = Hom(A, ℝ) ⊕ Hom(B, ℝ)` is direct, so `χ_1 = rψ` and `χ′ = rψ′`. Hence
   `[χ_1] ∉ Σ^p(A)` and `[χ′] ∉ Σ^{n−p}(B)`.
5. `Σ^0(A) = S(A)` contains `[χ_1]`, so `p >= 1`.
6. Then `n − p <= n − 1 <= min(m, j − 1) − 1 <= min(m, (j − 1) − 1)`.
7. `B` is a product of `j − 1` groups of type `F_m`, and `χ′` is nonzero on each factor. So P(j − 1) gives
   `[χ′] ∈ Σ^{n−p}(B)`, contradicting step 4.

So P(j) holds for every `j`.

**Conclusion.** Take `j = k >= m + 1` and `n = m <= min(m, k − 1)`. Then P(k) is the target claim. ∎

## Consistency checks

These are not part of the proof.

- **Sharpness.** The claim node's `F_2 × F_2` example has `k = m = 2` and `[χ] ∉ Σ^2`. It shows that step 6 cannot be
  improved to allow `n = j`.
- **Products of free groups.** `F_{r_1} × ... × F_{r_k}` (all `r_i >= 2`) is the right-angled Artin group on the
  complete `k`-partite graph with parts of sizes `r_i`.
  - A character nonzero on every factor has a living vertex in every part.
  - A dead simplex `σ` meets `|σ|` parts. Its living link is the join of the nonempty living sets of the other
    `k − |σ|` parts, which is `(k − |σ| − 2)`-connected.
  - The Meier–Meinert–VanWyk living-link condition for `Σ^m` needs `(m − |σ| − 1)`-connectivity. That holds for every
    `σ` exactly when `k >= m + 1`.
  - This criterion was not re-read in this session. It is used here only as a check on the threshold `m + 1`.

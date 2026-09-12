# Swarm 2 adversarial review (2026-09-12)

Reviewer lane `swarm2-reviewer`. Each section gives one claim, the verdict
(PASS, FAIL or GAP), and the specifics. Sections are landed one at a time.

## 0. `weyl-algebra-blocks-a-universal-leavitt-host`: SCOPE ERROR, corrected forward

Priority item, flagged by `bh-leavitt-path-steinberg`.

**Finding.** The claim stated "the first Weyl algebra does not embed into
`L_K(1,2)`" for every field `K`. It was the only invalidator of
`boone-higman-via-universal-leavitt-host`, whose far end is this repository's
`F_2` host. The source proves the statement only in characteristic zero.
- **Source check.** From the arXiv:2512.09241v2 PDF, extracted on MSI with
  ghostscript txtwrite: Theorem 3.5, "Let k be a field of characteristic
  zero", and Theorem 3.7, with the same hypothesis. The proof uses
  Proposition 3.1, on Banach algebras over `R` or `C`, and a
  transcendence-degree reduction. The abstract omits the hypothesis, and the
  2026-08-17 import quoted only the abstract.
- **Counterexample to the abstract's wording in characteristic p.** On
  `F_p[t]/(t^p)`, `D = d/dt` and `T = t·` satisfy `DT - TD = 1`. Over `F_2`,
  `D = [[0,1],[0,0]]` and `T = [[0,0],[1,0]]` give `DT - TD = diag(1,-1) = 1`.
  Since `M_n(L) ≅ L` for `L = L_K(1,2)`, the Heisenberg equation is realized in
  `L_{F_p}(1,2)`. Whether `A_1(F_p)` embeds is not settled.

**Correction landed.**
- The claim is narrowed to characteristic zero.
- The citation route and the dead route are updated, together with item 5 of
  `boone-higman-conjecture`.
- A replacement invalidator that holds in every characteristic is added:
  `fixed-leavitt-hosts-cannot-be-universal-bh-containers`, with proof route
  `fixed-leavitt-hosts-not-universal-proof`. It requires only
  `binary-leavitt-unit-word-problem-decidable` and
  `complexity-bounded-host-classes-are-not-universal`.

**False establishment?** No, either before or after. The route stayed
invalidated throughout and `boone-higman-conjecture` stays OPEN; this is
confirmed by `cairn why` on MSI in the landing batch. The defect was a scope
overstatement: over `F_2` the route was dead for the wrong reason.

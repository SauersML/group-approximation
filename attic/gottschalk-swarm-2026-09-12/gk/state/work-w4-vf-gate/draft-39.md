
## 39. w7-escape-set follow-up (6b94153534)

Sources:
- Artifact `four-transvection-escape-set-2026-09-12.md` (blob `bd8af4a3`).
- The claims `four-transvection-set-escapes-depth-monotone-units` (blob `01226942`),
  `four-transvection-units-have-a-weakly-finite-symbol-image` (blob `e957dd5f`) and
  `depth-monotone-units-carry-weakly-finite-nonzero-defect` (blob `2666d2b3`).
- The entry on `ternary-leavitt-units-have-no-weakly-finite-representation` (blob `275475a0`).
- The diff against `45282c2142`, read in full: 24 insertions, 15 deletions.

**Verdict: PASS. The advisories of 36.5 are applied, and no statement changed.**
- **Advisory 1.**
  - The escape claim's Scope, the symbol claim's `distinct_from` and the first ternary entry now say `S4 ∪ {T}`.
  - The Scope adds that other five-transvection sets are not covered.
- **Advisory 2.** The symbol claim's consequence now uses the suggested obstruction wording.
- **Advisory 3.**
  - Remark 4.4 now cites Lemma 3.1 and the non-additive models of Theorems 4.1 and 4.3, and says that other
    non-additive models are undecided.
  - The defect claim's consequence cites item 4 for the algebra-level case.
- **Optional note.** The `distinct_from` entry for `unitriangular-data-cannot-assemble-corner-leavitt-families` is
  added, and it describes that node as 36.5 does.
- **Status lines.**
  - The three claims now read ESTABLISHED. They cite their routes and Sections 36.1, 36.2–36.3 and 36.3–36.4, which
    matches the route verdict lines landed at `89d646844c`.
  - The artifact header cites Section 36.

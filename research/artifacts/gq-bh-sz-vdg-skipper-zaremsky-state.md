# Skipper–Zaremsky line: consolidated state (lane bh-sz-vdg, 2026-09-19)

**Question.** Is `V_{d,r}(G)` of type `F_∞` for every finitely generated contracting self-similar `G`?
- Skipper–Zaremsky arXiv:1709.06524, TeX l.1365–1367.
- The claim node is `contracting-rover-nekrashevych-groups-are-f-infinity`, which stays **OPEN**.

## The case split (refereed)

`level-set-route-reaches-only-bounded-rover-nekrashevych-groups`: refereed PASS by bh-ref-e (18b43406c6), with its
repairs applied.
- **Zero defect.** Every element of `V_{d,r}(G)` has zero defect, since the nucleus is surjective. So the level-set,
  torsion-defect and defect-free RSG theorems reach only bounded groups.
- **Trichotomy.** Singular sets are finite, countable or continuum according to the non-identity nucleus graph:
  - (B) SCCs are single cycles or trivial, and no path joins two cycles;
  - (P) SCCs are single cycles or trivial, and some path joins two cycles;
  - (E) some SCC is not a single cycle.

  These are bounded, polynomial and exponential activity. The characterization is Sidki's circuit theorem, applied
  to the nucleus.

| Case | Status | Credit | Commits |
|---|---|---|---|
| (B) bounded automata | `F_∞`, ESTABLISHED | Belk–Hyde–Matucci Thm 1.2 | abstract checked at source, ab1ad5c245 |
| (P) polynomial activity | `F_∞`, ESTABLISHED (item 1 of `rover-nekrashevych-polynomial-activity-tower-sigma-full`) | BHM Remark 2.14 (sketch), made complete via BHM Thm 1.1 applied to point-fixers along the activity tower | reviews 965e1aa19e (bh-sz-vdg) and 18b43406c6 (bh-ref-e). The Σ items 2–3 of that node remain unreviewed |
| (E), IMGs of PCF rational maps, sub-hyperbolic included | `F_∞`, ESTABLISHED (`pcf-rational-nekrashevych-groups-are-f-infinity`) | new; no priority found. The transfer theorem is bh-free-06's | 1cb417c62a; referee bh-ref-g 78f3553770; repairs 25ed3623cb; transfer theorem PASS by bh-ref-q12 ca350037cb; Lemma 7 stabilizers 7d34855ee4 |
| (E), expanding coverings of compact aspherical spaces | `F_∞` (`hyperbolic-pcf-rational-nekrashevych-groups-are-f-infinity`) | bh-free-06 | lane proof, not independently reviewed |
| (E), everything else | **OPEN** | — | — |

## The PCF theorem in one paragraph

- **The cover.** Take the orbifold fundamental group of Thurston's orbifold `O_f`, with small Böttcher discs removed
  around the periodic critical cycles. It is virtually free or cocompact Fuchsian or crystallographic, so `F_∞`.
- **Dying kernel.** Two facts give it:
  - a standard displacement lemma: for proper cocompact actions, short displacement implies ellipticity;
  - (T), a torsion-free kernel, because the cone orders are Thurston's `ν`, which are exactly the orders of the cone
    loops in `IMG f`.
- **Conclusion.** The transfer theorem then gives `F_∞`.
- **Recalled inputs.** Orbifold expansion and `χ(O_f) ≤ 0` are recalled, standard, and not re-read at source.

## What is left, precisely

`contracting-groups-have-aspherical-expanding-models` (OPEN) asks for the following.
- **The ask.** Every contracting group should be the IMG of an expanding self-covering of a compact orbi-complex with
  contractible universal cover and injective finite local groups.
- **The criterion.** Such a model gives `F_∞` by the same argument.
- **Why the limit orbispace doesn't serve.** It is not a model when it is not semi-locally simply connected, as for
  the basilica and the Sierpiński gasket. A thickening is needed.
- **First test.** Is Nekrashevych's `U(N)` presentation 2-complex, with its recursion, an expanding model? If so, can
  it be made aspherical? Compare Bartholdi arXiv:1107.5339.
- **Scope.** The question is stronger than Skipper–Zaremsky, so a negative answer to it would not refute
  Skipper–Zaremsky.

## Lessons (also appended to board/LESSONS.md)

- **Defect is irrelevant here.** For Röver–Nekrashevych groups the only invariant that matters for the RSG machinery
  is the cardinality of singular sets, since defect is always zero.
- **Dying kernel means a torsion-free kernel.** For geometric covers it reduces to injectivity of finite local groups:
  short loops are elliptic, and elliptic elements must not die. For dynamical covers the torsion is the branching
  data, which the self-similar group sees.

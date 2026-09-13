# Relation climbing, part 2: finite presentation forces finite type, illegality relations, and the escape of illegality from interacting pairs

Lane `ex-fp-simple-relation-climbing`, 2026-09-13. Unreviewed. Continues
`research/artifacts/fp-simple-relation-climbing-2026-09-13.md`. It backs:
- `zd-derived-full-group-fp-forces-finite-type` (the proof is in its route);
- the Attempts of `labbe-full-group-local-relations-climb`.

## 0. Summary

1. **Finite presentation forces finite type (landed `5eab856027`).** A free minimal
   `Z^d`-subshift whose derived full group is finitely presented is of finite type. For `d = 1` this
   is Matui's theorem; for `d >= 2` it is new in the sources read.
   - The engine is Lemma B of the proof route: on every colouring of `Z^d` whose small windows are
     legal, ChJN's nested commutator word `W(q, e)` of any ball pattern `q`, legal or not, acts as
     the 3-cycle on the occurrences of `q`.
2. **Illegality relations (Section 3).**
   - If some radius-`R` sub-ball of `q` is illegal, `W(q, e)` reduces to the empty word.
   - Otherwise `W(q, e) = 1` is a genuine relation of `G`. For a nearest-neighbour SFT this happens
     exactly for locally admissible patches that do not extend.
   - These relations are one family that relation climbing must derive from finitely many.
3. **Escape from interacting pairs (Section 4, exact data).** Take two legal ball patterns of
   radius `r+1` that agree at offset `delta`, `|delta|_1 <= 2`, and whose union is illegal.
   - Some pair of radius-`r` sub-balls always has an illegal union: no exceptions at radii 2–6.
   - At every radius, part of that illegality is visible only at sub-ball offsets 3 or 4, where the
     coarse 3-cycles never meet. At diagonal offsets this is the usual case.
   - One dimension shows the same escape, so pairwise combinatorics does not separate `Z^2`-SFTs
     from `Z`-subshifts.
4. **Literature and tools (Section 1).** A bounded search found no finite-presentation result for
   `Z^d` full groups. GAP is available on MSI.

## 1. Literature (bounded) and tools

- **arXiv search page** (arxiv.org/search, query `"topological full group" "finitely presented"`,
  all fields): two results.
  - Matui, arXiv:1210.5800: one-sided SFT groupoids, finitely presented.
  - Carrión–Dadarlat–Eckhardt, arXiv:1210.4050.
  - The arXiv API returned HTTP 429 on MSI.
- **Semantic Scholar citation lists.**
  - Chornyi–Juschenko–Nekrashevych arXiv:1602.04255 has 8 listed citing papers: 2312.07375,
    2304.13691, 2209.08087, 1902.04131, 1901.04428, 1712.08418, 1601.01033, 1511.08241.
  - Grigorchuk–Medynets arXiv:1508.04454 has 2: 2605.30605 and one unnumbered 2021 paper.
  - By title, none treats finite presentation of derived full groups of `Z^d`-subshifts.
- **Scope of the check.** Citation lists are incomplete, full texts were not read, and the web
  search budget is exhausted. So this is a bounded check, not a literature verification.
- **GAP 4 on MSI.** Run it as
  `singularity exec -B /scratch.global,/projects,/common <sagemath 10.7 image> gap -q file.g`.
  The module wrapper `sagemath-exec` fails, because it binds `/panfs`, which does not exist on the
  node.

## 2. What the finite-type mechanism says about climbing

**Setting.** `X` is a free minimal `Z^d`-subshift (`d >= 2`), `R >= R_1 + 2`, `S` the rule 3-cycles
of legal `B(R)`-patterns, and `W(q, e)` the recursive words of
`zd-derived-full-group-fp-forces-finite-type-proof`.

**Lemma B, restated.** Let the colouring `c` be `max(R, R_1 + 3)`-legal. Then `W(q, e)` acts on `Z^d`
as `tau_c(q; 0, e, -e)`, for every ball pattern `q`.

**Two readings.**
- **Non-SFT `X`.** The colourings of the Markov approximation `X_N` carry the relations of length
  `<= (N - R - 1)/2`, and they violate `W(q, e) = 1` for illegal `q` occurring there. These rule
  groups converge to `G` in the space of marked groups and differ from it. That is the approximating
  sequence the crux dossier (Section 4) asked for, now with the detecting word identified.
- **An SFT such as `Omega_U`.** The legal colourings are the points of `X`, and Lemma B only restates
  `minimal-free-sft-full-group-pattern-models-are-exact`.
  - An approximant that is a rule action must see illegal small windows somewhere.
  - **Remark (sketch).** Evaluating `W(q, e)` at a point reads the colouring on a bounded
    neighbourhood of radius `O(|q|)`. So if all relations of length `<= L` hold, every ball pattern
    of radius `M` occurring farther than `O(M)` from the illegal windows is legal.

## 3. Illegality relations

**Lemma 3.1.** For `q` on `B(r)`, `r >= R`, the leaves of the recursion defining `W(q, e)` are the
restrictions `q|(B(R) + v)` for `v ∈ B(r - R)`, and every such sub-ball occurs as a leaf. If some leaf
is illegal, `W(q, e)` is the empty word.

*Proof.*
1. **Leaves.** `W(Q_j, e)` has children `W(Q_(j-1), e)` and `W(q_(h_j), ·)`. Unwinding `j` gives the
   children `q|B(r-1)` and all `q_h`, `h ∈ S_d`, which are the radius-`(r-1)` sub-balls at centres
   `0` and `h`. Induction on `r` gives all centres in `B(r - R)`.
2. **Empty children propagate.** An illegal leaf has the empty word by definition.
   - If `b = 1`, then `[[b^(-1), a^(-1)], [b, a]] = [a^(-1), a] ... = 1` in the free group.
   - If `a = 1`, the same holds.
   - So a node with an empty child is empty, and by induction so is the root. ∎

**Illegality relations.** Call `q` *locally legal* if all its radius-`R` sub-balls are legal. For
locally legal `q` that is illegal, `W(q, e) = 1` is a relation of `G` that free reduction does not
see.
- **Nearest-neighbour SFTs.** For `R >= 1` every adjacent pair of sites lies in a radius-`R` sub-ball.
  So locally legal means locally admissible, and illegal means non-extendable.
- **Consequence for climbing.** Finite presentation requires these relations to follow from
  finitely many. It also requires the order-3 and Alt-type relations among climbed words at every
  radius to follow from finitely many. Those are not free-group identities either.

## 4. Test (T1): does illegality stay visible to interacting coarse pairs?

**Setup.** Script `experiments/fp-simple-relation-climbing/labbe_pairs.py`, run on MSI in 4 seconds,
using `L_(B(9))` (1630 patterns, from `omega^7` of the 50 legal `2 x 2` patterns; completeness as in
part 1, Section 4).
- For each radius `r+1` and offset `delta`, enumerate all pairs of legal `B(r+1)`-patterns that
  agree on the overlap of `B(r+1)` and `B(r+1) + delta`, and whose union is illegal.
- For each, find the least offset between a radius-`r` sub-ball of the first (centres `H_5`) and one
  of the second (centres `delta + H_5`) whose union is illegal.
- A 3-cycle `tau(sigma; 0, e, -e)` and one for a pattern at offset `u` can share a point only if
  `|u|_1 <= 2`. So offsets 3–4 are *non-interacting*.

**Results.** Each cell is `illegal unions / witnessed at offset <= 2 / only at offset 3–4 / no
witness`.

| `r+1` | `delta = (1,0)` | `(0,1)` | `(2,0)` | `(0,2)` | `(1,1)` | `(1,-1)` |
|---|---|---|---|---|---|---|
| 2 | 145/145/0/0 | 74/73/1/0 | 223/213/10/0 | 136/130/6/0 | 13/1/12/0 | 11/1/10/0 |
| 3 | 155/151/4/0 | 123/102/21/0 | 219/209/10/0 | 214/168/46/0 | 31/0/31/0 | 29/0/29/0 |
| 4 | 168/168/0/0 | 92/92/0/0 | 214/214/0/0 | 132/132/0/0 | 8/0/8/0 | 6/0/6/0 |
| 5 | 206/197/9/0 | 117/108/9/0 | 260/237/23/0 | 207/160/47/0 | 35/0/35/0 | 21/0/21/0 |
| 6 | 286/286/0/0 | 129/125/4/0 | 352/345/7/0 | 201/198/3/0 | 13/4/9/0 | 17/3/14/0 |

**Reading.**
- **Pairwise determination holds at radii 2–6.** Every illegal union of two finer ball patterns has
  an illegal union of two coarser sub-balls.
- **The witness often escapes interaction.**
  - At diagonal offsets, at radii 3, 4 and 5, every illegal union is witnessed only at offsets 3–4.
  - At radii 2 and 6 a few are witnessed at offset `<= 2`.
  - At axis offsets the escape happens at radii 2, 3, 5 and 6.
  - So the finer commutation relation `[W(rho, e), W(rho', e')] = 1` at diagonal offsets cannot be
    read off from the pair relations of interacting coarse generators. It needs relations among at
    least three coarse generators, placed around the diagonal.
- **Calibration against one dimension.** For words of length `n+1` at offset 2, the witnessing pair
  is the first subword of one and the last of the other, at offset 3, also non-interacting (part 1,
  Section 5). So the escape is common to `Z`-subshifts and to `Omega_U`. Pairwise combinatorics of
  sub-balls does not separate the case where climbing is known to fail from the case at hand.

## 5. Where the positive side stands

**Dead or settled.**
- Rule-action approximants on legal colourings (pattern-model exactness).
- Every non-SFT candidate (Section 2).
- Climbing through interacting coarse pairs alone, which fails at every computed radius (Section 4).

**Live.**
- A local presentation (`zd-subshift-derived-full-group-local-presentation`), together with
  climbing through relations among `k >= 3` coarse generators.
- Climbing by self-similarity (`labbe-full-group-embeds-in-its-supertile-corner`).

**Refutation must use** colourings with illegal small windows whose cores are patched so that the
short relators still hold, or non-spatial marked groups.

---
rg: 2
id: closed-surface-mapping-class-groups-satisfy-boone-higman
kind: claim
root: true
title: The mapping class group of every closed surface of genus at least three embeds in a finitely presented simple group
distinct_from:
  boone-higman-conjecture: that quantifies over all finitely generated groups with solvable word problem; this is the special case of closed-surface mapping class groups, the part of item (2) of the survey's Problem 5.3 still open after BFFHZ.
  punctured-surface-mcgs-satisfy-permutational-boone-higman: that is the known case, surfaces with a puncture or boundary and closed surfaces of genus at most two; this is the remaining case, closed surfaces of genus at least three.
  fp-residually-finite-boone-higman: that is item (12), all finitely presented residually finite groups; this is the open part of item (2), a single family of such groups.
artifacts:
  - research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md
---

**OPEN.** For every closed orientable surface `Σ` of genus `g ≥ 3`, `Mod(Σ)`
embeds in a finitely presented simple group.

This is the open part of a named problem.
- **Survey.** Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356v3, Problem
  5.3(2), "Mapping class groups of surfaces", and Remark 5.4: "Item (2) remains
  open for mapping class groups of closed surfaces of genus 3 or greater".
- **BFFHZ.** arXiv:2503.21882v2: "For mapping class groups, the conjecture
  remains open for closed surfaces of genus at least three."

Genus at most two and all surfaces with a puncture or boundary are
`punctured-surface-mcgs-satisfy-permutational-boone-higman`.

## Attempts

1. **The BFFHZ method.** BFFHZ, Section 4: "If a version for Out(Fn) were
   possible, it is likely that a similar argument would also cover the mapping
   class group of a closed surface Σ, since this is an index-2 subgroup of
   Out(π1(Σ))." No such version exists yet (`out-free-groups-satisfy-boone-higman`).
2. **Covering lifts to marked covers.**
   - *Dies* for `g ≥ 4`: the route `closed-mcg-bh-via-covering-lift-to-marked-cover`
     is invalidated by `closed-mcgs-have-no-covering-lift-to-marked-covers`.
   - In genus 3 such a lift exists iff the genus-3 Birman sequence has a
     section over a finite-index subgroup (`outer-covering-lifts-are-virtual-sections`),
     and a section would settle genus 3 through
     `punctured-surface-mcgs-satisfy-permutational-boone-higman`. Chen--Salter's
     Theorem A starts at genus four, so this case is undecided here.
   - Luo--Watanabe, arXiv:2502.14343v2, abstract (read from the PDF on MSI):
     "for any finite index subgroup of the mapping class group containing the
     Johnson subgroup, the profinite Birman exact sequence does not split in
     genus g ≥ 3". Whether this excludes a discrete section over a finite-index
     subgroup in genus 3 was not checked. Such a subgroup need not contain the
     Johnson subgroup, and exactness of the completed sequence was not verified
     from source.
3. **A punctured host by other means.** Route `closed-mcg-bh-via-punctured-mcg-host`,
   with open premise `closed-mcgs-virtually-embed-in-punctured-mcgs`. Its
   Attempts record the small-genus exclusion of Aramayona--Souto.
4. **Linear hosts.** BFFHZ: "it is an open problem whether mapping class groups
   of closed surfaces of genus at least three are linear."
5. **PIP homeomorphisms.** Survey Remark 5.5:
   - The mapping class group acts on the Thurston boundary of Teichmüller
     space by piecewise-integral-projective homeomorphisms.
   - Thurston's question whether these groups are finitely generated "remains
     open, but if these groups turn out to be finitely presented simple groups,
     this would yield a natural Boone–Higman embedding for mapping class groups
     of closed surfaces."

   Not pursued here.

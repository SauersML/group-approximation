---
rg: 2
id: soluble-automatic-groups-are-virtually-abelian
kind: claim
title: Every soluble automatic group is virtually abelian (Thurston's conjecture)
distinct_from:
  amenable-automatic-groups-are-virtually-abelian: that asks it of every amenable automatic group; this is the soluble case alone, which that claim implies but which does not imply it without elementary amenability and further imports
  soluble-automatic-groups-are-polycyclic: that concludes only polycyclic; the two are equivalent given Harkins' polycyclic theorem, but polycyclic groups such as Sol lattices need not be virtually abelian
---

**OPEN.** If `G` is a finitely generated soluble group with an automatic structure
(ECHLPT, *Word Processing in Groups*, 1992), then `G` has an abelian subgroup of finite
index.

Rees (arXiv:2205.14911v1, p. 14, read 2026-09-16): "It was conjectured by Thurston that
the same result must hold for an automatic soluble group. That conjecture remains open".

It matters here because, together with
`amenable-automatic-groups-are-elementary-amenable`, it gives
`amenable-automatic-groups-are-virtually-abelian` (route
`amenable-automatic-va-via-ea-and-soluble-case`). It is also a consequence of that claim
(route `soluble-automatic-va-from-amenable-case`).

## Attempts

- 2026-09-16 (lane swarm-amenable-automatic-groups-are-): **status.**
  - Rees's 2022 survey calls the conjecture open on p. 14. On p. 27 it lists "whether
    all soluble automatic groups must be virtually abelian" among the open questions and
    says: "The most recent progress on this last question was made by the proof of
    Romankov [69], that a soluble biautomatic group must be virtually abelian".
  - arXiv API searches on 2026-09-16 (title and abstract only, math.GR) found no later
    progress:
    - `abs:"automatic" AND abs:"soluble"`: 1 hit;
    - `abs:"automatic" AND abs:"solvable"`: 11 hits;
    - `abs:"automatic group"`: 39 hits. The 2024–2026 hits are arXiv:2405.17695,
      2508.01075 and 2607.26284, and none of them is about soluble groups.
- **Known cases.**
  - Nilpotent: `automatic-nilpotent-groups-are-virtually-abelian` (ECHLPT).
  - Polycyclic: `polycyclic-automatic-groups-are-virtually-abelian` (Harkins' 2001
    thesis, secondary import).
  - Soluble biautomatic: Romankov, arXiv:1511.00223v1, Theorem 6.3.
- **Equivalent forms.**
  - With Harkins, this claim is equivalent to `soluble-automatic-groups-are-polycyclic`
    (routes `soluble-automatic-va-via-polycyclic-case` and
    `soluble-automatic-polycyclic-from-virtually-abelian-case`).
  - Romankov (p. 1) writes that whether automatic groups are biautomatic "is not known
    even in the class of soluble groups". Virtually abelian groups are biautomatic (Rees,
    p. 14). So Romankov's Theorem 6.3 makes this claim equivalent to "soluble automatic
    groups are biautomatic". That equivalence is not recorded as routes, because
    Romankov's theorem is not imported.
- **Where the biautomatic proof stops.** The steps of Romankov's proof are checked one by
  one in `research/artifacts/amenable-automatic-groups-are-virtually-abelian-2026-09-16.md`,
  Section 7.
  - Surviving steps: type `FP_∞` (`automatic-groups-are-of-type-f-infinity`), then
    Kropholler's theorem, then a torsion-free finite-index subgroup `H` that is soluble
    minimax and nilpotent-by-(virtually abelian).
  - Failing steps: the Gersten–Short exclusion of `UT_3(Z)` subgroups, and the minimal
    condition on centralizers that makes `H` polycyclic. Both use the biautomatic
    centralizer theory, and no automatic analogue is known to this lane.
  - Romankov writes `[u, y] ∈ ζ_1(H)` where the argument gives `ζ_1(N)`. That
    correction is recorded in the artifact.
- **Growth and Dehn function do not help.**
  - `automatic-groups-virtually-abelian-or-free-subsemigroup` excludes subexponential
    growth. Non-virtually-nilpotent soluble groups already grow exponentially
    (Milnor–Wolf).
  - A quadratic Dehn function does not exclude non-polycyclic metabelian groups.
    De Cornulier–Tessera (arXiv:1003.0148, abstract read 2026-09-16) embed `BS(1,n)` in
    finitely presented metabelian groups with quadratic Dehn function. Whether those
    examples are of type `FP_∞` was not checked.

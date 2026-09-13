---
rg: 2
id: every-closed-surface-mcg-embeds-in-some-aut-free-group
kind: claim
title: For every g some Aut(F_n) contains a subgroup isomorphic to the mapping class group of the closed genus-g surface
distinct_from:
  closed-mcgs-virtually-embed-in-punctured-mcgs: that asks for a finite-index subgroup of a closed-surface mapping class group inside a punctured-surface mapping class group; this asks for the whole group inside some Aut(F_n), which that implies through punctured-surface-mcgs-virtually-embed-in-aut-free-groups, while the converse is not known.
  low-genus-closed-mcgs-embed-in-aut-free-groups: that is the established case of genus at most two; this is the statement in every genus.
---

**OPEN.** For every `g ≥ 0`, the orientation-preserving mapping class group
`MCG(S_g)` of the closed orientable surface of genus `g` embeds in some
`Aut(F_n)`. By `aut-free-embeddability-passes-to-finite-index-overgroups` this is
the same as asking that some finite-index subgroup does, and it covers the
extended mapping class group too.

- `g ≤ 2`: established, `low-genus-closed-mcgs-embed-in-aut-free-groups`.
- `g ≥ 3`: follows from `closed-mcgs-virtually-embed-in-punctured-mcgs`
  (route `closed-mcg-aut-embedding-via-punctured-host`).
- Any host has `n ≥ 2g − 1`
  (`rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg`).
- A yes gives the Boone--Higman conjecture for these groups
  (`closed-mcg-bh-via-aut-free-host`).

This is the affirmative answer to the Aut-host question of Zaremsky Problem 3.10
(`zaremsky-3-10c-by-yes`).

## Attempts

1. **Punctured host.** Route `closed-mcg-aut-embedding-via-punctured-host`; its
   open premise records the Aramayona--Souto exclusion of small-genus targets.
2. **Covering lifts to marked covers.** Die in genus `≥ 4`
   (`closed-mcgs-have-no-covering-lift-to-marked-covers`) and in genus 3
   (`genus-three-mcg-has-no-covering-lift-to-marked-covers`, resting on an
   unreviewed adaptation of Chen--Salter).
3. **Linear intermediaries.** None available: linearity of closed-surface
   mapping class groups of genus `≥ 3` is open, and `Aut(F_n)` is not linear for
   `n ≥ 3` (Formanek--Procesi 1992, not re-read), so a linear host would not sit
   inside `Aut(F_n)` anyway.
4. **Arbitrary faithful actions.** By the finite-index lemma any faithful action of
   any finite-index subgroup on a finitely generated free group suffices; it need
   not come from a surface. No candidate is known.

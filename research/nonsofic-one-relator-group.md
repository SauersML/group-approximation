---
rg: 2
id: nonsofic-one-relator-group
kind: claim
title: A one-relator group that is not sofic
distinct_from:
  one-relator-groups-sofic: that is the affirmative answer to the same question of Pestov; this is the witness demanded by the negative answer. They cannot both be established.
  nonsofic-one-relator-relator-has-primitivity-rank-two: that is a necessary condition on any such group and is closed; this asks for one to exist and is open.
  nonsofic-hyperbolic-group: that asks for a nonsofic group in the hyperbolic class; this asks for one in the one-relator class. The classes overlap only at negative immersions, where one-relator groups are hyperbolic and virtually special hence sofic, so no witness can serve both.
  kun-thom-nonsofic-wreath: that records existing nonsofic groups, all built from Kazhdan pairs; this asks for one with a one-relator presentation, which by the local-indicability obstruction cannot contain any of them.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

OPEN.  Exhibit a group `G = <X | w>` with a single defining relation that is
**not sofic** — the negative answer to Pestov's Open Question 4.9, whose
affirmative answer is [[one-relator-groups-sofic]].

Any such `G` is heavily constrained before the search starts.  By
[[nonsofic-one-relator-relator-has-primitivity-rank-two]] it has `π(w) = 2`, is
torsion-free and locally indicable; by
[[torsion-free-one-relator-has-no-kazhdan-subgroup]] it contains no nontrivial
finitely generated Kazhdan subgroup; by
[[residually-rationally-solvable-one-relator-sofic]] it is not residually
rationally solvable, so its Linton radical `R = G_Q^(ω) = <<r>>_G` is nontrivial
and (in the torsion-free case) infinitely generated; and by
[[one-relator-soficity-localizes-at-rational-derived-stage]] the nonsoficity is
already present in `E = G_Q^(n) ≅ R ⋊ F₀` for some `n <= |w|`.

## The structural tension that makes this hard

Every nonsofic group known in August 2026 gets its nonsoficity from **rigidity**
— property (T) in the Kun--Thom wreaths and in Fournier-Facio's torsion-free
example alike.  The one-relator regime where a counterexample could live is
**locally indicable**, which forbids exactly that.  So a witness needs a
nonsoficity mechanism nobody has: one compatible with every nontrivial finitely
generated subgroup surjecting onto `Z`.

## Attempts

1. **Embed a known nonsofic group.**  *Dead*, recorded as
   `nonsofic-one-relator-via-kazhdan-subgroup-embedding` and killed by
   [[torsion-free-one-relator-has-no-kazhdan-subgroup]].  Both sides of the
   torsion dichotomy close: torsion-free one-relator groups are locally
   indicable and admit no f.g. Kazhdan subgroup, while one-relator groups with
   torsion are virtually compact special, hence residually finite, hence sofic
   and containing nothing nonsofic at all.
2. **Compress a two-generator perfect nonsofic quotient to one relation.**
   *Dead*, recorded as `nonsofic-one-relator-via-perfect-quotient-compression`
   and killed by [[perfect-two-generator-relation-module-not-cyclic]]: over `F_2`
   with perfect target, the relation module's coinvariants surject onto `Z²`,
   so the module is not cyclic and the kernel is not the normal closure of one
   element.
3. **Force a nonsofic quotient with amenable kernel.**  *Dies on the direction
   of the permanence theorem.*  Soficity is not known to pass to quotients at
   all, and the available theorem is sofic **kernel** plus amenable
   **quotient** ⟹ sofic, which says nothing about a quotient by an amenable
   normal subgroup.  So a one-relator `G` with `1 → A → G → Q → 1`, `A`
   amenable and `Q` nonsofic, is not a contradiction with soficity of `G` and is
   not a witness either.  This killed several Rips- and HNN-style constructions
   at once.
4. **Boone/Higman-style compression of a finitely presented nonsofic group.**
   *Dies on presentation count.*  The clean base in this corpus is genuinely
   one-relator ([[boone-base-group-two-generator-one-relator]] — three
   generators, one relation, as its body says), but the tower that encodes the
   content adds a stable letter with conjugacy relations per stage, and no
   Tietze collapse to a single relator preserving the embedded subgroup is
   known.  Higman embedding delivers **finite** presentation, not one-relator
   presentation; a universal "every f.p. group embeds in a one-relator group"
   theorem would settle this claim immediately and is exactly what the subgroup
   structure of one-relator groups makes implausible.
5. **Marked-group openness.**  *Insufficient, though it looks close.*
   Nonsoficity is open in the space of marked groups, so any f.g. nonsofic group
   yields **finitely presented** ones by adding the finitely many relations that
   already witness the failure.  That controls presentability, not relator
   count; openness gives a finite obstruction, never a one-word one, and
   attempt 2 shows one-word compression can fail for homological reasons.
6. **Break soficity inside a Magnus chain directly.**  *Deferred, and the most
   promising negative lane.*  Take a specific `π(w) = 2` relator, build the
   bi-infinite amalgam of §8 of the artifact, and show its finite permutation
   models violate a rigidity inequality.  Structurally aligned with the real
   core — it attacks the free-edge obstruction rather than importing a witness —
   but no candidate inequality is in hand, and the whole point of the local
   indicability constraint is that the Kun--Thom style of inequality is
   unavailable here.

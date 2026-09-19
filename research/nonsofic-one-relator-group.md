---
rg: 2
id: nonsofic-one-relator-group
kind: claim
title: A one-relator group that is not sofic
root: true
distinct_from:
  one-relator-groups-sofic: that is the affirmative answer to the same question of Pestov; this is the witness demanded by the negative answer. They cannot both be established.
  nonsofic-one-relator-relator-has-primitivity-rank-two: that is a necessary condition on any such group and is closed; this asks for one to exist and is open.
  nonsofic-hyperbolic-group: that asks for a nonsofic group in the hyperbolic class; this asks for one in the one-relator class. The classes overlap only at negative immersions, where one-relator groups are hyperbolic and virtually special hence sofic, so no witness can serve both.
  kun-thom-nonsofic-wreath: that records existing nonsofic groups, all built from Kazhdan pairs; this asks for one with a one-relator presentation, which by the local-indicability obstruction cannot contain any of them.
  hyperlinear-nonsofic-group: that asks for a nonsofic group that is additionally hyperlinear, answering Pestov 3.4; this asks for one that is additionally one-relator, answering Pestov 4.10. Different questions, and no witness is known to serve either, let alone both.
  residually-rationally-solvable-one-relator-sofic: that establishes soficity on a subclass of the same groups; this asks for a nonsofic member of the complementary subclass. The first is a theorem, the second an open search, and the first constrains where the second may look.
  linton-shell-sofic: that is a positive statement about the shell of every one-relator group; this asks for a single one-relator group that is nonsofic. Establishing this refutes that; they are opposite answers reached through different objects.
  linton-radical-sofic: that concerns the radical alone and would be one input to a positive answer; this asks for the whole group to fail, and by the failure of semidirect closure a sofic radical does not prevent it.
  linton-radical-abelianization-is-truncated-group-ring: that is a closed homology computation inside such a group; this asks for the group to exist at all. The computation constrains any witness without producing one.
  one-relator-fox-magnus-descent-to-derived-linton-radical: that proves every element outside `R'` survives in a concrete sofic quotient and `E/R'` is residually finite; this asks for a witness whose obstruction must evade all those first-order quotients.
  magnus-staggered-chain-sofic: that is the positive amalgamation theorem in the Magnus picture; this is the negative existence claim. Attempt 6 here proposes breaking exactly that chain, so they meet, but as opposite answers.
  boone-base-group-two-generator-one-relator: that identifies a specific base group of the Boone tower as one-relator (on three generators) and is established; this asks for a one-relator group with a nonsoficity property that base group does not have and cannot acquire from the tower, since the tower adds relators.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
  - research/artifacts/approximation-cs-root-audit-2026-08-31.md
---

OPEN.  Exhibit a group `G = <X | w>` with a single defining relation that is
**not sofic** — the negative answer to Pestov's Open Question 4.10, whose
affirmative answer is [[one-relator-groups-sofic]].

The exact reduction
[[one-relator-soficity-is-torsion-free-two-generator-case]] now shows that
any witness can be replaced by a torsion-free two-generator one-relator
witness. Thus the negative search loses no generality by imposing both
restrictions simultaneously.

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

Independently, [[one-relator-groups-are-coherent]] and
[[characteristic-zero-one-relator-group-algebras-are-coherent]] show that every
hypothetical witness `G` and every `K[G]` over a characteristic-zero field are
coherent.  Thus incoherence cannot supply the missing nonsoficity mechanism;
these finiteness theorems constrain the search without deciding it.

There is now one further exact constraint.  By
[[one-relator-fox-magnus-descent-to-derived-linton-radical]], `G/R'` is sofic,
`E/R'` is residually finite, and every element outside `R'` is separated by a
concrete sofic quotient.  Thus no candidate obstruction detectable by an
abelian, solvable, rational-derived, or first-order Fox quotient can witness
nonsoficity.  This does not assert that `R'` itself is nonsofic; it says the
remaining failure, if any, must be action-sensitive and invisible after
quotienting by `R'`.

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
3. **Force a nonsofic quotient with amenable kernel.** *Dies on the direction
   of the permanence theorem.* Arbitrary quotient permanence is false by
   [[sofic-quotient-nonclosure]], so a nonsofic quotient alone cannot force the
   source to be nonsofic. The narrower statement needed here, permanence under
   quotienting by an amenable normal subgroup, is not supplied by the standard
   theorem. That theorem goes the other way: sofic **kernel** plus amenable
   **quotient** implies sofic. Thus a one-relator `G` with
   `1 → A → G → Q → 1`, `A` amenable and `Q` nonsofic, is neither contradicted
   by known permanence nor proved nonsofic. This kills the naive Rips- and
   HNN-style constructions.
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
7. **Iterate relation modules or solvable lamps.**  *Closed as a route to the
   perfect core.*  The mod-`k` Magnus map already has exact kernel `R'`.  When
   `k = 1`, `R = R'` is perfect, so every solvable quotient of the radical is
   trivial.  Any negative witness must therefore use genuinely nonabelian
   second-order information and its coupling to the free shell action.

---
rg: 2
id: ffgs-local-hs-examples-resist-split-finite-presentation-wrappers
kind: claim
title: FFGS locally HS-stable simple groups resist every split or finite-index finite-presentation wrapper
artifacts:
  - research/artifacts/ffgs-local-hs-wrapper-audit-2026-08-21.md
distinct_from:
  hs-stability-descends-to-retracts: that transfers normalized-HS stability from an ambient finitely presented group to a finitely presented retract; this identifies the algebraic obstruction before stability is considered and applies to the infinitely presented FFGS source groups.
  finitely-presented-local-hs-stable-non-rf-is-nonhyperlinear: that is the final analytic criterion; this classifies which natural finite-presentation wrappers cannot even reach its finite-presentation hypothesis.
---

Let `T` be a minimal Cantor subshift and put

```text
H=[[T]]'.
```

Fournier-Facio--Gerasimova--Spaas, arXiv:2307.13155v2,
Theorems 5.4 and 5.5, give that `H` is finitely generated, infinite, simple,
amenable, LEF, and locally normalized-HS stable.  Then:

1. `H` is not finitely presented.  Indeed a finitely presented LEF group is
   residually finite, whereas an infinite simple group has no nontrivial
   finite quotient.
2. If `H` is a retract of a group `G` and `G` is finitely presented, then
   `H` is finitely presented.  Hence no retract, split-extension, direct-
   product, or graph-product wrapper containing `H` as a vertex can turn it
   into a finitely presented group.
3. If `H` has finite index in `G` and `G` is finitely presented, then `H` is
   finitely presented by Reidemeister--Schreier.  Hence no finite extension
   of `H` supplies the missing finite presentation.
4. Every finite-dimensional unitary representation of `H` is trivial.  A
   nontrivial representation would be injective by simplicity; its finitely
   generated linear image would be residually finite by Malcev, contradicting
   the preceding finite-quotient observation.  Therefore any embedding
   `H -> G` carries every nontrivial `h in H` to a nontrivial word killed by
   every finite-dimensional representation of `G`.

The retract assertion in item 2 is purely finite-presentation theoretic.  If
`G=<S|R>` is finite and `e:G->G` is the idempotent with image `H`, choose a
word `w_s` for `e(s)` for each `s in S`.  Then

```text
< S | R, s=w_s (s in S) >
```

presents `im(e)`: its added relations kill `ker(e)`, since every `g` becomes
equal to `e(g)`, and `e` is the identity on its image.  Thus retracts of
finitely presented groups are finitely presented.

There is one genuine positive permanence statement, but it cannot evade this
obstruction.  FFGS Proposition 4.12 says that if an amenable group `H` and a
group `K` are locally HS-stable, then `H x K` is locally HS-stable (and
likewise in the flexible variants).  In particular `H x F_2` is an explicit
finitely generated locally HS-stable non-MAP group, as their Example 4.13
records.  It remains infinitely presented because projection onto `H` is a
retraction.

Consequently Higman/Clapham-style **non-split embeddings** are the only listed
wrapper type not excluded algebraically.  They preserve the marked finite-
dimensional residual by item 4, but no local-HS-stability permanence theorem
passes from an embedded subgroup to its overgroup.  Proving such permanence
for one finitely presented wrapper would not be a routine compilation lemma:
by `finitely-presented-local-hs-stable-non-rf-is-nonhyperlinear`, it would
already construct a nonhyperlinear group.


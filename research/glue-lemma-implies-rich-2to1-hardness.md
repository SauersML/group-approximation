---
rg: 2
id: glue-lemma-implies-rich-2to1-hardness
kind: claim
title: The affine orientation-glue lemma would supply the missing richness in the F_lin 2-to-1 reduction
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**OPEN.**  The implication -- not the analytic lemma, the *use* of it:

```text
affine-orientation-glue-lemma  ==>  rich-2to1-games-conjecture.
```

It is recorded as a claim rather than folded into a route on purpose.  In
rg:2 the existence of a route asserts that route's validity, and this
implication is **not proved anywhere**.  The external dossier that opened
this region states it as "if established, would give the missing endgame",
which is a hope about an endgame, not an endgame.  Writing it as an
unmarked arrow would be a restatement dressed as a reduction: it would make
the graph report that UGC reduces to one analytic lemma, when in fact it
reduces to one analytic lemma *plus an unwritten reduction*.

What the implication has going for it: the glue lemma's conclusion is
exactly the object a soundness analysis consumes -- a list `Q` of at most
`L` candidate global labels, with `L` independent of the alphabet, hitting
a `gamma`-fraction of the heavy cosets.  Richness is the property that this
list exists.  `dummy-padding-cannot-beat-the-random-guessing-floor` shows
independence of the alphabet is the whole content, so a lemma delivering it
is delivering the right thing.

What is missing: the composition itself.  The decoder has to be assembled
from the list, the soundness loss accounted against the completeness of the
`F_lin` test, and the resulting gap has to survive whatever amplification
the reduction uses.  None of that is written down here.

## Attempts

* **Read it off the published Rich 2-to-1 framework.**  The natural move is
  to take the reduction of Braverman--Khot--Minzer and substitute the
  bounded list for the alphabet-sized one.  Not carried out; the point at
  which the published argument uses list size is not identified in this
  repository, and asserting the substitution works is exactly the trap this
  node exists to avoid.
* **Route through the multi-slice invariance machinery.**  Braverman, Khot,
  Lifshitz and Minzer (Adv. Math. 480 (2025), Art. 110460) prove a
  dictatorship-test-implies-hardness paradigm with perfect completeness
  **assuming** Rich 2-to-1.  So that work consumes the conclusion rather
  than producing it, and cannot supply this implication.
* Deferred until `affine-orientation-glue-lemma` is closer, since the
  precise form of `L` and `gamma` a reduction can afford is not yet fixed.

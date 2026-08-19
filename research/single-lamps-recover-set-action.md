---
rg: 2
id: single-lamps-recover-set-action
kind: claim
title: A sofic C-action on the C2 lamp group forces the underlying set action sofic
invalidates: [halo-target-class-enrichment]
distinct_from:
  coordinate-action-not-sofic: That refutes soficity of one specific coset action; this is a general transfer lemma, valid for every action on every set and for every target class, which says the lamp-group automorphism action can never be easier than the set action.
  halo-locally-sofic-target-collapse: That collapses witnesses whose targets happen to be locally sofic, via finite generation of a single witness; this is class-agnostic and argues through the lamp coordinates, so it covers target classes containing nonsofic groups.
  lamp-charts-recover-set-action: That is the strict generalization to an arbitrary lamp group permuted by G, including the Clifford lamp C(X) and the invariant-graph lamps that the Clifford lane uses; this is the commuting case V = directSum_X C_2, which is the one the wreath candidate itself needs.
artifacts:
  - notes/NOTEPAD.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

Let a group `G` act on a set `X`, put

```text
D = directSum_X C_2,
```

and let `G` act on `D` by permuting coordinates.  If this automorphism action
is a **sofic `C`-action** in the sense of Alekseev--Bradford Definition 4.23,
**for any class `C` of groups whatsoever**, then the original action
`G action X` is a sofic action on a set.

The quantifier over `C` is the whole point: nothing in the proof uses any
property of the target class, so no enrichment of the targets — hyperlinear,
weakly sofic, linear sofic, Clifford, unitary, or any class yet to be named —
can make the lamp action satisfy the hypothesis while the set action fails it.

## Why this matters here

Applied to the Kun--Thom pair it removes the last apparent escape from
`coordinate-action-not-sofic`.  Alekseev--Bradford Corollary 5.2 is stated for
four classes (sofic, `K`-linear sofic, hyperlinear, weakly sofic), and its
class (c) invites the hope that `G action G/Gamma` might be a sofic
*hyperlinear* action even though it is not a sofic action, which would deliver
hyperlinearity of `W` from the permanence theorem directly.  This lemma says
that hope is empty for every class at once: a sofic `C`-action on the lamp
group would produce a sofic set action, and `coordinate-action-not-sofic`
forbids that.

Consequently the 2026 semidirect-product permanence theorem is inapplicable to
the Kun--Thom lamp for *every* choice of target class, not merely for the
sofic class.  Recorded as the invalidated route `halo-target-class-enrichment`.

## Scope

The lemma constrains the hypothesis of a permanence theorem.  It says nothing
about whether `W` is hyperlinear, and it is not an obstruction to
`hyperlinear-wreath-model`: it closes one family of *methods*, exactly as
`sofic-action-permanence` does, and leaves abstract existence untouched.

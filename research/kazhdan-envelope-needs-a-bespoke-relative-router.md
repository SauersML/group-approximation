---
rg: 2
id: kazhdan-envelope-needs-a-bespoke-relative-router
kind: claim
title: The Kazhdan envelope half of the universal source cannot use the literature route, and its bespoke replacement puts the relative transfer on the critical path
distinct_from:
  fournier-facio-torsion-free-skeleton: that records a PUBLISHED group that already carries the compression data, obtained by Osin small cancellation over a relatively hyperbolic pair; this claim is about replacing exactly that step by an in-repo construction, because the hyperbolic apparatus it needs is not present.
  defect-normally-generates-torsion-free-quotient: that is the remaining gap in the published skeleton; this is a gap in the fully bespoke route, and the two are alternatives rather than stages.
  torsion-free-finitely-presented-non-mf: that root is the existence statement; this is one half of one route to a source datum for it.
artifacts:
  - notes/KAZHDAN_ENVELOPE_BESPOKE_ROUTE_2026-08-22.md
  - GroupApproximation/Sofic/FournierFacioUniversalGroup.lean
  - GroupApproximation/Sofic/OsinRelativeSmallCancellation.lean
  - notes/lean_drafts/Sofic_GreendlingerRelativeTransfer.lean.txt
---

`ChiodoBelegradek.Statement` reaches only `UniversalTorsionFreeHost`.  The
universal Kazhdan group `KC.21` is assembled from that host **and** a
`KazhdanEnvelope`, and the envelope half has no in-scope literature route: it
would need Osin small cancellation over a relatively hyperbolic pair together
with a torsion-free hyperbolic Kazhdan partner, and the repository's
`HyperbolicKazhdanPartner` is a typed literature input with no hyperbolic
apparatus behind it.

Claim: the envelope can instead be built by running the repository's **own**
router pattern relatively.  Take `U * B` with `B = Gamma(3)`, which is finitely
presented, torsion-free and Kazhdan and is certified in-repo; impose a
symmetrized `C'(1/7)` family with no proper powers in which every generator of
each factor is tied to a long word of the other, every relator at least `42`
syllables.  Then property `(T)` descends because the tie relators make
`B ->> quotient` surjective; `U` embeds by the free-product Greendlinger factor
embedding; torsion-freeness comes from torsion-into-factors with both factors
torsion-free; and finite presentability is immediate.

## Why 1/7 and 42, and not 1/6

Whole-syllable `C'(lam)` is *weaker* than the classical letter-level condition,
so the fragment slack condition

```text
lam * wlen r + 1 <= (1/6) * wlen r
```

is what restores it.  That forces `lam < 1/6`, and `lam = 1/7` needs
`wlen r >= 42` exactly.  This is the recorded concrete pair; taking `lam = 1/6`
does not satisfy the slack condition at any length.

## The sequencing consequence, which is the point of recording this

The relative transfer --- `greendlingerConclusion_of_slack` and
`cyclicTorsionIntoFactors_of_slack`, Lyndon--Schupp V.9-11 re-run over
syllables --- is **not** needed for the torsion-free router on the free lane,
but it **is** on the critical path for the envelope.  So it is not optional
work that can be deferred indefinitely: it becomes a dispatch target the moment
the free-lane gate closes, and the combinatorial core is the same one, re-run
over `wlen`.

## Attempts

**Not attempted in Lean.**  This is a design, recorded so that the scope of the
remaining program is honest.  Nothing below has been formalized.

**Why the literature route was ruled out rather than deferred.**  Osin's
Theorem 2.4.5 is the standard tool and it is genuinely available in print; the
objection is not to its truth but to the trust surface --- using it means
carrying a typed transcription premise, and the corpus does not permit one.
That is a policy constraint, so no amount of care in reading Osin changes the
answer.

**The load-bearing uncertainty.**  Whether the tie relators can simultaneously
be long enough for the slack condition, avoid proper powers, and still make the
`B`-surjection hold is a family-construction question of exactly the kind the
router's own avatar exponent code answers on the free lane.  The expected mode
of failure is not that the argument breaks but that no family satisfies all
three at once; that would be worth recording as a refutation.

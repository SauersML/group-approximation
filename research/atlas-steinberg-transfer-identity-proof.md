---
rg: 2
id: atlas-steinberg-transfer-identity-proof
kind: route
title: Two applications of one bracket identity, with the derived object's commutation as output
target: atlas-steinberg-transfer-identity
requires: []
---

# Two applications of one bracket identity, with the derived object's commutation as output

The complete proof is displayed in the claim body (it is five lines) and
in full expansion in `research/artifacts/steinberg-spare-index-2026-08-15.md`
§6, with the two ingredient identities — `[ab,c] = a[b,c]a^{-1}·[a,c]`
and the `[X,Z] = 1` conjugation step — machine-checked on 4,000 random
samples each and the assembled statement on 782 samples meeting exactly
the three hypotheses.  Adversarial verification (2026-08-15, night)
re-derived both identities by hand, confirmed no hidden same-length
commutation enters (the length-`t` objects `T` and `[U,Z]` appear only
as outputs, and the commutation of `V` with `[U,Z]` is derived from
`[U,V] = [V,Z] = 1`), verified the three root patterns are genuine (St2)
instances including the load-bearing same-target pair, and confirmed the
emitted family contains all 120 qualifying root pairs by independent
count (380 ordered pairs of distinct roots, minus 140 failing the side
condition, giving 120 unordered: 60 + 30 + 30).

The history is part of the content: the first landed version of this
node assumed in addition that `T` commutes with `X`, `Y`, `V` — a
same-length hypothesis set that manufactured the apparent circularity
recorded in the derivation artifact's rejected-routes section.  An
over-strong lemma statement can manufacture an obstruction that is not
in the problem; the five rejected routes were attempts to supply a
hypothesis that never needed supplying.

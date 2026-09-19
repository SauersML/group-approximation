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
§4 (the two elementary identities), with the corrected hypothesis set
assembled in §11.3; the ingredient identities were machine-checked on
4,000 random samples each, and the assembled statement exhaustively over
`S₅` and `S₄` with per-hypothesis counterexample cells (see the claim
body's cross-check paragraph).  Adversarial verification (2026-08-15, night)
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

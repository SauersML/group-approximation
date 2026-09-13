---
rg: 2
id: non-finite-field-linear-sofic-via-uniform-rank-stability
kind: route
title: A finitely presented simple group that is uniformly rank-stable over finite fields is not linear sofic over finite fields
target: non-finite-field-linear-sofic-group-exists
requires: [fp-simple-group-uniformly-rank-stable-over-finite-fields-exists, fp-simple-group-not-linear-sofic-iff-rank-stable]
---

Let `G` witness `fp-simple-group-uniformly-rank-stable-over-finite-fields-exists`. By (b') => (a') of item 2 of
`fp-simple-group-not-linear-sofic-iff-rank-stable`, `G` embeds in no rank ultraproduct of groups `GL_(n_k)(F_(q_k))`.
So `G` witnesses the target, and with it `non-weakly-sofic-group-exists`, through
`non-weakly-sofic-group-from-non-finite-field-linear-sofic`.

The converse also holds for finitely presented simple witnesses, by (a') => (b'). So this route loses nothing for
them.

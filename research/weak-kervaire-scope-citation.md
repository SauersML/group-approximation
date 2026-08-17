---
rg: 2
id: weak-kervaire-scope-citation
kind: route
title: Read off the two automatic degrees, then record what Klyachko's equivalence covers
target: weak-kervaire-transfers-only-at-unimodular-degree
requires: []
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

The two automatic degrees are a computation, not a citation.  Let
`m = deg_t(w)`.

* `m = 0`.  The map `G * <t> -> Z` killing `G` and sending `t |-> 1` kills
  `w`, so `(G * <t>)/<<w>>` surjects onto `Z` and is nontrivial.
* `|m| > 1`.  The map `G * <t> -> C_|m|` killing `G` and sending `t` to a
  generator kills `w`, so the quotient surjects onto `C_|m|` and is
  nontrivial.

So the weak statement can only fail at `m = ±1`.  The nonsingular statement,
by contrast, has content at every `m != 0`: the surjections above kill `G`
entirely and therefore witness nothing about injectivity.

That the weak conjecture is *equivalent* to unimodular coefficient
injectivity is Klyachko, arXiv:math/0409146.  That reference was not read
from source on 2026-08-17 and the claim does not depend on it — the claim is
about what the weak conjecture leaves untouched at `|m| > 1`, which the
computation above settles.

Marimon--Pinsker, arXiv:2606.24741v2, read from source 2026-08-17, name the
one-variable case as "the famous Kervaire-Laudenbach Conjecture, answered
positively for finite groups and for hyperlinear groups" — the same
attribution the graph carries on
`kervaire-laudenbach-holds-for-hyperlinear`.

`requires: []` is a proof commitment for the computation, and a citation
import for the parenthetical equivalence.

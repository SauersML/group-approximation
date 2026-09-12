---
rg: 2
id: level-synchronous-first-mismatch-area-is-centralizer-impossible
kind: claim
title: Equal-level Morita mismatch tables still violate finite-mark centralizer properness
distinct_from:
  unsynchronized-first-mismatch-area-is-centralizer-impossible: that freezes one tail while allowing the other tail length to escape; this freezes one column separately at every common level and uses the exponentially many rows at that same level.
  finite-mark-centralizer-commutator-area-is-proper: that is the abstract properness theorem; this constructs the required growing distinct sections by conjugating each frozen Morita column back to one fixed root involution.
---

**ESTABLISHED.**  In the notation of `(MTR1)--(MTR2)`, no constant `A`
can satisfy

```text
Area([c_(ia),h_(jb)])<=A                                (SFM1)
```

for every `n`, every `a,b in {0,1}^n`, and one fixed unequal pair `i!=j`.

Fix a tail `b_n` at each level and put `g_n=D_(j b_n)^(-1)`.  Then

```text
g_n h_(j b_n) g_n^(-1)=h,
eta_(n,a)=g_n c_(ia) g_n^(-1) belongs to C_G(h).         (SFM2)
```

Conjugation does not change relator area, so `(SFM1)` would give

```text
Area([eta_(n,a),h])<=A                                  (SFM3)
```

for all `2^n` tails at level `n`.

For fixed `n`, the `eta_(n,a)` occupy `2^n` distinct cosets modulo `<h>`.
Before conjugation they are distinct `x_12` roots with distinct dual-prefix
coefficients.  Simultaneous conjugation preserves distinctness, and a
quotient of two such roots cannot become the identity or the `x_23`
involution `h`, as seen under the map to elementary matrices.  Thus `(SFM3)`
puts arbitrarily many distinct cosets of `C_G(h)/<h>` in one fixed
commutator-area sublevel set.

This contradicts `finite-mark-centralizer-commutator-area-is-proper`, whose
properness makes every such sublevel set finite.  Hence even the exact
equal-level quantifier needed by the canonical complete-graph tree cannot
have uniform area.

The obstruction identifies the hidden cost in qualitative context
absorption: the nested null word has constant area, but synchronously
rebracketing the canonical cross-branch commutators into that word must cost
unboundedly many cells.

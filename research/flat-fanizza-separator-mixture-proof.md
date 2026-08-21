---
rg: 2
id: flat-fanizza-separator-mixture-proof
kind: route
title: Direct-sum the eight pointwise extensions with prescribed multiplicities
target: flat-fanizza-triangle-realizes-every-separator-distribution
requires: []
---

Write `s=(q,p,z)`.  In `C_X`, take the two compared signs equal.  In `C_Z`,
take the private comparison sign equal to `z`.  These choices satisfy both
conditional-equality tables for either value of `q`.  In `C_D`, choose
`O_D` to be the required Boolean conjunction of `p,q`.

For `C_R`, its bad first-coordinate set is

```text
A_123={(-,+,+),(+,-,+),(+,+,-),(-,-,+),(-,-,-)}.
```

If `p=+1`, choose the other two first-coordinate signs as `(+,+)`; if
`p=-1`, choose them as `(+,-)`.  The resulting triple is outside `A_123`,
so the six-variable forbidden product does not occur, independently of `z`
and the other two last-coordinate signs.  This constructs a simultaneous
abstract context-table extension `a(s)` for every `s`.

If `mu(s)=n_s/N`, act on `C^N` diagonally:
on `n_s` basis vectors, every context occurrence has the sign prescribed by
`a(s)`.  Each truth-table projection is evaluated coordinatewise and is zero
because `a(s)` is satisfying.  Shared separator occurrences agree
coordinatewise because all four contexts use the same chosen `s`.

Direct sums preserve every group equation used only to copy, conjugate, or
match these diagonal signs.  Tensoring an independent packet preserves them
as well.  This proves the construction and the stated marginal-only no-go.
It does not impose the algebraic identities among the prescribed machine
words; those identities are exactly the possible source of a nonflat return
left open in the claim.

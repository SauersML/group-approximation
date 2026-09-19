---
rg: 2
id: non-mf-overgroup-with-nonkazhdan-quotient-proof
kind: route
title: Restrict an MF embedding to the subgroup and pass Property T to the quotient
target: non-mf-overgroup-with-nonkazhdan-quotient
requires: []
---

If `G` were operator-MF, restricting a faithful norm-corona representation
to `B<=G` would make `B` operator-MF, a contradiction.  If `G` had Property
`(T)`, its quotient `A` would have Property `(T)`, again a contradiction.

For the direct product use the subgroup `B x {1}` and the quotient onto
`A`.  For the free product use the canonical copy of `B` and kill that
factor to obtain the quotient onto `A`.  Standard finite presentations for
direct and free products prove the final finiteness assertions.

The proof literally invokes the already established non-MF theorem for
`B`; wrapping `B` cannot erase any assumptions in that theorem's dependency
cone.

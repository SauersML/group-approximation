---
rg: 2
id: nonresidual-sofic-module-envelope-proof
kind: route
title: Pull back the regular module of a simple amenable quotient
target: nonresidual-linear-module-can-give-a-sofic-envelope
requires: []
---

Choose a finitely generated recursively presented infinite simple amenable
group `Q` and an epimorphism `F->Q` from a finite-rank free group.  Let
`A=F_p[Q]` with its regular action pulled back to `F`.  It is cyclic, and
enumerating `(n-1)delta_1=0` for `n` in the recursively enumerable kernel
gives a recursive module presentation.

For `q!=1`, `a=delta_q-delta_1` is nonzero but dies in every finite invariant
module quotient: the induced map `Q->GL(V)` is trivial, since a nontrivial
map from infinite simple `Q` to a finite group would be injective.  The same
element dies in every finite quotient of `A semidirect F`, proving both
nonresiduality assertions.

If `N=ker(F->Q)`, then

```text
1 -> A times N -> A semidirect F -> Q -> 1.
```

The kernel is sofic (`A` amenable, `N` free) and the quotient is amenable.
Closure of soficity under extensions with amenable quotient proves the
semidirect product sofic.

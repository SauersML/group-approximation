---
rg: 2
id: stw95-nuclear-range-cross-k1-counterexample-proof
kind: route
title: Realize a nuclear Cu(Z) factor whose cross K1 class becomes compact
target: stw95-cu-z-tensor-counterexample
requires: []
---

Use the range theorem for the Elliott invariant to choose a separable unital
simple infinite-dimensional nuclear Z-stable UCT C*-algebra `E` with

```text
(K_0(E),K_0(E)_+,[1_E])=(Z,N_0,1),
K_1(E)=Z,
T(E)={tau},
rho_E(n)(tau)=n.
```

This is admissible range data: `(Z,N_0,1)` is a simple scaled ordered group,
the one-point simplex has the displayed faithful pairing, and `K_1` may be
any countable abelian group.  The resulting algebra is not elementary since
its `K_1` is nonzero.

The algebra `E` has stable rank one.  Hence its projection monoid is
cancellative and embeds into `K_0(E)`.  The specified ordered group gives

```text
V(E)=N_0.
```

Nuclearity identifies quasitraces with traces, so `QT(E)` is a point.
The standard Cuntz-semigroup formula for a simple unital stably finite pure
algebra therefore yields

```text
Cu(E)
 = V(E) disjoint_union LAff(QT(E))_(strictly positive)
 = N_0 disjoint_union (0,infinity]
 = Cu(Z).
```

Now set `F=E tensor_min E`.  Nuclearity makes `F` simple, and Z-stability
passes to `F`; thus `F` is again stably finite and of stable rank one.  Since
`E` is nuclear and satisfies the UCT, the Kunneth exact sequence applies.
All its `Tor` terms vanish because both K-groups of `E` are free.  Its even
part is therefore

```text
K_0(F)
 = (K_0(E) tensor K_0(E)) direct_sum (K_1(E) tensor K_1(E))
 = Z direct_sum Z
 = Z^2.
```

Stable rank one identifies the compact elements of `Cu(F)` with `V(F)`, and
their Grothendieck completion is `K_0(F)=Z^2`.  By contrast, the compact
elements of `Cu(Z)` form `N_0`, whose Grothendieck completion is `Z`.
Every Cu-isomorphism preserves the way-below relation and hence compact
elements.  Thus no isomorphism `Cu(F)=Cu(Z)` can exist.

This proof also isolates a reusable obstruction.  Whenever stable-rank-one
factors have `Cu=Cu(Z)` but a Kunneth cross term makes the tensor product's
`K_0` noncyclic, the tensor product cannot again have Cuntz semigroup
`Cu(Z)`.  Ordinary `Cu` has forgotten precisely the odd K-theory that creates
this new compact branch.

---
rg: 2
id: genuine-hnn-switches-over-amenable-bases-sigma1-proof
kind: route
title: Separate ascending HNN extensions from tree ping-pong and pass mapping tori to the stable quotient
target: genuine-hnn-switches-over-amenable-bases-are-sigma1
requires: []
---

Fix one index and suppress it.  Let `T` be the Bass--Serre tree of

```text
P=<B,t | t^-1 H t=K>.
```

If `H=B`, the relation identifies `B` with `K<=B`.  The normal
subgroup

```text
N=union_(n>=0) t^n B t^-n
```

is a directed union of conjugates of the amenable group `B`, and the
exponent-sum map gives `P/N~=Z`.  Hence `N` and then `P` are
amenable.  If `K=B`, apply the same argument with `t^-1`.

Assume now that `H` and `K` are both proper.  Let `v` be the vertex
fixed by `B`, and let `L` be the axis of `t`.  The stabilizers inside
`B` of the two edges of `L` incident to `v` are `H` and `K`,
up to interchanging the orientation.  A group is never the union of two
proper subgroups, so choose `b in B\(H union K)`.  Then `b` fixes
`v` but moves both incident edges of `L); consequently the axes `L`
and `bL` meet only at `v`.  Tree ping-pong applied to sufficiently
large positive powers of `t` and `b t b^-1` gives a nonabelian free
subgroup.  Thus `P` is nonamenable, proving `(GHS2)`.

For the complexity assertion write `X={x_1,...,x_d}`.  Equality `H=B`
holds exactly when there are words `u_i(h_1,...,h_r)` and finite van
Kampen derivations over `<X|R>` of

```text
x_i=u_i(h_1,...,h_r), 1<=i<=d.
```

This is one finite recursively checkable certificate, so `H=B` is
`Sigma^0_1`.  The same holds for `K=B`, and finite union gives
`(GHS3)`.

Finally let `phi:B->B` be arbitrary and put
`K_infty=union_(n>=0)ker(phi^n)`.  The kernels are increasing, and
`phi` descends to an injective endomorphism `bar(phi)` of
`bar(B)=B/K_infty`: if `phi(b)` lies in `K_infty`, then
`phi^(n+1)(b)=1` for some `n`, so `b in K_infty`.

Equivalently, form the direct limit

```text
D=colim(B --phi--> B --phi--> ...).
```

The kernel of the initial map `B->D` is exactly `K_infty`, the shift of
stages is an automorphism `alpha` of `D`, and the universal properties
give

```text
M(B,phi) ~= D semidirect_alpha Z.
```

Every stage image in `D` is a quotient of the amenable group `B`, so
`D` is amenable as a directed union.  Extension by `Z` proves that
`M(B,phi)` is amenable and shows exactly why noninjectivity cannot create
the required free negative branch.

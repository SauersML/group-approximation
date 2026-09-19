---
rg: 2
id: steinberg-separated-support-firewall-proof
kind: route
title: Compute the deleted-vertex cycle spaces and the matching restriction map
target: steinberg-separated-support-imposes-only-matching-zeros
requires:
  - steinberg-x-row-splits-zero-marginal-tree-sectors
  - steinberg-zero-marginal-space-is-biaffine-circulation
---

The biaffine graph has `p^3` edges and `2p^2` vertices.  Deleting the `p`
point vertices with `a=1/2` removes `p^2` edges and leaves a connected graph,
so

```text
dim W_P=(p^3-p^2)-(2p^2-p)+1
       =p^3-3p^2+p+1.                                  (SSPF4)
```

The line calculation gives the same dimension for `W_L`.  Deleting both
vertex sets removes `2p^2-p` edges, because their `p` common edges are the
matching `M`.  To see that the remaining graph is connected, put

```text
x=a-1/2,                 y=b-a,                 m=c-1.
```

Surviving point and line fibers have `x!=0` and `m!=0`, and a two-edge move
between point vertices is

```text
(x,y) -> (x',y+(x'-x)m).                               (SSPF5a)
```

Choose `x'!=x`.  Going to `x'` with `m_1!=0` and back with `m_2!=0` changes
`y` by `(x'-x)(m_1-m_2)`.  Over every odd field, differences of two nonzero
elements exhaust the field, including when `p=3`.  Thus one may change `y`
arbitrarily at fixed `x`, and then change `x`; every surviving point is
connected, and every surviving line is incident to such a point.  Therefore

```text
dim(W_P intersect W_L)
 = (p^3-2p^2+p)-(2p^2-2p)+1
 = p^3-4p^2+3p+1.                                     (SSPF5)
```

Dimension addition now gives

```text
dim(W_P+W_L)=p^3-2p^2-p+1=dim W-p.                    (SSPF6)
```

On the other hand, deleting only the matching edges leaves the graph
connected.  For each `e in M`, join its endpoints by a path avoiding `M`;
that path together with `e` is a circulation whose restriction to `M` is
the basis vector at `e`.  Hence `res_M:W -> F_p^M` is onto, its kernel has
the dimension in `(SSPF6)`, and both `W_P,W_L` lie in that kernel.  This
proves `(SSPF2)`.

For completeness, the two chord summands away from their zero hyperplanes
are

```text
T_1f=f(a/d,b/d,cd+2b)-f(1/(2d),b/d,cd+2b), d=1-2a,
T_2f=f(4(a-b),2b,c/[2(1-c)])
     -f(4(a-b),2a,1/[2(1-c)]).                        (SSPF7)
```

Expanding `(T_1+T_2)^nF` and regrouping by its outer letter yields the same
two vectors `T_1F,T_2F`.  The individual words `T_iT_jF` can have tree mass;
only their grouped outer-letter sums are known to be the separated
circulations.  Thus the first tree-sector argument cannot be reapplied word
by word, and bare support iteration supplies no further forbidden slice.

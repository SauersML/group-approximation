---
rg: 2
id: dellm-shortened-core-unique-neighbor-proof
kind: route
title: Peel shortened local-code cores and expand the fully core squares
target: dellm-all-dual-presentation-has-many-unique-neighbors
requires:
  - soundness-unique-neighbors-give-erasure-cleaning
---

Fix `U subset S`.  For a vertex `v`, write `W_v=U intersect S(v)` and let

```text
K_v = union{supp(c): c in C_v, supp(c) subset W_v}.       (DUC1)
```

If `s in W_v minus K_v`, there is `h in C_v^perp` whose restriction to
`W_v` is the unit vector at `s`.  Indeed, the orthogonal complement of the
restricted dual space `C_v^perp|_(W_v)` consists exactly of the restrictions
of local codewords supported in `W_v`; separation by `e_s` proves the claim.
The labelled row `(v,h)` therefore meets `U` exactly at `s`.  Rows selected
for distinct pairs `(v,s)` are distinct.  If `t` is the total number of
unique-neighbor rows and `K=sum_v |K_v|`, then, since every square has four
vertices,

```text
t >= sum_v (|W_v|-|K_v|) = 4|U|-K.                       (DUC2)
```

Let `R={v:K_v is nonempty}`.  Every nonempty `K_v` contains the support of
a nonzero local codeword, hence `|K_v|>=delta r^2`, and

```text
|R| <= 4|U|/(delta r^2).                                 (DUC3)
```

If `t<gamma|U|`, at most `t` squares fail to lie in `K_v` at all four of
their vertices: every non-full square contributes at least one to the
deficit `4|U|-K`.  Hence more than `(1-gamma)|U|` squares are fully core.
Their four boundary edges lie in the graph induced by `R`.  Each Cayley edge
belongs to exactly `r` squares, so

```text
|E(R)| >= 4(1-gamma)|U|/r.                               (DUC4)
```

Combining `(DUC3)`--`(DUC4)`, the induced average degree on `R` is at least
`2 delta r(1-gamma)`.  The Alon--Chung bound in the `2r`-regular
one-skeleton gives

```text
|R|/|G| >= delta(1-gamma)-lambda.                        (DUC5)
```

Since `|S|=r^2|G|/4`, `(DUC3)` and `(DUC5)` imply

```text
|U|/|S| >= delta(delta(1-gamma)-lambda)=alpha,
```

contradicting the assumed size of `U`.  This proves `(DAU1)`.

Finally, every rejected local view violates some row in `C_v^perp`.
DELL​M tester soundness says
`wt(x+C)/|S| <= kappa^(-1) #reject/|G|`; labelled rows give
`#reject<=wt(Hx)`, proving `(DAU2)`.  The abstract SUN theorem then supplies
the asserted common erasure cleaner.

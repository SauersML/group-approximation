---
rg: 2
id: left-partners-lie-in-collision-universes
kind: claim
title: A one-sided partner of a fixed group-algebra element can be taken inside its collision universe
distinct_from:
  eleven-term-s0-lift-has-no-radius-four-left-inverse: that is a finite fence by Cayley-ball radius around one lift; this is the general reduction that replaces radius by collision depth, which is exhaustive for every partner and reaches word lengths far beyond any feasible ball.
  subgroup-supported-one-sided-inverse-rigidity: that excludes partners of an element supported in a directly finite subgroup, whatever their support; this constrains where any partner of any element can live, with no finiteness hypothesis on a subgroup.
  dykema-heister-juschenko-bounded-rank-direct-finiteness: that kills one-sided pairs of small support sizes over every group; this bounds the support location of a partner of one fixed element, not its size.
---

**ESTABLISHED.** Let `k` be a field of characteristic two, `G` a group and
`A` in `k[G]` with finite support. Suppose `B A = 1` for some `B` in `k[G]`.
Then there is `B_0` with `supp B_0` contained in `supp B`, `B_0 A = 1`, and

```text
supp B_0  in  A^(-1) (A A^(-1))^r        for some r < |supp B_0|,
```

where `A^(-1) = {a^(-1) : a in supp A}` and products of subsets are taken in
`G`. Dually, if `B A = 1` with `B` fixed, some sub-partner of `A` lies in
`(B^(-1) B)^r B^(-1)`.

So for a fixed `A` the left partners are exhausted by the increasing finite
sets `U_r = A^(-1) (A A^(-1))^(<= r)`, and each test `1 in span{u A : u in U_r}`
is exact Gaussian elimination over `F_2`. The same holds over any field once
coefficients are carried.

## Use

- For a lift `A` of the non-unit `s_0` of `L_(F_2)(1,2)`, any partner is a
  strict pair, so a hit at any depth refutes Kaplansky direct finiteness and
  Gottschalk surjunctivity through `leavitt-direct-finiteness-failure-from-left-invertible-lift`.
- A miss at depth `r` excludes every partner whose collision graph reaches all
  its vertices within `r` steps of an identity-producing root. It is a fence,
  not a no-go.
- The universe at depth `r` reaches word length `(2r+1)` times the radius of
  `supp A`, far beyond any feasible Cayley ball. This is the measurement
  `eleven-term-s0-lift-has-no-radius-four-left-inverse` asks for: grow the
  partner universe by multiplication-collision class, not by word length.

Proof: [[left-partners-collision-universe-proof]].

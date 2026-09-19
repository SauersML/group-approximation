---
rg: 2
id: directed-unions-preserve-trace-approximations-proof
kind: route
title: Extend one stage u.c.p. approximation and control a nearby ambient finite set
target: directed-unions-preserve-trace-approximations
requires: []
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Restriction of a u.c.p. approximation on `A` to a unital subalgebra proves
both forward implications.

Conversely, fix a finite set `F` in the unit ball of `A` and `epsilon>0`.
Choose one index `i` and contractions `a_x in A_i`, for `x in F union F^2`,
so close to their indexed ambient elements that all trace and product errors
introduced below are below `epsilon/4`.  Choose a u.c.p. map

```text
phi_i:A_i -> M_k
```

which recaptures `tau|A_i` on these elements and is approximately
multiplicative on the required pairs, in normalized Hilbert--Schmidt norm for
amenability and in operator norm for quasidiagonality.

Arveson's extension theorem extends `phi_i` to a u.c.p. map
`phi:A -> M_k`.  Contractivity of `phi` and of the matrix trace gives

```text
|tr(phi(x))-tau(x)|
 <= |tr(phi(a_x))-tau(a_x)| + 2||x-a_x||.
```

For `x,y in F`, insert `a_x,a_y,a_{xy}` and use
`||uv||_2<=||uv||` to obtain

```text
||phi(xy)-phi(x)phi(y)||_star
 <= ||phi(a_{xy})-phi(a_x a_y)||
    + ||phi(a_x a_y)-phi(a_x)phi(a_y)||_star
    + O(||x-a_x||+||y-a_y||+||xy-a_{xy}||),
```

where `star` is either normalized `2`-norm or operator norm.  The first term
is controlled by contractivity and the choice of approximants, the second by
the stage hypothesis, and the remaining terms by the displayed errors.
Thus the ambient finite-set approximation exists in either norm.

For the final consequence, write `A` as the directed union of its separable
unital subalgebras.  Amenability restricts to each one.  If every restriction
were QD, the proved converse would make `tau` QD on `A`; contraposition gives
a separable counterexample subalgebra.

**Trust boundary.**  Only Arveson's u.c.p. extension theorem is imported.
The finite-set error argument is explicit and uses no exactness, quotient
lifting, or ultraproduct characterization.

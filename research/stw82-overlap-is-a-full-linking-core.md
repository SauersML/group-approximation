---
rg: 2
id: stw82-overlap-is-a-full-linking-core
kind: claim
title: The unresolved multiplier overlap is a full linking core with two residual diagonal quotients
distinct_from:
  stw82-complement-symmetry-and-overlap-reduction: that theorem identifies the overlap ideal and the quotient after removing it; the present theorem computes every Peirce corner and shows exactly where linking-algebra colour transport stops.
  stw82-split-af-is-one-multiplier-projection-problem: that reduction presents the problem as adjoining one projection; the present normal form presents the same remainder as partial unitization of one diagonal in a generalized linking algebra.
artifacts:
  - research/artifacts/stw82-overlap-linking-core-audit-2026-08-30.md
---

Retain the genuinely two-sided situation from
`stw82-complement-symmetry-and-overlap-reduction`: `p,q=1-p` are multiplier
projections outside `A`, both support ideals

```text
L=closure(ApA),       R=closure(AqA)
```

are proper, and `I=L intersect R` is nonzero.  Put

```text
P=pAp,       Q=qAq,       X=pAq,
B=pIp,       C=qIq.
```

Then

```text
X=pIq,
B=closure(XX*),       C=closure(X*X).                    (OLC1)
```

Thus `X` is a full `B`--`C` imprimitivity bimodule and

```text
I = [ B   X  ]
    [ X*  C  ]                                           (OLC2)
```

is its linking algebra.  The two support ideals and the original algebra
have the exact compatible forms

```text
L = [ P   X  ]       R = [ B   X  ]       A = [ P   X  ]
    [ X*  C  ],          [ X*  Q  ],          [ X*  Q  ]. (OLC3)
```

Adjoining `p` does only one thing:

```text
A+C p = [ P~  X  ],                                      (OLC4)
          [ X*  Q  ]
```

where `P~=P+C p` is the minimal unitization of `P`.  The residual diagonal
quotients are

```text
P/B isomorphic to A/R,
Q/C isomorphic to A/L.                                  (OLC5)
```

This is a sharp linking-algebra reduction of the open case: partially
unitize one diagonal of a generalized linking algebra whose off-diagonal
module is full only on the common core ideals `B,C`.

It also gives an exact firewall against the naive full-corner proof.  Every
finite frame expression from `X` satisfies

```text
sum_j xi_j xi_j* in B,       sum_j xi_j* xi_j in C.      (OLC6)
```

Hence such frames can transport nuclear-dimension colours between `B` and
`C`, and therefore across `I`, but they cannot approximate any element of
`P` or `Q` whose image in `P/B` or `Q/C` is nonzero.  Quantitatively, for a
positive contraction `e in B` and `y in P`,

```text
||y-eye|| >= ||y+B||_(P/B),                              (OLC7)
```

and symmetrically on `Q/C`.  Thus fullness of both complementary
projections on `I` is not by itself fullness on `A+C p`; a valid maximum
proof must couple the two residual diagonal approximations to the same core
colours.  Morita invariance of the overlap alone cannot do so.

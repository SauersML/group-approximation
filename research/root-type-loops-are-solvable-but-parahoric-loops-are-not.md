---
rg: 2
id: root-type-loops-are-solvable-but-parahoric-loops-are-not
kind: claim
title: Root-type loop holonomy is solvable, but parahoric-carrier holonomy need not be amenable
distinct_from:
  shortest-second-denominator-return-has-coweight-holonomy: That computes one shortest root-type loop and finds a diagonal coweight holonomy; this classifies every exact root-type loop and then exhibits the first failure for the weaker parahoric-carrier notion.
  first-root-parahoric-target-has-a-distinct-double-coset-type: That computes the shortest A2 section holonomy `x_23(2)`; this proves structurally why it lies outside the root normalizer and refutes a blanket amenable-holonomy classification.
  native-parahoric-triangle-kills-all-corrector-gauges: That kills a common supported corrector using several translated triangles; this explains why one parahoric return may already have nonamenable internal holonomy yet remains uncharged without path interference.
---

# Every exact root-type return lies in a solvable normalizer

Let

```text
U_12={x_12(t):t in Q[1/2]} < SL_3(Q).                  (RTL1)
```

If two native paths `T_0,T_1` both return this root subgroup to the same
root subgroup, their relative holonomy

```text
g=T_1T_0^(-1)                                         (RTL2)
```

lies in `N(U_12)`.  If they return every parameter with the same labeling,
then `g` lies in `C(U_12)`.

This normalizer is solvable.  Write `N=E_12`.  The relation

```text
g(I+tN)g^(-1)=I+phi(t)N                                (RTL3)
```

for nonzero `t` implies that `gNg^(-1)` is a scalar multiple of `N`.
Consequently `g` preserves both

```text
im(N)=span(e_1),
ker(N)=span(e_1,e_3).                                  (RTL4)
```

Thus `N(U_12)` is contained in the stabilizer of the complete flag

```text
span(e_1) subset span(e_1,e_3),                        (RTL5)
```

a Borel subgroup of `SL_3(Q)`.  Borel subgroups are solvable, so every
discrete arithmetic subgroup of this normalizer is amenable.  Weyl
conjugacy gives the same conclusion for every root.

This proves the structural classification for **root-type** loops, with no
bounded-length hypothesis.  The coweight holonomy
`diag(2,2,1/4)` found in
`shortest-second-denominator-return-has-coweight-holonomy` is the expected
diagonal part of this solvable normalizer.  Root unipotent and diagonal
parts admit the same amenable/Folner escape unless an additional relation
authenticates a literal stationary carrier.

# The analogous parahoric statement is false at length two

A parahoric-carrier return is weaker.  Two section paths ending at the same
point of `C/D` differ by an element of `D`, not by an element of one root
normalizer.  The group `D` has finite index `42` in `SL_3(Z)` and is
nonamenable (indeed it has property `(T)`).

The shortest A2 section loop already witnesses the failure.  With

```text
u=x_12(1),             d=x_23(2) in D,                 (RTL6)
```

the two paths `udu^(-1)` and `x_13(2)` have relative holonomy `d`.  But

```text
d u d^(-1)=u x_13(plusOrMinus 2) notin U_12,           (RTL7)
```

so `d notin N(U_12)`.  This is a length-two holonomy outside the amenable
root stabilizer, refuting the proposed classification as soon as
"parahoric type" is included.

Nonamenability of `D` does not by itself charge this loop.  The native base
projection `P` commutes with `D`, so `d` acts as an internal corner unitary;
the ordinary product word is allowed to remain canonically trace-separated
from the identity.  As shown in
`native-a2-two-path-average-is-not-an-ordinary-word-compression`, a payment
appears only after the two transports interfere in one authenticated Gram
block.  A monomial group relation merely names `d` and produces no defect.

Hence the correct final classification is a dichotomy:

```text
exact root-type return
  -> solvable root normalizer -> amenable carrier drift;

parahoric endpoint return
  -> possibly nonamenable D-holonomy,
     but no payment without same-carrier path interference.              (RTL8)
```

Literal carrier authentication (or an equivalent noncentral additive
wordization) is unavoidable in both cases, but not because all native
holonomies are amenable.


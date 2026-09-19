---
rg: 2
id: endpoint-external-order-four-is-conditional-s3-breaker
kind: claim
title: The endpoint Whitehead and active external return have an exact order-four S3 breaker
artifacts:
  - experiments/endpoint_external_weyl_order_audit.py
  - research/endpoint-external-order-four-s3-breaker-proof.md
distinct_from:
  native-weyl-return-gauges-have-s3-model: that leaves the constant root-position Weyl gauge and the active external-return gauge as two reflections with product of order three; this supplies a literal endpoint/external word whose order is four and proves that it kills that model as soon as the endpoint and constant-Weyl occurrences are identified on one carrier.
  endpoint-order-five-actor-has-half-gram: that uses the endpoint Whitehead with the second Singer head and obtains a positive endpoint Gram; this uses the same endpoint Whitehead directly with the active external root and isolates the strictly smaller missing occurrence bridge.
  eight-external-returns-have-no-whitehead-gauge-lock: that exhausts the two native prefix Whiteheads and all eight returns; this uses the different endpoint Whitehead and then proves why its new global relation still does not apply before a common-carrier identification with the constant Weyl occurrence.
---

**ESTABLISHED CONDITIONAL BREAKER AND EXACT SCOPE FENCE.**  Put

```text
n=x_78(1),                 m=x_87(1),
w=nmn=w_78(1),             P=What_(8,2;2).             (EOF1)
```

Here `P` is the literal endpoint Whitehead used in the order-five actor,
whereas `w` is the constant root-position Weyl word in the surviving native
`S_3` gauge model.  Faithful sparse Leavitt multiplication gives the ordinary
elementary-group relations

```text
(Pn)^4=(Pm)^4=1,                 (Pw)^6=1,             (EOF2)
```

and all three displayed orders are exact: they are respectively `4,4,6`.
In particular `(Pn)^4=1` is a Coxeter length incompatible with the old
order-three holonomy.

Indeed, let `D,E,F` be the reservoir factors of `w,n,m` in the native cell.
That cell gives

```text
D=EFE,                 F=DED,                 (DE)^3=1. (EOF3)
```

Let `H` be the reservoir factor of `P`.  On any common reducing homogeneous
carrier on which the fixed label packet inherits `(EOF2)`, the first row of
`(EOF2)` gives

```text
(HE)^4=1.                                             (EOF4)
```

Consequently an occurrence identification

```text
H=D                                                    (EOF5)
```

immediately yields `(DE)^4=1`.  Together with `(DE)^3=1` this forces
`DE=1`, hence `D=E`; then `(EOF3)` gives `F=D` as well.  Thus `(Pn)^4=1`
is an ordinary, dimension-independent same-carrier relation which kills the
surviving three-reflection model.  It is smaller than the endpoint
order-five cycle and needs no commutation relation.

The bridge `(EOF5)` is not supplied by the current interface.  The endpoint
star braids synchronize `P` with the two **prefix** Whiteheads `J_1,J_2`,
whereas `D` in `(EOF3)` belongs to the distinct constant Weyl word
`w_78(1)`.  The known root-position naturality squares transport these two
occurrences between charts but do not identify their reservoir factors.

This distinction is exact.  The combined scoped interface consisting of

1. the native `w,n,m` cell and all eight external-return/naturality rows;
2. the endpoint star-braid and internal `P,M` actor rows, including
   `P^2=M^7=(PM)^5=1`; and
3. the new cross-order rows `(EOF2)`

still has a finite reservoir model.  Use the old reflections

```text
D=(1 2),                 E=(2 3),                 F=(1 3) (EOF6)
```

for `w,n,m`, extend the eight-return rows as in
`eight-external-returns-have-no-whitehead-gauge-lock`, and give `P`, `M`,
both prefix-Whitehead **restrictions on the endpoint chart**, and their
endpoint factors identity reservoir gauge.  The external-return chart keeps
the nontrivial Whitehead restrictions from the old `S_3` model; the current
interface contains no positive reducing identification of those restrictions
with the endpoint-chart copies.
Then `(HE)^4=E^4=1`, `(HF)^4=F^4=1`, and `(HD)^6=D^6=1`; every endpoint
relator and star braid is exact, while `DE` remains a nonidentity
three-cycle.  Transported target occurrences are assigned their literal
conjugate gauges as before.

Therefore the smallest endpoint/external closure does contain the desired
incompatible order, but it closes the `S_3` seam **if and only if one adds
the missing same-carrier occurrence bridge between `P` and `w_78(1)`**.
Searching for another endpoint order relation is unnecessary at this level;
the live task is to authenticate `(EOF5)` on positive signed-Hecke mass.

This is a scoped occurrence-interface model, not a representation of the
full elementary group with independently assigned root factors.  No
Property `(T)`, Kazhdan input, trace profile, stability theorem, literature
result, or local computation is used.

DERIVATION
endpoint-external-order-four-s3-breaker-proof

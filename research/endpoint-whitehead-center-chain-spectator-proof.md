---
rg: 2
id: endpoint-whitehead-center-chain-spectator-proof
kind: route
title: Commute the endpoint braid through the nested center-chain flags
target: endpoint-whiteheads-are-center-chain-hecke-spectators
requires:
  - endpoint-detector-cell-retains-coboundary-gauge
  - center-chain-hecke-polar-supports-are-nested-pauli-flags
  - spectator-dressed-gram-does-not-share-selector-gauges
  - fixed-center-chain-hecke-occurrence-is-regularly-impossible
---

For `m=1,2`, write

```text
c_m=s_(0^(m+1))t_(0^m),       d_m=s_(0^m)t_(0^(m+1)).
```

The first endpoint Whitehead uses only coordinates `10,11`, so it is
disjoint from every root occurring in `e,p_1,p_2,A_1,A_2`.  The second uses
coordinates `11,2`.  Its only possible interaction with the center-chain
group

```text
H=<x_65(q),x_54(q),x_42(q)>
```

is between `x_42(q)` and the factor `x_(2,11)(c_2)`.  But

```text
q c_2=s_1t_1s_000t_00=0,                              (1)
```

so the Steinberg commutator is trivial.  The reverse endpoint factor has
the same column `2` as `x_42(q)` and commutes directly.  All other pairs are
index-disjoint.  Therefore both endpoint Whiteheads centralize `H` and its
character atom `e`.

The elementary abelian flag groups

```text
<x_57(a_1),x_67(a_1)>
  <= <x_57(a_1),x_67(a_1),x_68(a_2)>
```

and the arms `x_47(a_1),x_58(a_2)` use none of `10,11,2`, so they also
commute with both endpoint words.  This proves commutation with `p_i,T_i`.

Now `p_2<=p_1`.  Using the commutations just proved,

```text
R_1^*R_2
 =p_1What_1^(-1)What_2p_2
 =What_1^(-1)What_2p_2.
```

Multiplying by its adjoint gives `p_2`, proving `(EHS4)` and its trace by
the established Hecke flag calculation.

Finally the endpoint Coxeter relations act entirely in the commutant of the
Hecke flag algebra.  Tensoring its canonical regular representation with
the left regular representation of `S_3` therefore realizes all displayed
relations while keeping both endpoint reservoir involutions nontrivial.
The abstract dressing fence applies verbatim to `(EHS5)`, and the fixed
regular-corner firewall excludes promoting this spectator Gram to the two
native affine rows.  This proves the claim.

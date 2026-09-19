---
rg: 2
id: endpoint-whitehead-profile-gram-proof
kind: route
title: Compute the complete Grams of the endpoint-prefix profile
target: endpoint-whitehead-profile-has-maximal-gram-overlap
requires:
  - middle-pauli-probes-leave-three-hecke-classes-untyped
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
---

Write

```text
c_m=s_(0^(m+1))t_(0^m),        d_m=s_(0^m)t_(0^(m+1)).
```

Prefix cancellation gives

```text
c_md_m=e_(m+1),   d_mc_m=e_m,
a_md_m=a_(m+1),   c_mb_m=b_(m+1).                    (EPG1)
```

The ordinary three-elementary partial Whitehead word on the coordinates
`r_m,r_(m+1)` therefore conjugates `A_m,B_m` to
`A_(m+1),B_(m+1)`.  The reverse conjugations and braid calculation are the
same Steinberg calculation as for the original same-center prefix
Whiteheads.  Also

```text
a_mb_m=s_1t_(0^m)s_(0^m)t_1=s_1t_1,
```

so every paired endpoint occurrence returns `z`.

Now let `U_i` denote the two adjacent Whitehead unitaries in any exact
matrix realization of this finite occurrence table, and let `U_h` be their
product for `h in S_3`.  Define `Q_h=U_hQU_h^*`.  For an edge
`h -> s_i h`,

```text
T_(i,h)=Q_(s_i h)U_iQ_h=U_iQ_h.
```

The last equality follows from
`Q_(s_i h)=U_iQ_hU_i^*`; taking the two Grams proves `(EWP1)`.

At a fixed target `k`, both incoming transports are surjective isometries
onto `Q_kH`.  Therefore their range projections coincide with `Q_k`.  If
they are regarded as maps from the direct sum of their two source spaces,
the off-diagonal Gram `T_e^*T_f` is a unitary from one source space to the
other.  Hence

```text
(T_e^*T_f)^*(T_e^*T_f)=Q_source(f)
```

and its ambient normalized Hilbert--Schmidt square is `tau(Q_k)`.  Summing
the two range projections gives `2Q_k`, proving `(EWP2)--(EWP3)`.

Finally, on the three-cell Pauli normal form the adjacent label swaps give a
representation of `S_3`.  Tensor it with the left regular representation of
`S_3` on the multiplicity space.  Taking the two reservoir factors to be
the two regular adjacent transpositions satisfies the involution and braid
relations exactly and keeps both factors nontrivial.  In the chart indexed
by `h`, the reservoir identification is `V_h`; the edge factor is therefore
`V_(s_i h)V_h^(-1)`.  Products around relator loops telescope.  This is the
announced exact finite profile model and proves that full-Gram conjugacy
alone does not fix a common reservoir frame.

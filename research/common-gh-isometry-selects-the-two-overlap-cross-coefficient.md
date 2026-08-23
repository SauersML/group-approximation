---
rg: 2
id: common-gh-isometry-selects-the-two-overlap-cross-coefficient
kind: claim
title: One common Gowers--Hatami isometry selects a near-identity cross coefficient for both Kac--Moody overlaps
distinct_from:
  finite-group-shared-overlap-polar-alignment: that aligns two exactifications of one finite subgroup abstractly; this averages one common exactification isometry over two different overlap subgroups and computes their cross coefficient on one large source intersection.
  one-cross-gram-moment-extracts-the-common-polar-gauge: that assumes a large cross-Gram moment; this derives it quantitatively from the common Gowers--Hatami isometry.
  one-state-protected-coefficient-leaves-relative-gh-gauge: that refutes selection from unrelated one-state intertwiners; this proves selection when the normalized-HS exactification supplies one common trace-controlled isometry for both overlaps.
  summed-reynolds-carrier-transports-only-tautologically: that leaves comparison with the independently exactified P_13 coefficient open; this closes that approximate coefficient-selection step and isolates exact simultaneous invariance as the remaining obstruction.
---

**ESTABLISHED.**  Let `H_1,H_3` be finite groups.  For `i in {1,3}`, let

```text
alpha_i:H_i->U(d),        beta_i:H_i->U(m),
```

be exact representations, with `m>=d`, and let the **same** isometry
`V:C^d->C^m` satisfy

```text
eta_i^2=(1/(|H_i|d)) sum_(h in H_i)
 ||beta_i(h)V-Valpha_i(h)||_F^2.                        (CGI1)
```

There are `alpha_i(H_i)`-invariant projections `p_i` and partial isometries
`U_i:C^d->C^m` such that `U_i` exactly intertwines `alpha_i` with `beta_i`
on `p_i`, and

```text
rank(I-p_i)<=4eta_i^2 d,
||U_i p_i-Vp_i||_F<=2eta_i sqrt(d).                     (CGI2)
```

Put `p=p_1 meet p_3`.  Then

```text
rank(p)>=d-4(eta_1^2+eta_3^2)d,                         (CGI3)
||(U_3^*U_1-I)p||_F/sqrt(d)<=2(eta_1+eta_3).            (CGI4)
```

Thus the two overlap comparisons have a canonically selectable cross
coefficient `C=U_3^*U_1` which is near the identity on `1-o(1)` of the common
source whenever both come from one normalized-HS Gowers--Hatami isometry.
If a full-carrier Reynolds polar coefficient satisfies
`||tilde B-I||_2<=epsilon`, then on the same source

```text
||(C-tilde B)p||_F/sqrt(d)
 <=2(eta_1+eta_3)+epsilon.                              (CGI5)
```

A common target multiplicity gauge is irrelevant rather than obstructive:
replacing both `U_i` by `QU_i` leaves

```text
(QU_3)^*(QU_1)=U_3^*U_1                                (CGI6)
```

exactly unchanged.  Hence “choose the identity target gauge” is not the
mechanism; using the same `V` before the two subgroup polar decompositions is
what selects the near-identity coefficient.  Separate state-dependent
dilations need not have this property, as
`one-state-protected-coefficient-leaves-relative-gh-gauge` shows.

Any target generator gauge which remains far after `(CGI4)` is a **common**
left gauge on both overlap maps.  It cancels from every relative coefficient
and may be set to the identity by global conjugacy.  There is therefore no
counterpacket with far relative generator gauge once the common trace-norm
isometry hypothesis is imposed.

This closes the approximate multiplicity-gauge ambiguity for the section
chart.  It does **not** give an exact common overlap intertwiner.  The
intersection `p_1 meet p_3` need not be invariant under either subgroup, and
`U_3^*U_1-I` can be small but full-rank, with no nonzero exact fixed
subspace.  The scalar matrices

```text
C_d=e^(it_d)I_d,        0!=t_d->0,                     (CGI12)
```

are the sharp quarantine countermodel: `||C_d-I||_2->0`, but
`ker(C_d-I)=0`, and restriction to any nonzero subspace still does not make
`C_d` the identity.  Replacing the two near comparisons by one exact map that
intertwines both `H_1` and `H_3` is precisely relative correction for the
group they generate.  In the Kac--Moody triangle that group is `P_13`, and
making the analogous choices simultaneously around all three edges is the
regular-branch stability problem, not a remaining choice of multiplicity
gauge.

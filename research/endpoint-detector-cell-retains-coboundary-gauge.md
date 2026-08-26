---
rg: 2
id: endpoint-detector-cell-retains-coboundary-gauge
kind: claim
title: Endpoint Whiteheads transport the complete detector cell but retain a coboundary gauge
artifacts:
  - research/endpoint-detector-cell-coboundary-proof.md
distinct_from:
  endpoint-whitehead-profile-has-maximal-gram-overlap: that computes the complete Grams of the moved source profile; this adds the actual detector/probe commutator occurrence and proves that it is transported covariantly rather than cutting either incoming range.
  endpoint-whitehead-signed-source-has-only-relative-hecke-overlap: that computes the exact intersection of the original and endpoint-moved signed pairs and gives a zero-meet finite profile; this transports the whole detector cube around all six charts.
  exceptional-endpoint-detector-products-stay-at-depth-three: that closes all products of L0 conjugates of the three exceptional detectors and rules out a fixed-source adjacent-depth pair; this begins with one third-depth cell and moves it covariantly.
  five-return-legs-cover-hecke-detectors-not-source-gauge: that isolates the three depth-three endpoint returns and asks for a fresh endpoint Whitehead; this constructs that Whitehead and audits the extra occurrence information it supplies.
  same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps: that swaps the original middle-index Pauli cells; this swaps endpoint cells whose last member is the literal return extracted from a signed-Hecke detector.
---

**ESTABLISHED OCCURRENCE-LEVEL FENCE.**  Fix the exceptional positive
signed-Hecke class whose deterministic representative in `(MPF4)` is
`(73,2,4,8,16,32,64)`.  Its nonidentity actor entries are
`E_(2,6)+E_(2,9)`, so the literal depth-three dual root gives the single
endpoint ejection below.  Thus, for `r_3=2`, one signed-source
representative `g_3`, and the literal dual-menu word `u_3=Y_3`,

```text
B_3=[g_3,u_3]=x_(r_3,3)(b_3),
A_3=x_(1,r_3)(a_3),                  [A_3,B_3]=z,     (EDC1)
```

where `a_m=s_1t_(0^m)`, `b_m=s_(0^m)t_1` and `a_mb_m=q`.
Choose two spare endpoints `r_1,r_2`, disjoint from the detector/probe
coordinates, and put

```text
A_m=x_(1,r_m)(a_m),                  B_m=x_(r_m,3)(b_m).
```

The fresh partial Whiteheads on `(r_m,r_(m+1))` satisfy

```text
What_m A_m What_m^(-1)=A_(m+1),
What_m B_m What_m^(-1)=B_(m+1),                         (EDC2)
```

and the two involution relations and Coxeter braid.  Define the neighboring
data, in either direction, by conjugation:

```text
g_(m+1)=What_m g_m What_m^(-1),
u_(m+1)=What_m u_m What_m^(-1),
Q_(m+1)=What_m Q_m What_m^(-1).                         (EDC3)
```

Then ordinary commutator covariance gives, with no analytic replacement,

```text
[g_(m+1),u_(m+1)]=B_(m+1),
[A_(m+1),[g_(m+1),u_(m+1)]]=z.                         (EDC4)
```

The fresh endpoint coordinates are disjoint from `Y_3`, so in this
particular occurrence one may take every `u_m=Y_3`.  Moreover `g_m` has
the same signed character on `Q_m` as `g_3` has on
`Q_3`.  Thus the fresh Whiteheads really transport the **whole** detector
occurrence, not only the isolated endpoint Pauli pair.

This additional typing does not produce an unequal selector row.  Every
map between the moved sources is still the full unitary

```text
T_(i,h)=Q_(s_i h) What_i Q_h=What_i Q_h.               (EDC5)
```

Consequently the two incoming ranges at any profile vertex are both the
whole `Q_h`; their cross Gram has squared normalized Hilbert--Schmidt norm
`tau(Q_h)`.  The detector identity `(EDC4)` is carried from one chart to
the next by the same conjugation and supplies no subprojection of either
range.  In particular it does not improve the maximal-overlap equations of
`endpoint-whitehead-profile-has-maximal-gram-overlap`.

On the common `z=-1` carrier the three endpoint pairs form a three-qubit
Pauli factor.  After removing the adjacent label swaps, the two endpoint
Whiteheads still have reservoir factors `V_1,V_2` satisfying only the
`S_3` involution and braid relations.  For an exact scoped model, take six
copies of a seed endpoint-cell space indexed by `h in S_3`, put on the
`h`-block the conjugated detector, probe, source and endpoint data from
`(EDC3)`, and let the adjacent Whiteheads permute the blocks by the left
regular action while applying their fixed label swaps.  This gives
nontrivial regular `V_1,V_2` and realizes all equations `(EDC1)--(EDC5)`.
Their chart gauges are the exact coboundaries
`V_(s_i h)V_h^(-1)` and telescope around every profile loop.

Therefore the fresh endpoint Whiteheads solve the algebraic
same-reservoir **transport** problem only in a moving frame.  They do not
lock that frame to `Q`, to the paid cut, or to the prescribed quarter/eighth
Hecke targets.  A continuation needs an additional ordinary occurrence
which produces proper unequal subranges or a nonmaximal cross Gram in one
fixed source frame; another conjugate copy of `(EDC4)` cannot do so.

The comparison with the original source is now exact as well.
`endpoint-whitehead-signed-source-has-only-relative-hecke-overlap` computes
`L_0 intersect What_iL_0What_i^(-1)`: it is only the subgroup isolating the
moved actor endpoint, of order `256` at endpoint `2` and `512` at endpoint
`4`.  The resulting canonical Hecke overlaps `tau(Q)/32` and `tau(Q)/16`
do not give arbitrary-profile meet mass.  A two-character finite profile
has `Q` and `What_iQWhat_i^(-1)` orthogonal while satisfying the complete
intersection table.  Thus even comparing one moved chart directly with
the original chart leaves the same fixed-frame seam.

Multiplying the original exceptional detectors does not create the missing
second cell before the source is moved.
`exceptional-endpoint-detector-products-stay-at-depth-three` closes all
products of their `L_0` conjugates to a positive elementary abelian group of
order eight.  Every endpoint entry of every element lies in the third
native middle column; the first two columns are identically zero.  Hence no
one positive actor on the fixed `Q` has adjacent mark-return depths.  The
fresh Whitehead remains necessary to create the earlier cells, and then the
coboundary fence of this claim applies.

This is a scoped exact finite-occurrence fence, not a finite-dimensional
representation of the full Steinberg group.  No Property `(T)`, canonical
trace, literature theorem, local computation, or Lean compilation is used.

DERIVATION
endpoint-detector-cell-coboundary-proof

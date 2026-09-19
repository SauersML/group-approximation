---
rg: 2
id: dihedral-soft-mode-proof
kind: route
title: Represent two separated Tanner sectors by nearby planar reflections
target: tanner-separated-codewords-create-dihedral-soft-mode
requires: []
---

Because `c` is a codeword, every parity face contains an even number of
coordinates from `supp(c)`; the same holds for `d`.  By `(DSM2)`, all
nonidentity images in one face are copies of only `s` or only `t`.
They therefore commute, and their product is the identity.  This proves the
surjection `(DSM3)`; it is onto because both supports are nonempty.

For the stated equivalence, `(DSM1)`--`(DSM2)` make the support incidence
of `c+d` the disjoint union of the nonempty `c` and `d` parts.  Conversely,
let one codeword `ell` have a disconnected support component `S`.  No face
meeting `S` meets the complementary support component.  Since every face
meets `supp(ell)` evenly, every face meets `S` evenly as well.  Hence the
indicator of `S` is itself a codeword, as is `ell+1_S`; these are a pair
satisfying `(DSM1)`--`(DSM2)`.

For `0<theta<pi/2`, the two balanced reflections `S,T_theta` have no common
eigenline, so the algebra they generate is `M_2` and its commutant is the
scalars.  With normalized trace, `tr(S)=0` and `||S||_2=1`, hence

```text
dist_2(S,{lambda I})^2=1.                                (DSP1)
```

Every face supported outside `supp(d)` has an algebra commuting with `S`,
so its pinching fixes `S`.  A face meeting `supp(d)` has face algebra
`span{I,T_theta}`, and its pinching is

```text
Phi_theta(X)=(X+T_theta X T_theta)/2.                     (DSP2)
```

Therefore

```text
||S-Phi_theta(S)||_2
 <= ||S-T_theta S T_theta||_2/2
 <= ||S-T_theta||_2
 = O(theta).                                              (DSP3)
```

Since a pinching is an orthogonal projection,
`<S,(I-Phi_theta)S>=||S-Phi_theta(S)||_2^2`.  Averaging over
all faces proves `(DSM5)`, regardless of how many faces meet `supp(d)`.

For the complete overlay, pairs outside
`supp(c) x supp(d)` commute.  On a cross pair,

```text
||[S,T_theta]||_2 <= 2||S-T_theta||_2=O(theta),           (DSP4)
```

so its average squared energy is `O(theta^2)`.  Finally, replacing
`T_theta` by `S` changes each affected coordinate by `O(theta)`, proving
the stated square-root-compatible rounding and showing exactly why this
example refutes the gap but not the decoder.

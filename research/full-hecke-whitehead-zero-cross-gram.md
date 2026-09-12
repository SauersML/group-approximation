---
rg: 2
id: full-hecke-whitehead-zero-cross-gram
kind: claim
title: Paid full-Hecke native supports and synchronized Whitehead gauges still allow orthogonal ranges
invalidates:
  - full-hecke-support-plus-whitehead-sync-proves-native-cross-gram
distinct_from:
  b2-b3-pair-full-hecke-four-native-sectors: that proves the two literal source supports have the four-sector quarter geometry; this exact interface model has that geometry and nevertheless makes the mixed target Gram zero.
  endpoint-whitehead-star-braid-synchronizes-native-gauges: that proves the three literal reservoir gauges obey the Whitehead braid; this model obeys the same braid and shows synchronized gauge spectra do not identify the target occurrences.
  binary-leavitt-native-two-scale-cross-gram-positive: that quantifies over full canonical-trace microstates of the binary-Leavitt group; this is a finite interface countermodel refuting one proposed implication, not the full claim.
---

**ESTABLISHED MIXED-GRAM FIREWALL.**  There is a canonical finite-group
regular model with all of the following features:

1. the two paid native source supports each occupy one half of `Q` and their
   intersection occupies one quarter;
2. the full-Hecke target/source capacity ratio is exactly `16:1`;
3. the three Whitehead actors satisfy all pairwise Coxeter braid rows and
   their reservoir gauges are synchronized; but
4. the two common-source/common-target contractions have zero cross-Gram.

Let `A=C_2^10` have commuting basis

```text
d_1,d_2,d_3,d_4, h_1,h_2,h_3,h_4,c_2,c_3.
```

Let `j_1,j_2,w` act by the simultaneous coordinate transpositions
`(12),(23),(24)` on both the `d`- and `h`-coordinates.  Let `b_2` send
`h_1` to `h_1c_2`, let `b_3` send `h_3` to `h_3c_3`, and let them fix the
other basis elements.  The generated automorphism group `K<=Aut(A)` is
finite.  Form `Gamma_0=A semidirect K` and use its canonical left-regular
trace.

Put

```text
r=h_1h_2,                 t=h_2h_3,

p=(1+h_2)(1+h_4)(1-c_2)(1-c_3)/16,

e_2^D=(1+d_1)(1-d_2)(1+d_3)(1+d_4)/16,
Q=p e_2^D.                                                (HCG1)
```

These are literal character projections in the finite group algebra and

```text
tau(p)=1/16,              tau(Q)=1/256= tau(p)/16.        (HCG2)
```

Furthermore

```text
[r,b_2]=c_2,              [t,b_3]=c_3,
b_2 t b_2=t,              b_3 r b_3=r,                  (HCG3)
```

and `c_2Q=c_3Q=-Q`.  Expanding in the canonical trace shows that all four
projections

```text
Q(1+/-r)(1+/-t)/4                                      (HCG4)
```

have trace `tau(Q)/4`: every nonconstant Fourier term contains `h_1` or
`h_3`, which lies outside the character subgroup defining `Q`.

Define

```text
T_1=p j_1 Q,                  T_2=p j_2 Q.               (HCG5)
```

Because `j_1pj_1` replaces the positive `h_2` sign by `h_1`, while
`j_2pj_2` replaces it by `h_3`, and `h_2Q=Q`,

```text
T_1^*T_1=Q(1+r)/2,            T_2^*T_2=Q(1+t)/2.         (HCG6)
```

Thus the two paid supports and their intersection have exactly the
`1/2,1/2,1/4` relative masses of the full-Hecke four-sector theorem.

Nevertheless

```text
T_1^*T_2=Q j_1 p j_2 Q=0.                                (HCG7)
```

Indeed `Q<=e_2^D`, while `j_2Qj_2<=e_3^D`, where `e_3^D` is the character
atom negative only at `d_3`.  The projection `p` commutes with `e_3^D`, and
`j_1` fixes `d_3`, hence commutes with `e_3^D`.  Moving that factor to the
left in `(HCG7)` produces `e_2^D e_3^D=0`.

Finally `j_1,j_2,w` are the star transpositions `(12),(23),(24)`, so every
pair obeys the Coxeter braid.  On the Fourier singleton orbit of the
`d`-coordinates, the regular representation has

```text
j_i=S_i tensor V_i,                                      (HCG8)
```

where `S_i` is the literal singleton-label swap and `V_i` is the same
transposition on the `h`-coordinates and remaining multiplicity data.  The
`V_i` obey the same braid rows and are conjugate.  Thus the exact Whitehead
gauge-synchronization conclusion holds in this canonical finite regular
model.

This does not refute either full native cross-Gram claim because `Gamma_0`
models only the displayed interface, not every relation of the binary
Leavitt Steinberg group.  It proves that separate paid self-Grams plus braid
synchronization do not constrain the mixed target moment.  A valid proof
must add an ordinary mixed target-incidence occurrence forcing
`||Qj_1pj_2Q||_2>0`.

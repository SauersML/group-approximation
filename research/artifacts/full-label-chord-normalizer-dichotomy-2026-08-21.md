# Full-label chord normalizers: a sharp but completeness-killing repair

## A concrete mixed word

Let `W` be a fixed Weyl/reset word table spanning the selected finite label
factor `End(V)`.  Add the ordinary relations

```text
[U,w]=1,                    w in W.                      (A1)
```

These relations are genuinely mixed: unlike Reynolds tests on a candidate
Gram, they constrain the native chord itself.  On `V tensor C^N`, they force
`U=I tensor U_N`.  For label projections `H<=E` and `F=E-H`,

```text
X=FUE,              X^*X=F,              E-X^*X=H.      (A2)
```

Thus the residual Gram projection cannot hide in `I tensor M_N`.

## Dimension-free floor on the saturated escape

For the saturated model of the preceding audit, write

```text
q=E_0 tensor Q,       rank(Q)/N=s/r,
h=s/d.
```

Then

```text
||q-H||_2^2=2h(1-s/r).                                  (A3)
```

Weyl averaging gives the exact identity

```text
(1/|W|)sum_w ||[U,w]||_2^2
   =2 dist_2(U,(End(V) tensor I)')^2.                   (A4)
```

Polar correction inside the commutant and the `2`-Lipschitz Gram map yield

```text
(1/|W|)sum_w ||[U,w]||_2^2
   >=(h/4)(1-s/r).                                      (A5)
```

This is a fixed positive floor, independent of `N`.

## Why it cannot be used

The same calculation is exact on infinite multiplicity.  Relation `(A1)`
forces the chord to act only on the external multiplicity, so it cannot map
the larger finite label cut `E_0` source-fully into the smaller cut
`F_0`.  The desired proper Hilbert-hotel compression is destroyed along
with the finite spectator.

More generally, prescribed chord covariance on two or three fixed
noncommuting label charts has only two outcomes:

1. their generated algebra controls both support cuts and covariance returns
   `U^*FU` to that fixed algebra; finite label rank is then preserved and the
   proper infinite return is killed; or
2. they do not control the support cuts, so the relative multiplicity gauge
   remains unauthenticated.

Joint generation of the full label factor is the cleanest instance of the
first case and forces `U=u_0 tensor U_N`.

The surviving relation must therefore distinguish finite from properly
infinite multiplicity.  A fixed full-label normalizer relation is too
functorial; a non-full fixed chart is too gauge-blind.

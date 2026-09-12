---
rg: 2
id: atlas-pointwise-column-coercivity-misses-moving-injection
kind: claim
title: Tracially functorial residual-column coercivity cannot prove the moving Atlas singular injection
invalidates: [atlas-moving-singular-injection-via-residual-column-coercivity]
distinct_from:
  atlas-fixed-packet-hall-cannot-prove-six-row-singular-counting: that freezes a finite type graph and uses rational multiplicity density; this allows the spectral subspaces to move arbitrarily with the matrix and threshold, but rules out proving their transversality from one pointwise residual-column inequality.
  atlas-radius-nine-packet-gram-sos-is-tracial: that rules out fixed block Gram and sum-of-squares proofs of the quadratic Hilbert--Schmidt charge; this isolates the apparently stronger singular-vector argument and shows that its standard injectivity step is the same forbidden operator domination.
---

**ESTABLISHED AS A SCOPED NO-GO.**  Put

```text
A=U-E_K(U),
R=(R_0,R_11,R_30,R_44,R_55,R_c)^T.                  (PCC1)
```

The most direct moving-subspace proof of `(SCI3)` would establish a constant
`L` such that, in every finite regular frame,

```text
||A xi|| <= L ||R xi||
           =L (sum_r ||R_r xi||^2)^(1/2)             (PCC2)
```

for every vector `xi`.  The inequality itself is a legitimate matrix-only
target, but it cannot be obtained from a dimension-free C-star/Gram argument
which remains valid in arbitrary finite tracial models.

Indeed `(PCC2)` is equivalent to the positive-operator inequality

```text
A^*A <= L^2 sum_r R_r^*R_r.                          (PCC3)
```

If `(PCC3)` is obtained by the fixed C-star/Gram calculus, the same derivation
is valid in every finite tracial model.  In the exact Leavitt factor all six `R_r`
vanish, while
`atlas-six-relator-factor-retains-half-nontrivial-s3-mass` gives

```text
||A||_2^2>=1/2.                                      (PCC4)
```

Thus `(PCC3)` would force `A=0`, contradicting `(PCC4)`.

This matters even though the spectral projections themselves move.  If
`P_t=1_[t,infinity)(|A|)` and
`Q_(r,t)=1_[kappa t,infinity)(|R_r|)`, then for
`xi in Ran(P_t) intersect intersection_r Ker(Q_(r,t))`, one has

```text
t||xi|| <= ||A xi||,
||R xi|| < sqrt(6) kappa t ||xi||.                   (PCC5)
```

Choosing `kappa<1/(sqrt(6)L)` in `(PCC2)` would force `xi=0`.  The codimension
inequality would then give

```text
rank(P_t)<=sum_r rank(Q_(r,t)),                       (PCC6)
```

which is `(SCI3)` with constant one.  The contradiction above shows that
this attractive principal-angle proof cannot be supplied by a tracially
functorial pointwise column estimate.

The result does **not** refute a genuinely matrix-only estimate `(PCC2)`
whose proof uses rank or integrality, nor a moving incidence proved only
after selecting `P_t` and the six `Q_(r,t)`.  What is ruled out is first
proving `(PCC3)` by fixed tracially valid positivity and then thresholding it.

DERIVATION
atlas-pointwise-column-coercivity-no-go-proof

---
rg: 2
id: julia-derivation-rank-controls-fold
kind: claim
title: Julia implementer rank is gauge, while derivation rank controls the fold kernel
distinct_from:
  sublinear-julia-seam-collapses-the-fold-kernel-tracially: that bounds fold words by `rank(V-1)`; this proves that quantity is gauge-dependent and replaces it by the intrinsic generator-commutator rank.
  corona-representations-have-an-ideal-valued-support-length: that defines ideal support after passing to the norm corona; this gives a finite-coordinate, gauge-invariant rank estimate directly from the Julia derivation.
  finite-cross-word-family-fits-one-hall-reflection: that gives explicit rank-one permutation seams with finitely many operator gaps; this identifies the necessary rank-spreading quantity for arbitrary globally conjugate models.
  common-padding-erases-julia-derivation-density: that proves faithful norm-corona coordinates can have this intrinsic density diluted to zero by common exact padding; this computes what the density would have to control if separately selected.
---

**ESTABLISHED GAUGE CORRECTION.** Let `F=<X>` be finitely generated and let

```text
sigma:F->U(d),                  V in U(d),
rho(i_0(f))=sigma(f),           rho(i_1(f))=V^*sigma(f)V.   (JDG1)
```

The raw rank `rank(V-1)` is not determined by the two vertex
representations.  For every `W in sigma(F)'`, replacing `V` by `WV` leaves
`rho` unchanged.  Already the identical pair `rho(i_0)=rho(i_1)=sigma` has
implementers `V=1` and `V=-1`, of deviation ranks `0` and `d`.  Thus even

```text
rank(V-1)/d=1                                             (JDG2)
```

does not force one fold word to move.

The intrinsic finite-coordinate quantity is instead

```text
R_X(sigma,V)=sum_(x in X) rank([sigma(x),V]).             (JDG3)
```

It is unchanged by the commutant gauge `V |-> WV`.  If `w in ker(fold)` and
`M_X(w)` is the total `X`-word length of its second-copy syllables, then

```text
rank(rho(w)-1) <= M_X(w) R_X(sigma,V),                    (JDG4)
||rho(w)-1||_(2,d)^2 <= 4 M_X(w) R_X(sigma,V)/d,          (JDG5)
|tr_d(rho(w))-1| <= 2 M_X(w) R_X(sigma,V)/d.              (JDG6)
```

Consequently, if `R_X(sigma_n,V_n)/d_n->0`, every fixed fold-kernel word is
trivial in the tracial ultraproduct, regardless of the size of
`rank(V_n-1)`. A trace-visible Shulman construction must therefore force
positive normalized **derivation rank** (or an equivalent gauge-invariant
commutator-support profile). Forcing macroscopic rank of the chosen Julia
implementer is neither necessary nor sufficient and cannot by itself yield
`(IR1)--(IR3)`.

Conversely, `(JDG5)` gives an explicit necessary rank floor. If one fixed
fold-kernel word of second-copy length `M` satisfies

```text
||rho_n(w)-1||_(2,d_n)^2 >= delta,                     (JDG7)
```

then

```text
R_X(sigma_n,V_n)/d_n >= delta/(4M).                    (JDG8)
```

In particular, selecting the canonical trace of a nontrivial fold word
would force a uniform derivation-rank floor. This isolates exactly what a
“trace-visible Shulman theorem” would add to the published norm theorem.
It is only a necessary condition: algebraic rank is discontinuous, so a
full-rank commutator may still have arbitrarily small normalized HS norm and
does not itself produce an `(IR)` band.

Moreover no lower bound on this density follows from faithful operator-norm
coordinates: `common-padding-erases-julia-derivation-density` preserves the
entire norm-corona model while diluting `R_X/d` to zero. A positive density
must be selected by additional trace data.

DERIVATION
julia-derivation-rank-fold-proof

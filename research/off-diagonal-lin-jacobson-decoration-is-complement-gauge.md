---
rg: 2
id: off-diagonal-lin-jacobson-decoration-is-complement-gauge
kind: claim
title: A Lin word placed in the rectangular Jacobson off-diagonal sees only the complement and leaves the qutrit cokernel representation free
artifacts:
  - research/off-diagonal-lin-jacobson-complement-gauge-proof.md
distinct_from:
  raw-root-hecke-gap-is-blind-to-qutrit-one-over-eighteen-cokernel: that tensors the Hecke carrier with one explicit qutrit regular bimodule; this classifies every representation satisfying the rectangular covariance rows and then inserts literal Lin words in the off-diagonal.
  rectangular-safe-covariance-has-a-positive-head-absorber: that builds an exact positive-density rectangular model; this identifies the uncontrolled representation living on its cokernel.
  commuting-raw-qutrit-router-has-active-rank-ceiling: that bounds raw routers which preserve the active head polar; this shows that decorating the noncommuting rectangular edge by source words still cannot touch the target cokernel.
---

Let `S:H_S-->H_T` and `T=S^*` satisfy

```text
TS=I_(H_S),                    ST=I_(H_T)-Q.             (OLJ1)
```

Suppose representations `pi_S,pi_T` of a Lin source group obey all
literal off-diagonal covariance rows

```text
pi_T(g)S=S pi_S(g).                                      (OLJ2)
```

Then `QH_T` reduces `pi_T`, and there is an arbitrary representation
`alpha` on that space such that

```text
pi_T is unitarily equivalent to alpha direct-sum pi_S.   (OLJ3)
```

The covariance rows determine the complement copy of `pi_T` and say
nothing about `alpha`.

This remains true after putting source words literally into the
off-diagonal.  For every word `w`,

```text
pi_T(w)S=S pi_S(w),       Q pi_T(w)S=0,       T pi_T(w)Q=0. (OLJ4)
```

Thus a raw/full-`C` coefficient made only from the rectangular
`S/T` edge, diagonal Lin words, and commuting qutrit head data cannot
route a Lin occurrence into the qutrit cokernel.  It lives in the
complement corner.  The qutrit target can be reached only by an
additional equality router which mixes `QH_T` with that complement.

There is an exact reflection realization.  On `H_T direct-sum H_S`
put

```text
a=[ Q  S ],                   z=diag(I,-I).
  [ T  0 ]
```

Then `a^2=z^2=I` and `(az)^4=I`.  If
`D_g=diag(pi_T(g),pi_S(g))`, equation `(OLJ2)` gives
`[a,D_g]=[z,D_g]=1`.  For an involutory Lin generator `g`, the
literal off-diagonal reflection `D_g a` is again an involution.  Hence
the entire decorated packet is a functorial `D_8` gauge over the
chosen source and cokernel representations; it adds no relation between
them.

For the 288-dimensional qutrit regular head, `rank(Q)=16` and the
complement has rank 272.  With normalized characters
`chi_alpha,chi_S`, every exact model has

```text
chi_T(g)=(1/18)chi_alpha(g)+(17/18)chi_S(g).              (OLJ5)
```

No row in `(OLJ1)--(OLJ4)` controls the first summand.  Choosing
`alpha=pi_S` recovers the tensor absorber; choosing `alpha` trivial
makes the qutrit block occurrence-free but changes the character by a
visible one-eighteenth contribution.

Therefore a literal off-diagonal Lin label is not the missing
authentication relation.  A surviving compiler must make its
left-right equality router covariant with the Lin tuple on the
rank-sixteen `Q` block itself, or prove a quantitative theorem that
every approximate `alpha` on that block collapses while the ambient
group trace forces it to remain nontrivial.  No such theorem is proved
here, and the nonhyperlinear-group root remains open.

DERIVATION
off-diagonal-lin-jacobson-complement-gauge-proof

---
rg: 2
id: left-rank-amplification-is-not-a-fixed-sector
kind: claim
title: Left-multiplication turns marked rank into an invariant adjoint projection, not a fixed adjoint sector
distinct_from:
  macroscopic-projection-is-one-adjoint-direction: that observes that one physical matrix spans only one adjoint direction; this tests the tempting left-multiplication amplification whose projection really has positive adjoint rank and shows that its range is merely invariant.
  tracial-superoperator-self-copy-has-no-macroscopic-excess: that forbids positive-density projections whose ranges are pointwise fixed by the child; this proves that a large packet spectral projection obtained by left multiplication does not satisfy that hypothesis.
  arithmetic-star-packet-hs-plancherel-anchor: that supplies a linear-rank marked packet displacement and an internal Reynolds gap; this separates the former rank datum from an external child-fixed range.
---

**ESTABLISHED.**  Let `U:H->U(d)` be a unitary representation and let
`X in M_d` commute with `U(H)`.  On the adjoint Hilbert space `M_d`, write

```text
S(h)=Ad(U(h)),                  L_X(Y)=XY.              (LRA1)
```

Then

```text
S(h)L_XS(h)^*=L_X.                                    (LRA2)
```

Thus `L_X` is fixed as **one superoperator vector** under conjugation by the
adjoint representation.  If `p` is a spectral projection of `X`, the
left-multiplication operator

```text
E=L_p in End(M_d)~=M_(d^2)                             (LRA3)
```

is an orthogonal projection with

```text
rank(E)=rank(p)d,
tr_ad(E)=tr_d(p).                                      (LRA4)
```

So a linear-rank packet spectral cut really does become a positive-density
projection on the adjoint space.  However `(LRA2)` gives only

```text
S(h)E=ES(h),                                           (LRA5)
```

not the pointwise fixed-range identity `S(h)E=E` required by
`tracial-superoperator-self-copy-has-no-macroscopic-excess`.  In fact

```text
Ran(E)^H=pM_d intersect U(H)',                         (LRA6)
```

whereas `Ran(E)=pM_d`.  The fixed part can therefore have vanishing adjoint
density even when `tr_ad(E)` is bounded below.

This failure is sharp.  Put `d=2m`, let `p` be the projection onto the first
`m` coordinate vectors, and choose a diagonal unitary

```text
D=diag(lambda_1,...,lambda_(2m))
```

with pairwise distinct eigenvalues.  Let `H=<D>` and `X=1-2p`.  Then `X`
commutes with `H` and `E=L_p` has

```text
tr_ad(E)=1/2.                                          (LRA7)
```

But `D'` is the diagonal algebra, so

```text
dim(Ran(E)^H)=m,
dim(Ran(E)^H)/d^2=1/(4m)->0.                           (LRA8)
```

A permutation exchanging the two `m`-dimensional coordinate halves moves
`X` by full normalized-HS mass, without changing `(LRA8)`.  Hence neither
macroscopic physical rank nor full marked displacement supplies the missing
macroscopic child-fixed operator space.

Iterating the construction does not repair the quantifier.  At the next
adjoint level `L_X` is again one fixed vector and its spectral projections
again commute with the child representation; their ranges are not thereby
pointwise fixed.  Any valid amplifier must instead construct an actual
positive-density subspace of the child commutant, normally a Reynolds-range
difference or an equivalent family of `Omega(d^2)` independently fixed
directions.

For canonical microstates of any group containing an infinite child, the
obstruction is absolute: `canonical-infinite-subgroup-has-zero-adjoint-fixed-density`
proves that every approximation-dependent pointwise-fixed adjoint projection
has density tending to zero.  Thus promoting a packet cut to `L_p` cannot be
repaired by taking its fixed part; a successful construction must force
positive fixed density from the presentation and thereby contradict
canonical microstates outright.

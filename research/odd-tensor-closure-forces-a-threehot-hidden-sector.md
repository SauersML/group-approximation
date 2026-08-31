---
rg: 2
id: odd-tensor-closure-forces-a-threehot-hidden-sector
kind: claim
title: Odd tensor closure forces a three-hot hidden sector in every literal marked one-hot group encoding
artifacts:
  - research/odd-tensor-threehot-hidden-sector-proof.md
distinct_from:
  central-selector-spectra-cannot-prune-a-nonlinear-predicate: that uses the regular marked corner and, for central selectors, finite-dimensional central characters; this gives a representation-by-representation tensor theorem for arbitrary commuting noncentral selector words and a quantitative trace leak.
  lcs-parity-gadgets-preserve-odd-dictator-affine-hull: that classifies scalar auxiliary extensions of a parity gadget; this applies even when the allowed atoms occur only as joint spectral atoms inside a noncommutative marked representation.
  lin-independent-set-synchbcs-has-uniform-nonaffine-onehot-mass: that forces three positive atoms in the source; this shows what tensor closure does to any literal group-word realization of those atoms.
---

Let `Gamma` be a discrete group, let `J in Z(Gamma)` be an involution,
and let `X_1,...,X_m` be commuting involutions.  For a unitary
representation `pi` with `pi(J)=-I`, define its visible joint spectrum

```text
Spec_X(pi)={a in F_2^m:
  product_i (I+(-1)^(a_i)pi(X_i))/2 !=0}.               (OTH1)
```

Let `Sigma_-` be the union of `Spec_X(pi)` over all such marked
representations.  If `Sigma_-` is nonempty, then it is affine.  More
precisely, it is closed under the ternary operation

```text
(a,b,c) |-> a+b+c.                                      (OTH2)
```

Indeed the diagonal tensor product of three negative-`J` representations
is again negative-`J`, and tensoring three joint eigenvectors multiplies
their selector characters.

Consequently, if one negative-`J` representation contains three distinct
one-hot atoms `delta_u,delta_v,delta_w`, its tensor cube contains the
forbidden three-hot atom

```text
delta_u+delta_v+delta_w.                                (OTH3)
```

This remains a positive-mass obstruction for traces.  If the three atoms
have tracial weights `alpha_u,alpha_v,alpha_w>0`, then the three-hot atom
in the tensor-cube trace has weight at least

```text
alpha_u alpha_v alpha_w.                                (OTH4)
```

Apply this to the canonical Lin independent-set source.  Let `M` be its
number of outcomes and let `eta_0>0` be the uniform constant from
`lin-independent-set-synchbcs-has-uniform-nonaffine-onehot-mass`.
For every perfect source trace, choose the two heaviest atoms and the
heaviest remaining atom in the context supplied there.  Their weights obey

```text
alpha_1>=1/M,
alpha_2>=eta_0/(M-2),
alpha_3>=eta_0/(M-2),                                   (OTH5)
```

and hence the marked tensor cube has forbidden local mass at least

```text
beta_0=eta_0^2/(M(M-2)^2)>0.                            (OTH6)
```

Therefore no ordinary group presentation can have both of the following
properties:

1. a negative-`J` tracial representation whose literal commuting group
   involutions reproduce the canonical one-hot PVMs; and
2. a decoder which reconstructs one-hot PVMs from those same literal
   selector spectra in **every** negative-`J` representation (or even in
   every odd tensor power of the distinguished trace).

This kills the smallest proposed shared-controller form when the decoded
source projections are `(1-pi(X_i))/2`: noncommuting ancillary generators
and finite parity transports do not alter `(OTH2)`.  A surviving compiler
must decode source projections as genuinely non-group-like, ancilla-dependent
corner expressions whose behavior is not preserved by diagonal tensor
powers, and it must authenticate one pointed trace face rather than the
whole `J=-1` sector.

The theorem is an exact sector-wide no-go, not a no-go for that pointed
nonmultiplicative possibility.

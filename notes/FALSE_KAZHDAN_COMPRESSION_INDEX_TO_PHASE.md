# The direct Kazhdan compression index has zero index

Date: 2026-08-13

## 1. Outcome

The proposed index-to-phase transducer starts from a fixed-space projection
`P` and a unitary compressor `U`, and tries to retain microscopic leakage by
the Fredholm or Murray--von Neumann index of

```text
P U P : P H -> P H.                                   (KIP1)
```

For this literal operator the index is identically zero in every finite
matrix coordinate and in every finite von Neumann algebra.  Passing to
parity therefore always gives `+1`, not the required Clifford phase.

This is not merely the familiar fact that normalized rank leakage can tend
to zero.  The domain and codomain in `(KIP1)` are the same finite module, so
kernel and cokernel have exactly equal dimension.  The two projections
`P` and `UPU^*` are already Murray--von Neumann equivalent, so their `K_0`
difference is zero before taking any limit.

An index construction could remain viable only after adding genuinely
asymmetric boundary data--for example a Toeplitz extension, a semifinite
ambient algebra, or two projections not already related by an internal
unitary.  None of that data is present in the marked group relations.

## 2. Finite-dimensional calculation

Let `H` be finite dimensional, let `P` be an orthogonal projection, and let
`U` be unitary.  Regard

```text
T=PUP|_(P H):P H->P H.                                (KIP2)
```

Rank-nullity applied to `T` and its adjoint gives

```text
dim ker(T)=dim(PH)-rank(T),
dim ker(T^*)=dim(PH)-rank(T^*)
            =dim(PH)-rank(T).                         (KIP3)
```

The cokernel of `T` is naturally isomorphic to `ker(T^*)`.  Hence

```text
ind(T)=dim ker(T)-dim coker(T)=0.                      (KIP4)
```

This holds whether or not `T` is invertible and regardless of the size of
the small singular-value sector.  In particular

```text
(-1)^(ind(T))=1.                                       (KIP5)
```

There is an equivalent projection calculation.  Put `Q=UPU^*`.  The
partial isometry `UP` has initial projection `P` and final projection `Q`.
Therefore

```text
P Murray--von Neumann equivalent Q,
[Q]-[P]=0 in K_0(M_d(C)).                              (KIP6)
```

The desired one-sided containment cannot be encoded by a nonzero class of
this pair at an exact finite coordinate.

## 3. Finite von Neumann algebra calculation

Let `(M,tau)` be finite and let `P,U in M` be a projection and a unitary.
The compression `T=PUP` lies in the finite corner `PMP`.  Write its polar
decomposition as

```text
T=V|T|.                                                (KIP7)
```

The support projections of `T^*T` and `TT^*` are `V^*V` and `VV^*`, so
finiteness and traciality give

```text
tau_P(V^*V)=tau_P(VV^*).                               (KIP8)
```

Taking complements inside `P` yields

```text
tau_P(proj ker T)=tau_P(proj ker T^*).                 (KIP9)
```

Thus the Breuer index in the finite corner also vanishes.  Likewise
`P` and `UPU^*` are internally equivalent through `UP`, so their
Murray--von Neumann difference is zero.

## 4. Why a microscopic integer is not automatically 2-norm stable

One can force a nonzero integer by changing the problem to a rectangular
map between spaces whose dimensions differ by one.  But that integer is
not determined continuously by normalized Hilbert--Schmidt data: adding or
removing one boundary dimension changes its parity while changing a
bounded operator by only `O(d^(-1/2))` in normalized Hilbert--Schmidt norm.

Therefore an integer parity cannot be read from arbitrary tracial
microstates unless the group relations themselves provide a uniform
spectral gap and canonical asymmetric boundary projection.  For the square
compression `(KIP1)`, a uniform gap only makes the zero-index conclusion
more rigid.

The unilateral shift analogy occurs in the properly infinite algebra
`B(L^2(M))`, where a projection can be equivalent to a proper subprojection.
It does not descend to a nonzero index in the finite matrix coordinates.
That mismatch is precisely why the operator-norm Kazhdan projection proof
does not transfer to normalized Hilbert--Schmidt microstates.

## 5. Scope for the active program

This closes only the direct proposal

```text
KInd(U,Gamma)=ind(PUP).                                (KIP10)
```

It does not rule out every possible secondary invariant.  A live
index-to-phase construction would have to manufacture additional boundary
or extension data functorially from a finite presentation and prove that
the resulting phase is stable under normalized-Hilbert--Schmidt relator
errors.  No such construction is currently present in the Kun--Thom or
one-orbit parity models.

Accordingly the minimal active endpoint remains the CE spatialization of
the one-orbit parity edge, or equivalently Connes embeddability of the
negative central corner described in
`FALSE_ONE_VERTEX_GROUP_CORNER_AND_COVER.md`.

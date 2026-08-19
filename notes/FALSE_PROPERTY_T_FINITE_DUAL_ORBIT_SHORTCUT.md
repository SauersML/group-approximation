# Property (T) does not turn finite dual-orbit rigidity into tracial rigidity

Date: 2026-08-13

## 1. Proposed shortcut and verdict

Let `A` be the additive group of the binary Leavitt ring and let
`Q x Q` act by left and right units.  The proved dual-orbit theorem says
that the trivial character is the only character with a finite orbit.  Since
`Q x Q` has property `(T)`, it is tempting to argue that every finite atomic
character model which is approximately invariant under the quotient must
concentrate at the trivial character.

That implication requires one global finite `Q x Q`-set.  A normalized-HS
microstate supplies only compatible spectral data on each prescribed finite
root window.  It does not supply an honest action of `Q x Q` on one finite
set of global characters.  Property `(T)` cannot be applied before that
completion has been constructed.

Thus

```text
property (T) + no nonzero finite character orbits
```

does not close the hyperlinear obstruction.  The missing statement remains
equivariant character completion, equivalently a special unitary-normalizer
recovery theorem.

## 2. The diffuse limiting model

For any infinite elementary abelian group `A`, its compact dual

```text
X=Hom(A,{+1,-1})
```

carries Haar probability `m`.  Every automorphism of `A` preserves `m`.
Consequently every subgroup of `Aut(A)`, including the left-right Leavitt
unit action, has an exact invariant diffuse character measure.

Moreover Haar measure has the regular root moments

```text
integral_X chi(a) dm(chi)=0,       a!=0.               (PFD1)
```

The corresponding covariant representation of `A semidirect (Q x Q)` on
`L2(X,m)` is

```text
(pi(a)f)(chi)=chi(a)f(chi),
(pi(g)f)(chi)=f(g^(-1) chi).                            (PFD2)
```

The constant vector is fixed by `Q x Q`, while for every `a!=0`,

```text
||pi(a)1-1||_2^2=2.                                    (PFD3)
```

This does not disprove relative property `(T)` for the pair: the constant
vector is not almost invariant under the root.  It does disprove the step
that would identify every quotient-invariant character measure with the
point mass at zero.  Finite atomic measures may converge weakly on every
fixed root window to `(PFD1)` without converging in total variation or
Hellinger distance on a common global character space.

## 3. Why every purely local linear package has atomic models

Let `V` be a finite-dimensional root window over `F_2`.  Its dual `V*` is a
finite character set, and the uniform measure on `V*` has exactly the
moments `(PFD1)` on `V`.  If an injective coefficient transport is tested
only on a subspace `V_0<=V`, enlarge the finite window so that source and
target lie in one finite-dimensional space `W`.  The induced isomorphism
between the two subspaces extends, after choosing complementary bases, to
an automorphism of `W`.  Its contragredient permutation preserves the
uniform measure on `W*` and implements the tested covariance exactly.

The same construction works simultaneously for a finite family of
transports whenever the requested partial maps already extend to a finite
action satisfying the tested word relations.  What can fail is precisely
the existence of those coherent extensions.  Adding more additive root
moments, deeper prefix windows, or separately exactifying each transport
does not address that failure.

Therefore a successful finite obstruction must use at least one of:

1. quotient multiplication relations strong enough to force a coherent
   global action on the atomic labels;
2. coefficient multiplication, visible through cross-root Steinberg
   commutators; or
3. a matrix-coordinate normalizer/commutant recovery theorem.

The formal theorem in
`GroupApproximation/Leavitt/FiniteDualOrbit.lean` applies immediately after
item 1 has been obtained.  It cannot be used to manufacture item 1.

## 4. Consequence for the active program

The Leavitt dual-orbit theorem remains an exact endpoint: once a coherent
finite character action is recovered, every character is forced to be
zero.  It is not itself the recovery mechanism.  The next live calculations
must therefore involve the two-chart coefficient-multiplication packet or
the Kun--Thom one-orbit parity inclusion.  A property-`(T)` argument on
empirical character measures alone is closed.

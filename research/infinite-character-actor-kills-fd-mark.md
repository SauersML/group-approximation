---
rg: 2
id: infinite-character-actor-kills-fd-mark
kind: claim
title: An aperiodic character actor and one Pauli seed kill the mark in every finite-dimensional representation
distinct_from:
  one-pauli-seed-character-expansion: that treats a finite character set and gives an explicit dimension-or-mass inequality; this replaces the all-n family by one infinite actor orbit and first records the exact finite-support obstruction.
  bounded-template-expanding-character-actor-family: that asks for all finite vector spaces inside one bounded-template presentation; this gives an alternative infinite-module interface.
---

Let `A` be a finitely generated group acting on an elementary abelian
2-group `M`, let `0!=m_0 in M`, and assume

```text
chi(m_0)=-1  ==>  |A chi|=infinity                        (ICA1)
```

for every character `chi in M^`.  Form the Pauli-seed extension generated
by `M semidirect A`, involutions `z,J`, and

```text
J central,                    [m_0,z]=J.                  (ICA2)
```

Then every finite-dimensional unitary representation kills `J`.

Indeed restrict a representation to the `J=-1` spectral sector.  The
commuting involutions from `M` have a finite joint spectral support

```text
F subset M^.                                                (ICA3)
```

Actor covariance makes `F` an `A`-invariant finite set, so `(ICA1)` implies
`chi(m_0)=+1` for every `chi in F`.  Hence `m_0` acts as the identity on the
sector.  But `(ICA2)` says that conjugation by `z` sends `m_0` to `-m_0`
there, impossible on a nonzero space.  Thus the sector is zero.

The mark is nevertheless nontrivial whenever `M` has a character `alpha`
with `alpha(m_0)=-1`.  On `L^2(M^)`, let `M` act by character multiplication,
let `A` act by its Koopman representation, let `z` translate `M^` by
`alpha`, and put `J=-I`.  Translation by `alpha` is an involution and
anticommutes with the multiplier for `m_0`, giving `(ICA2)`.

If `A` has property `(T)`, every infinite character orbit has one uniform
Schreier `ell^2` gap for a fixed actor generating set.  Therefore a
dimension-independent procedure which rounds a finite matrix microstate to
one finite-support `M`-spectral PVM and controls actor covariance would give
the approximate analogue of the preceding proof: PVM Poincare energy makes
the `J=-1` mass vanish.  This is precisely the infinite-orbit replacement
for the all-`n` quantifier in
`bounded-template-expanding-character-actor-family`.

The exact theorem does not itself supply that rounding.  In a matrix
ultraproduct the limiting `M`-spectral measure can be diffuse and
`A`-invariant, as it is in the displayed infinite model.  Finite atomic
support is the matrix-only input, so it must be retained quantitatively at
finite stages rather than passed through an arbitrary tracial limit.

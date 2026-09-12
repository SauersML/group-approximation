# The Iwahori twist is not symmetric at the full C-star level

Date: 2026-08-14

## 1. Outcome

Let

```text
K=SL_2(Z),
u=[[1,1],[0,1]],
z=-I,                                                   (ICS1)
```

and let `B_+,B_-` be the two index-three Iwahori subgroups.  Their
commensurator isomorphism satisfies

```text
sigma(u)=u^2.                                          (ICS2)
```

The two edge embeddings do not become identical after applying an
automorphism of the full group C-star algebra of `K`.  More strongly, there
are no

```text
Phi in Aut(C*(K)),       V in U(C*(K))                 (ICS3)
```

such that

```text
Phi(b)=V sigma(b) V*             for every b in B_+.   (ICS4)
```

The same obstruction holds in each fixed central quotient `z=+1` and
`z=-1`.

Consequently the Dogon--Vigdorovich Iwahori amalgam cannot be converted to
Shulman's identical-embedding symmetric amalgam by a non-group-like
automorphism of the vertex C-star algebra.  The failure of the twist to
extend is already visible on the finite space of scalar representations.

## 2. The abelianization calculation

Use the standard presentation

```text
K=<w,u | w^4=1, (wu)^3=w^2>.                          (ICS5)
```

In additive abelianization notation, `(ICS5)` gives

```text
4w=0,
3(w+u)=2w,
w=-3u.                                                 (ICS6)
```

Thus

```text
K_ab ~= Z/12,
u |-> 1,
w |-> -3,
z=w^2 |-> 6.                                          (ICS7)
```

In particular, the scalar characters of `C*(K)` are

```text
chi_j(u)=exp(2 pi i j/12),       j in Z/12.            (ICS8)
```

Their values on `u` run through all twelve twelfth roots of unity.  Their
values on `u^2` run through only the six sixth roots of unity.

## 3. No C-star automorphism absorbs the twist

Assume `(ICS3)--(ICS4)`.  Evaluating `(ICS4)` at `u` and using `(ICS2)`
gives

```text
Phi(u)=V u^2 V*.                                       (ICS9)
```

Every scalar character kills inner conjugacy, so for every character `chi`
of `C*(K)`,

```text
(chi composed Phi)(u)=chi(u^2)=chi(u)^2.              (ICS10)
```

Precomposition by the automorphism `Phi` is a bijection of the character
space.  Therefore the set of values of the left side of `(ICS10)`, as `chi`
varies, must be the full set of twelve values in `(ICS8)`.  The right side
has only six values.  This contradiction proves the full-algebra claim.

The argument allows the unitary `V`; hence it rules out equality of the two
edge embeddings even up to inner conjugacy after applying `Phi`.

## 4. The obstruction survives both central sectors

Fix `epsilon in {+1,-1}` and put

```text
A_epsilon=C*(K)/<z-epsilon>.                          (ICS11)
```

A scalar character `chi_j` factors through `A_epsilon` exactly when

```text
(-1)^j=epsilon,                                       (ICS12)
```

because `z` has class `6` in `(ICS7)`.  Thus each sector has six scalar
characters.  On the positive sector, the values `chi_j(u)` with `j` even
are the six sixth roots of unity; their squares have only three values.  On
the negative sector, the six odd twelfth roots again have only three
distinct squares.

If a sector automorphism absorbed the Iwahori twist, the analogue of
`(ICS10)` would make a six-element value set equal a three-element value
set.  This is impossible.  Hence neither central-sign reduction removes the
obstruction.

## 5. Exact consequence for the hyperlinear program

Shulman's automatic MF theorem for a symmetric amalgam concerns

```text
A *_C A                                                  (ICS13)
```

with the same embedding of `C` into both copies of `A`.  A twisted amalgam
can be put in this form when the edge twist extends to an automorphism of a
vertex algebra, up to an inner conjugacy.  Equations `(ICS8)--(ICS12)` prove
that the Iwahori twist has no such extension even at the full C-star level.

This is stronger than observing that `sigma` does not extend to a group
automorphism of `K`: full group C-star algebras can have automorphisms which
do not preserve canonical group elements, but the scalar-character spectrum
still excludes the required image of `u`.

The result does not rule out a Morita-correspondence argument, a genuinely
twisted amalgam theorem, or the regular-sector basin theorem in
`TRUE_AUTOMORPHIC_GAP_DOES_NOT_CAPTURE_THE_IWAHORI_BASIN.md`.  It rules out
only the proposed reduction to an identical-embedding symmetric double.

## References

- M. Dogon and I. Vigdorovich, *Hyperlinearity, stability and asymptotic
  spectral gap of higher rank lattices*,
  [arXiv:2506.20843v2](https://arxiv.org/abs/2506.20843v2), Question 1.4.
- T. Shulman, *The MF property for amalgamated free products*,
  [arXiv:2603.13564](https://arxiv.org/abs/2603.13564), for the
  identical-embedding symmetric-amalgam theorem.

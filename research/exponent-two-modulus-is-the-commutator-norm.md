---
rg: 2
id: exponent-two-modulus-is-the-commutator-norm
kind: claim
title: At exponent two the power-law modulus is exactly the commutator norm
distinct_from:
  corona-restricted-burnside-equals-power-law-moduli: that is the general equivalence, whose moduli are conjectural for every exponent with an infinite free Burnside group; this is the one exponent at which the modulus is an exact identity, and it exists to show the scheme is not vacuous.
  corona-commuting-torsion-lifts: that lifts commuting torsion families and assumes almost-commutation as a hypothesis; here commutation is the CONCLUSION, derived from three power equations and nothing else.
artifacts:
  - research/artifacts/opnorm-burnside-dossier-2026-08-24.md
---

Let `U, V in U(d)` be exact involutions, `U^2 = V^2 = I`. Then

```text
(UV)^2 - I = U (VU - UV) V,
```

hence, `U` and `V` being unitary,

```text
|| (UV)^2 - I || = || UV - VU ||.                                (E2M1)
```

So the exponent-two law applied to the three words `x, y, xy` forces
commutation **exactly**, with constant `1` and with no dependence on the
matrix dimension. The approximate version follows with an additional
`O(||U^2-I|| + ||V^2-I||)` error, which is the shape `(PLM1)` asks for.

Since finitely generated exponent-two groups are finite elementary abelian
groups, `B(m,2) = R(m,2) = (Z/2)^m` and this produces no non-MF example. Its
role is calibration: it shows that **mixed group structure can be recovered
from finitely many full operator-norm power equations with no rank, trace or
support information at all**, which is precisely what
`corona-restricted-burnside-equals-power-law-moduli` asks for in general.

## Where the difficulty actually starts

Whenever `B(m,N)` is finite, `R(m,N) = B(m,N)` and its relators are literal
consequences of finitely many instances of the exponent law, so moduli exist
for soft reasons. The content of the general problem lives exactly at the
pairs `(m,N)` with

```text
B(m,N) infinite   while   R(m,N) finite,
```

where some relator `s_j` holds in every finite exponent-`N` group without
being a group-theoretic consequence of the exponent law. `(E2M1)` is the
degenerate end of that spectrum and must not be mistaken for evidence about
it.

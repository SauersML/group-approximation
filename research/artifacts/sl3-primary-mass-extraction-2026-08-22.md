# Positive denominator-primary mass from a projective far gap

The coprime-sector projective modulus has a direct mixed-level consequence.
Given an exact finite-dimensional correction of the lattice vertex, split
its irreducibles according to whether their minimal congruence conductor is
coprime to the denominator prime.  If the complementary positive-conductor
summand has normalized dimension `m`, replacing it by the trivial
representation produces a wholly coprime exact correction at normalized HS
cost at most `2 sqrt(m)` on every generator.

Applying the established coprime projective modulus gives

```text
e_h <= eta_odd(delta + xi + E_Lambda + 2 sqrt(m)).
```

Thus a fixed far gap `e_h>=epsilon`, with the other three errors tending to
zero, forces

```text
liminf m >= s_epsilon^2/4 > 0
```

for any `s_epsilon` satisfying `eta_odd(s_epsilon)<epsilon`.

This is insensitive to mixed levels and multiplicities, and it avoids the
false assumption that the denominator generator preserves conductor
summands.  It does not force bounded depth: the positive primary mass may
still spread across an unbounded conductor Folner profile.  The next genuine
problem is therefore contraction or non-Folner coherence of that positive
mass, not merely proving that some primary component is present.


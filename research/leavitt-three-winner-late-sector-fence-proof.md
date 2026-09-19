---
rg: 2
id: leavitt-three-winner-late-sector-fence-proof
kind: route
title: Exhaust cyclic boundaries in the final carrier sector
target: leavitt-three-winner-late-sector-fenced
requires:
  - leavitt-d4-l14-three-winner-profile-has-one-class
---

The coordinate-preserving carrier compiler produces 446 simultaneous states.
For states 426--446 it freely reduces every syllable cut of the exact outer
boundary, appends a formal inverse target in each coefficient copy, and runs
the exhaustive all-coarsening-maximal noncrossing-forest semiring.  The final
audited MSI replay, job `16684287`, found 672 boundary presentations, 331 with
a nonempty formal target: 170 contain that target as a cyclic relator, and 151
kill it by the gcd of powers of one cyclic primitive root.  The remaining ten
presentations are retained with their exact coordinate images.

Iterated primitive-root saturation kills seven of those ten.  Whenever powers
of a cyclic primitive root have exponent gcd one, adjoining the root is a
consequence of Bezout's identity in the cyclic subgroup; coordinate-aware
Tietze elimination then updates every residual and the formal target.  Iterate
this operation to a fixed point.

The last three presentations all have target `b=x7` and relator
`(a b^-1)^2`, where `a=x3`.  Introduce `t=a b^-1`; then `t^2=1` and `a=t b`.
Two presentations contain

```text
b^-2 a b^-1 a = b^-2 (t b) b^-1 (t b) = b^-1,
```

while the third contains

```text
a^2 b^-1 a b^-2 a
  = (t b)(t b)b^-1(t b)b^-2(t b)
  = b.
```

Thus `b=1` in all three.  The implementation performs this exact Tietze
substitution in the free product with the involution `t`, including
involution-aware cyclic reduction.  An independent raw-word and sign audit
confirmed both residual types.  Hence no nontrivial one-copy boundary remains
in the sector.  The final classifier summary was

```text
saturation_killed_q=7
involution_killed_q=3
unresolved_q=0
```

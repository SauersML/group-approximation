# Prime scaling rigidity from maximal Kazhdan blocks

## Result

For every prime `p`, the scaling group `E_p` intrinsically contains a
conjugacy class of maximal property-`(T)` subgroups whose finite radical has
order `2^(p^3+1)`.  Therefore the groups `E_p`, with `p` prime, are
pairwise non-isomorphic.

## Orbital block calculation

At a fixed telescope height, differences in the orbit of the marked pair are
the nonzero vectors of `F_p^3`.  This uses
`SL_3(Z)->SL_3(F_p)`, not the full affine general linear group.  Translation
then makes every coset of
`p^(n-1)Z^3/p^nZ^3` a complete orbital component of size `p^3`.
The lamp block is consequently the finite Clifford group
`ClLamp(p^3)`, of order `2^(p^3+1)`.

The block tree has one vertex type

```text
A_p=V_p x <w>
```

and the other

```text
L_p=ClLamp(p^3) semidirect B_(p,1),
```

with edge group `B_(p,1)x<w>`.

## Intrinsic recognition

Property-`(T)` implies property FA.  A property-`(T)` subgroup fixing an
`A_p` vertex has zero telescope height and, by finite generation, lies in
one edge group.  A subgroup fixing an `L_p` vertex lies in that vertex
stabilizer.  Since `L_p` itself has property `(T)` and fixes exactly one
`L` vertex, its conjugates are precisely the maximal property-`(T)`
subgroups.

The affine group `B_(p,1)` has trivial finite radical.  Projection of a
finite normal subgroup to `SL_3(Z)` is finite normal; commuting with finite
index powers of every elementary unipotent makes it central, and the center
of `SL_3(Z)` is trivial in odd rank.  The translation kernel is
torsion-free.  Hence the finite radical of `L_p` is exactly its Clifford
kernel.

## Adversarial checks

- The affine permutation group is
  `F_p^3 semidirect SL_3(F_p)`; no false identification with
  `AGL_3(F_p)` is used for odd `p`.
- The height-zero argument includes property-`(T)) subgroups of the
  ascending vertex, not only those already in a block vertex.
- Maximality uses uniqueness of the fixed block vertex.
- `B_(p,1)` is not called torsion-free; only its finite radical is proved
  trivial.
- The theorem is deliberately restricted to primes.  For composite scales,
  primitive-vector differences do not make a complete block, so the same
  finite-radical invariant does not apply without additional analysis.

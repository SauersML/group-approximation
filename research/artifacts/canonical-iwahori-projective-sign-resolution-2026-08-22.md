# Projective trace-square resolves Iwahori overlap once the edge orients signs

For `V=2P-1`, direct expansion gives

```text
tr(VUVU*)=1-2||[P,U]||_2^2
```

and hence

```text
1-|tr([V,U])|^2
 =4||[P,U]||_2^2(1-||[P,U]||_2^2).
```

This explains exactly why an isolated balanced block flip is invisible to
projective trace square: both ordinary commutation (`r=0`) and complementary
block exchange (`r=1`) have zero projective energy.

Across an exact `SL_2(Z)` vertex, however, choosing the flip branch for each
generator defines a sign character.  The common Iwahori edge fixes the
orientation.  The unique nontrivial sign character of `SL_2(Z)` is reduction
modulo two followed by sign on `S_3`, and it is nontrivial on the order-two
point stabilizer whose inverse image is the Iwahori subgroup.  Therefore no
nontrivial sign character is trivial on the edge.

The conclusion is that projective trace-square centrality for every fixed
second-vertex generator, together with ordinary edge centrality, forces
ordinary second-vertex centrality even in the rank-half sector.  Thus the
open approximate projective arithmetic-transfer theorem would imply the
canonical Iwahori projection-transfer theorem directly; there is no further
Pauli-orientation loss.

This is a reduction, not a proof of approximate projective transfer.  Exact
projective transfer is already known for exact finite-dimensional arithmetic
representations, but the canonical Iwahori tuple is only an approximate
representation of the full amalgam.  The remaining obstruction is precisely
that approximate arithmetic transfer wall.


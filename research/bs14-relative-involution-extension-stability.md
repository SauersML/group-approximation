---
rg: 2
id: bs14-relative-involution-extension-stability
kind: claim
title: An almost Iwahori involution over an exact BS(1,4) core can be repaired with a dimension-free modulus
distinct_from:
  iwahori-outlier-repair: that is formulated through low-energy edge intertwiners for two modular vertices; this is the equivalent relative one-involution problem after the amenable BS(1,4) core has been repaired.
  iwahori-newton-closes-near-sector: that handles a fixed torsion-multiplicity tube by differential rigidity; this asks for a global packetwise repair over arbitrary periodic BS cycle packets.
  bs14-unitary-representations-are-periodic-cycle-packets: that classifies the exact core; this is the open uniform repair theorem for the remaining involution.
---

OPEN.  Let `R,S in U(d)` be an exact representation of `BS(1,4)`,

```text
R S R^(-1)=S^4,
```

and let `X in U(d)` satisfy, with normalized-HS error at most `epsilon`,

```text
X^2=1,
X R X=R^(-1),
(X S^2)^3=1,
(X R S)^3=1.                                         (BRI1)
```

Prove that `(X,R,S)` is within `f(epsilon)` (allowing only `o(d)` flexible
padding if required) of an exact solution, for one modulus `f(epsilon)->0`
independent of `d`, the periodic orbit lengths, and the multiplicity
monodromies in
`bs14-unitary-representations-are-periodic-cycle-packets`.

The exact core decomposes into fourth-power cycle packets.  After
diagonalizing each return monodromy as in
`bs14-unitary-representations-are-periodic-cycle-packets`, every irreducible
packet is multiplicity one and has a scalar return phase `v in T`.  The
relation `X R X=R^(-1)` pairs the `R`-spectral data, hence the scalar phases
`v` and `v^(-1)`, while the two cubic equations require the same `X` to
extend both modular triangles.  The load-bearing content is simultaneous
scalar-packet matching: repairing either cubic equation separately, or
matching only the scalar spectrum of `S`, need not produce one common
involution.

## Attempts

- **Strict repair fails, and one-dimensional flexible repair is sharp.**
  `even-weil-fixed-line-compression` removes the one `R,S`-invariant fixed
  line from the even Weil representation for every prime `p=1 mod 4` and
  polar-rounds the compressed involution.  The BS core remains exact, all
  four remaining relators have defect `O(p^(-1/2))`, but no exact extension
  exists in dimension `(p-1)/2`.  Adding back one dimension gives an exact
  model.  Property `(T;FD)` upgrades the algebraic nonextension to uniform
  distance from every exact same-dimensional representation: otherwise,
  after adjoining one trivial line, two exact equal-dimensional
  representations would violate the `(T;FD)` intertwiner gap.  Thus strict
  stability fails but the flexible claim survives, and its sharp target must
  permit `padding/d=O(epsilon^2)`.
- **Primitive prime packets are now classified exactly.**
  `prime-bs14-packet-extension-classification` proves that a scalar packet
  extends exactly iff it is the full odd Weil orbit (`p=3 mod 4`,
  `ord_p(4)=(p-1)/2`, `v=1`).  This identifies the exact repair targets, but
  the even-Weil compression shows why exact classification alone cannot
  yield a dimension-free same-dimensional gap.

- **Scalar packets cannot be repaired independently.**  For
  `p=1 mod 4`, the exact even Weil representation restricts on the BS core
  as the direct sum of the trivial fixed line and the primitive nonzero
  packet.  The latter packet has no exact Iwahori extension in its own
  dimension.  Hence the exact Weil involution cannot preserve the two BS
  summands: if it did, its restriction to the nonzero summand would be the
  forbidden exact extension.  Exact repair therefore necessarily uses
  off-diagonal coupling between distinct scalar packets.  After deleting
  the fixed line this coupling has rank at most one, giving defect
  `O(d^(-1/2))`; restoring the line costs relative dimension `1/d`.
  Orthogonal packetwise rounding is thus rigorously ruled out, while a
  global transport that permits boundary mass of order `defect^2` remains
  viable.

- **Core exactification is available.**  The one-solenoid dense-periodic-
  measures theorem gives HS stability of `BS(1,4)`, so the approximate core
  can be repaired before this claim is applied.  This does not control `X`.
- **The matrix-monodromy obstruction disappears.**  The return unitary is
  diagonalizable, so the core is a sum of scalar-phase packets.  The phase
  coordinate remains essential, but no noncommutative `U(k)` matching
  theorem is needed.
- **Fixed-stratum Newton is insufficient globally.**  It controls packets
  after all torsion multiplicities are fixed.  Small-rank stratum changes
  approach one another in normalized HS as dimension grows and require the
  separate reconciliation step.
- **Finite packet target.**  Refine the core into scalar packets `(O,v)`.
  Express `(BRI1)` as equations on the Hankel coefficients between packets
  whose `R`-spectra are inverse.  A dimension-free transport/matching theorem
  for those scalar packet coefficients, coupled across both cubic
  constraints, would prove the claim.
- **Exact determinant pruning.**
  `iwahori-cycle-packet-determinant-fence` eliminates every scalar packet
  violating `(det R/det S)^3=1`; for prime full quadratic-residue orbits with
  `v=+1`, this already excludes `p=1 mod 4`.  This is only an exact
  classifier.  Determinant defects dilute under normalized-HS amplification,
  so the surviving packet transport still needs a positive-density argument.

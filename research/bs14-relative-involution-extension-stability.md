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

The exact core decomposes into fourth-power cycle packets with arbitrary
return monodromy `V`.  The relation `X R X=R^(-1)` pairs the `R`-spectral
and monodromy data with their inverses, while the two cubic equations require
the same `X` to extend both modular triangles.  The load-bearing content is
simultaneous packet matching: repairing either cubic equation separately, or
matching only the scalar spectrum of `S`, need not produce one common
involution.

## Attempts

- **Core exactification is available.**  The one-solenoid dense-periodic-
  measures theorem gives HS stability of `BS(1,4)`, so the approximate core
  can be repaired before this claim is applied.  This does not control `X`.
- **Scalar periodic-orbit matching is insufficient.**  Each cycle carries an
  arbitrary `U(k)` return monodromy.  A proof that ignores it can match every
  parabolic eigenvalue while leaving a full-rank obstruction in the
  multiplicity space.
- **Fixed-stratum Newton is insufficient globally.**  It controls packets
  after all torsion multiplicities are fixed.  Small-rank stratum changes
  approach one another in normalized HS as dimension grows and require the
  separate reconciliation step.
- **Finite packet target.**  On each orbit pair, write `R` in the normal form
  `(BP4)` and express `(BRI1)` as equations on the Hankel intertwiners between
  the `V` and `V^(-1)` multiplicity spaces.  A dimension-free polar/matching
  theorem for those intertwiners, coupled across both cubic constraints,
  would prove the claim.

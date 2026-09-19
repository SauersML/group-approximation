---
rg: 2
id: iwahori-parabolic-boundary-splitting-is-uniform
kind: claim
title: Interior and Eisenstein cohomology split with uniform angle for congruence local systems
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-eisenstein-angle: that proves transversality of the two vertex restriction maps after passing to the residue model; this asks that the residue and interior pieces themselves have a uniformly conditioned splitting in the original fixed-generator cochain norm.
---

**ESTABLISHED.**  For each of the two conjugate modular vertex groups `V` and every
finite-dimensional unitary congruence local system `E=Ad rho`, consider the boundary sequence
from parabolic/interior cohomology to ordinary cohomology and cusp residues.
It admits a splitting whose operator norm, measured in the fixed
cellular quotient norm, is bounded independently of `rho` and its dimension.
Equivalently, the angle between the interior and Eisenstein summands stays
uniformly positive over all congruence coefficient sectors.

The Iwahori edge does not require a separate boundary splitting in the
application: its **total** harmonic norm is compared with the fixed-generator
cochain norm by
`fixed-complex-unitary-local-system-hodge-norms-are-uniform`; only the two
vertex classes are decomposed before restriction.

The proof is `triple-angle-gap-proves-uniform-parabolic-splitting`, using the
explicit adjoint formula and Selberg property `(tau)` from
`selberg-tau-proves-modular-parabolic-triple-angle`.  It never inverts
`1-Ad rho(u)`; its constant is at most `2/kappa`, where `kappa` is a fixed
congruence Kazhdan constant for the modular generators.

## Attempts

- In the Shapiro model over a principal kernel, boundary residues are vectors
  on cusp orbits and the fixed-generator cochain norm is a deck-invariant
  cellular norm.  The desired statement becomes a uniform singular-value
  bound for the finite incidence map from cusp residues to cellular
  cohomology, after quotienting constants.
- `iwahori-eisenstein-angle-proof` shows that the **two-vertex mismatch** on
  residue vectors has exact singular interval `[1,3]`.  This does not by
  itself bound the lift of one residue vector back to a vertex cocycle; the
  lift/splitting map is the missing operator here.
- A proof by orthogonal projection in an arbitrary cochain inner product is
  insufficient unless restriction preserves that orthogonal decomposition
  with uniform norm.  This is exactly the cancellation that must be excluded
  when the cuspidal and Eisenstein lower bounds are assembled.
- **Exact operator reduction.**
  `modular-parabolic-restriction-is-a-three-projection-angle` identifies the
  harmonic cohomology with `ker P_(C2) cap ker P_(C3)` and restriction with
  `-2P_(<u>)`.  Hence this claim is now reduced to the single spectral
  statement `congruence-modular-parabolic-triple-angle-gap`.  A bounded MSI
  screen through `p=23` finds a floor between `.429` and `.667`, settling near
  `.51` in the tested `Ad(P^1(F_p))` family.

## Hecke-square reduction

The fixed Hecke polynomial

```text
K_2=T_2^2/(2<2>).
```

Independently, by `iwahori-hecke-square-separates-cuspidal-and-eisenstein`, its algebraic
cuspidal spectrum lies in `[0,4]`, while its Eisenstein spectrum lies on an
ellipse at distance `1/2` from that segment.  Before the direct proof above,
this reduced the claim to a dimension-uniform bound for the Riesz projector of `K_2`
around either of these two fixed spectral sets (and the analogous
Bernstein-central operator on the Iwahori edge).  This is sharper than
inverting `1-Ad rho(u)`, but spectral separation alone does not control
projectors for a nonnormal operator.  This alternate route remains incomplete
and is not a dependency of the established claim.

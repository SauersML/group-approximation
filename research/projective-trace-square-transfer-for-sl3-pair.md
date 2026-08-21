---
rg: 2
id: projective-trace-square-transfer-for-sl3-pair
kind: claim
title: Projective trace-square transfer for the co-dense SL3 arithmetic pair
distinct_from:
  relative-commutant-collapse-for-sl2-pair: that forces an actual subgroup-central unitary into the ambient commutant; this asks only that its commutator with the one ambient generator become scalar in normalized Hilbert--Schmidt norm.
  no-spherical-leak-in-matrix-ultraproducts: that excludes every nontrivial spherical component and is equivalent to full relative-commutant collapse; this permits a leak whenever its ambient commutator is scalar, because scalarity already suffices for the HNN trace contradiction.
  no-exact-quasi-regular-leak: that excludes only the exact HNN coefficient profile and contains no quantitative transfer inequality; this proposes a dimension-free projective energy inequality for all regular approximate representations of the fixed arithmetic presentation.
---

Let

```text
C = SL_3(Z),
A = SL_3(Z[1/2]) = <C,h>,
h = diag(2,1,1/2).
```

Fix finite presentation relators for `A` and a finite generating set `S_C`
of `C`.  There are a constant `K<infinity` and a modulus `eta(delta)->0`
such that every finite-dimensional unitary assignment `rho` with presentation
defect at most `delta`, and every unitary `U` of the same matrix size, satisfy

```text
1-|tr([U,rho(h)])|^2
 <= K sum_(c in S_C) (1-|tr([U,rho(c)])|^2) + eta(delta).       (PTS1)
```

Equivalently, after passing to inner superoperators,

```text
||[Ad(U),Ad(rho(h))]||_2^2
 <= K sum_(c in S_C) ||[Ad(U),Ad(rho(c))]||_2^2 + 2 eta(delta), (PTS2)
```

because for every unitary `W in U(d)`, with normalized trace and normalized
Hilbert--Schmidt norm on `M_(d^2)`,

```text
||Ad(W)-I||_2^2 = 2-2|tr(W)|^2.                               (PTS3)
```

The claim is projective: `(PTS1)` concludes that `[U,rho(h)]` is close to
*some scalar*, not necessarily to `1`.  This phase quotient is exactly the
weakening consumed by the HNN marked word.

## Attempts

- **Exact models now pass with a uniform quantitative gap.**
  `exact-projective-codensity-has-a-uniform-trace-square-gap` proves `(PTS1)`
  with `eta(0)=0` and one dimension-independent `K` for every exact
  finite-dimensional representation.  Perfectness of `SL_3(Z)` cancels the
  scalar phases on fixed commutator expressions, property (T) moves `U` close
  to `rho(C)'`, and co-density identifies that commutant with `rho(A)'`.
  Thus projective centralizers and finite congruence quotients are no longer a
  falsification gate.  What remains is entirely the uniform-outlier sector of
  approximate ambient representations.
- **Coset-Bernoulli firewall.** If the generalized coset Bernoulli crossed
  product of `coset-bernoulli-ce-refutes-relative-commutant-collapse` is
  Connes embeddable, its base-coordinate unitary produces an exact
  `C`-central witness.  Its commutator with `h` is non-scalar, so it also
  refutes `(PTS1)`.  Projectivization weakens RCC but does not evade that CE
  countermodel.
- **Hecke reduction.** `hecke-far-commutator-defect-formula` already compresses
  ordinary commutator energy to one spherical coefficient.  The missing
  calculation is the modulus-square/projective analogue restricted to the
  nonlinear inner orbit `{Ad(U)}`.  Property (T) controls the surrounding
  Hilbert space but not, by itself, this fixed set.
- **Finite test.** On congruence quotients minimize the ratio of the left side
  of `(PTS1)` to its `C`-energy.  The exact theorem bounds this ratio uniformly
  in the quotient level; computation is now only a calibration of the proven
  exact constant, not a possible refutation of the zero-defect case.

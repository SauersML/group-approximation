---
rg: 2
id: uniform-generated-adjoint-gap-rounds-to-central-code
kind: claim
title: A uniform generated-adjoint gap rounds reflections to central code reflections
distinct_from:
  complete-overlay-code-group-has-uniform-conjugation-gap: that computes a gap after the tuple is already an exact commuting code representation; this assumes a gap for the current generated algebra and uses it to construct the commuting code representation
  code-distance-upgrades-pair-energy-to-full-pinching: that begins with one commuting reference PVM; this manufactures a central commuting reference directly from the current tuple whenever its generated adjoint channel has a gap
  central-clifford-parity-sectors-round-uniformly: that assumes exact scalar commutator signs; this needs no projective-sector decomposition and rounds by projecting each generator to the commutant of the algebra it generates
---

ESTABLISHED.  Let `C=ker(H)<=F_2^L`, where every row of `H` has width at
most `q`, every column occurs in at most `D` rows, `M>=cL`, and

```text
 |Hx|/M >= kappa dist(x,C)/L.                            (UGA1)
```

Let `Q_1,...,Q_L` be reflections in a finite-dimensional tracial von Neumann algebra,
put `A=W*(Q_1,...,Q_L)`, and define

```text
 E_com=(1/L^2)sum_(i,j)||[Q_i,Q_j]||_2^2,
 E_par=(1/M)sum_h||prod_(i:h_i=1) Q_i-I||_2^2.           (UGA2)
```

The products in `(UGA2)` use any fixed ordering.  Suppose the **current**
generated tuple has adjoint Poincare constant `lambda>0`:

```text
 (1/L)sum_j||[T,Q_j]||_2^2
   >=lambda||T-E_(A')(T)||_2^2       for every T in A.  (UGA3)
```

Then there are central commuting reflections `S'_1,...,S'_L in Z(A)`
whose joint spectrum is supported on `C` and

```text
 (1/L)sum_i||Q_i-S'_i||_2^2
 <=(4/lambda+8qD/(c kappa lambda))E_com
    +(4/kappa)E_par.                                   (UGA4)
```

All constants are independent of `L`, the matrix dimension, and character
multiplicities.  In particular, any sequence with `E_com+E_par->0` which
stays a fixed average HS distance from every commuting code tuple must have
its generated-adjoint Poincare constants tend to zero.

This theorem changes the diffuse basin problem qualitatively.  Noncentral
unbounded matrix type is not itself an obstruction: if it has a uniform
adjoint gap, the conditional expectation onto its commutant collapses every
generator to the center at cost paid by the complete-pair energy.  The only
surviving mass is **gapless generated-algebra mass**.  Sparse Clifford
cycles are consistent with this diagnosis: their conjugation gap is of
order the minimum nonzero commutator-row weight, hence tends to zero.

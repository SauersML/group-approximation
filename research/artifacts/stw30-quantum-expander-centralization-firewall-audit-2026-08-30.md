# STW XXX: quantum-expander centralization firewall audit (2026-08-30)

## Result

A norm corona of growing matrix algebras has real rank zero and contains
unital copies of `M_n direct_sum M_(n+1)` for every `n`.  Nevertheless one
fixed finite quantum-expander packet has a relative commutant containing no
unital copy of `M_2 direct_sum M_3`.

This is an operator-norm obstruction to arbitrary centralization, not a
diagonal or tracial approximation defect.  The selected projection

```text
h=e_11^(2) direct_sum e_11^(3)
```

has normalized rank between `1/3` and `1/2` in every unital representation,
including representations that kill one direct summand.  The expander gap
therefore keeps its commutator with one packet unitary uniformly bounded
below.

## Checks

- The product has real rank zero by a coordinatewise spectral gap at zero
  with a uniform inverse bound; the same lifting argument works in the
  `c_0` quotient.
- For each fixed `n`, Frobenius arithmetic gives positive endpoint
  multiplicities in every sufficiently large matrix size.  Omitting finitely
  many coordinates does not affect unitality or injectivity in the corona.
- Finite-dimensional semiprojectivity for the increasing finite-support
  ideals turns any alleged corona embedding into exact tail representations;
  their unit projections are eventually `1` because they converge in norm
  to `1`.
- If `t` is the trace of the selected projection, then
  `t in [1/3,1/2]` and its distance from the scalars in normalized
  Hilbert--Schmidt norm is at least `sqrt(2)/3`.
- The quantum-expander contraction gives the operator-norm commutator floor
  `(1-lambda)sqrt(2)/3`; normalized `2`-norm is bounded above by operator
  norm, so there is no dimension-dependent loss.

## Boundary

The corona is nonseparable and non-simple, and the theorem makes no
nuclearity assertion.  It does not answer Problem XXX.  It rules out every
centralization argument whose only inputs are real-rank-zero spectral
cutting and the existence of scale-wise weak-divisibility blocks.  A positive
proof needs some additional structural or uniform-selection input; the
example does not distinguish separability, simplicity, nuclearity, or a
related central-sequence selection principle from one another.

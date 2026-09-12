---
rg: 2
id: near-weyl-covariant-channels-round
kind: claim
title: A near-idempotent channel close to its twirl over a projective group basis rounds to an expectation
distinct_from:
  bistochastic-near-idempotents-round-dimension-free: that is the unrestricted rounding premise; this proves rounding only for maps close to their own twirl over some irreducible projective unitary group basis, and records the resulting counterexample fence.
  bistochastic-channel-rounding-fails: that asks for a counterexample family; this is one necessary feature of every such family, plus the exclusion of the mutually unbiased non-algebra idempotent.
  schur-near-idempotents-round-dimension-uniformly: that rounds maps diagonal in a matrix-unit basis; this uses unitary error bases, where the twirl produces the diagonal map from an arbitrary nearby channel.
---

**ESTABLISHED.** Let `G subset U(d)` be a projective unitary group basis:
the unitaries `W_g` form an orthonormal basis of `L^2(M_d,tr_d)` and
multiply up to scalars. For a UCP map `P` put

```text
T_G(P) = |G|^(-1) sum_g Ad(W_g) o P o Ad(W_g^*).
```

Suppose `P` is self-adjoint bistochastic UCP with

```text
||P^2-P||_(infinity->2) <= delta,       ||P-T_G(P)||_(infinity->2) <= eta,
delta+3eta < 1/10.
```

Then some unital subalgebra `A` has `||P-E_A||_(infinity->2) <= 2delta+7eta`.

Two consequences:

1. **Counterexample fence.** In any family witnessing
   `bistochastic-channel-rounding-fails` at distance `c`, the distance of `P_n`
   to its own twirl is eventually at least `c/8` for every projective group
   basis of `M_(d_n)`. Counterexamples must be far from every Weyl-covariant
   symmetrization.
2. **The mutually unbiased idempotent is not approximable.** For the diagonal
   algebra `D`, the Fourier matrix `F`, and `P_0=E_D+E_(FDF*)-E_C` on `M_d`,
   every UCP map `P` satisfies

   ```text
   ||P-P_0||_(infinity->2) >= 1/10.
   ```

   So this trace-preserving idempotent onto the non-algebra operator system
   `D+FDF*` cannot be the macroscopic shadow of a channel.

DERIVATION
near-weyl-covariant-channels-round-proof

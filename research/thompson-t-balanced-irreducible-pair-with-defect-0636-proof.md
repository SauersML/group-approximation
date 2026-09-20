---
rg: 2
id: thompson-t-balanced-irreducible-pair-with-defect-0636-proof
kind: route
title: Store the float unitary, pass to its polar part, and bound the change of every relator by the number of A-letters it contains
target: thompson-t-balanced-irreducible-pair-with-defect-0636
requires: []
artifacts:
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/verify_witness.py
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/witness_bal12.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_verify_witness_bal12.json
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/control_n2.py
  - experiments/thompson-t-balanced-riemannian-census-2026-09-17/out_control_n2.json
---

Numbering follows the claim. `||.||` is the operator norm. `python3 verify_witness.py verify`
reads only `witness_bal12.json` and uses numpy float64.

## Item 1

1. **The exact pair.** The stored entries of `U` are floating-point numbers, so they are exact
   rationals. Put `eta = ||U^* U - 1||`. The computed value is `1.02e-15`. Then `U^* U` is
   invertible, and `U~ = U (U^* U)^(-1/2)` is an exact unitary with
   `||U~ - U|| <= eta`. Hence `A = U~ diag(dA) U~^*` is unitary with `A^4 = 1` exactly, and its
   eigenvalue multiplicities are `3,3,3,3`. `B = diag(dB)` is exact, with multiplicities `4,4,4`.
   So `(A, B)` is an exact balanced pair.
2. **Float surrogate.** The script evaluates the relators at `A' = U diag(dA) U^*` and `B`.
   Then `||A - A'|| <= 2 ||U~ - U|| (1 + eta) <= 2 eta (1 + eta)`, and `||A'|| <= (1 + eta)^2`.
3. **Lipschitz bound.** Each relator is a word in `A^(+-1)` and `B^(+-1)`.
   - The letter `A^(-1)` is evaluated as `A'^*`, whose distance to `A^* = A^(-1)` is at most
     the same bound as in step 2.
   - The numbers of `A`-letters are 12 in `r_1`, 20 in `r_2` and 5 in `r_P`.
   - Replacing one letter at a time (a telescoping sum) gives, for each `k`,

     ```text
     | ||r_k(A,B) - 1|| - ||r_k(A',B) - 1|| |  <=  20 * 2 eta (1+eta) * (1+eta)^38  <=  40 eta (1+eta)^40.
     ```

4. **Float evaluation.** A product of at most 40 matrices of size `12 x 12` with norm at most 2,
   followed by a spectral norm, has float64 rounding error well below `1e-12`. The script adds
   `1e-12` for this. This is a standard floating-point bound, not interval arithmetic. With the
   computed `D' = 0.6360452410174076`, this gives `D(A,B) <= 0.6360452410184483`, as recorded in
   `out_verify_witness_bal12.json`.
5. **gamma.** The value `||A^2 B A^(-2) B^(-1) - 1|| = 1.3759` is computed the same way.
   Its perturbation is below `1e-13`.

## Item 2

6. **Irreducibility.** Let `L(A,B)` be the linear map `X -> ([A,X], [B,X])` from `M_12` to
   `M_12^2`. As a matrix it is `288 x 144`, assembled with row-major `kron`. Its kernel is the commutant, and it always contains the scalars.
   - The computed singular values of `L(A',B)` have smallest `4e-16` (the scalars) and second
     smallest `sigma_2' = 0.23801`.
   - The map `L` is 2-Lipschitz in `A`, so `sigma_2(L(A,B)) >= 0.23801 - 4 eta (1+eta) - 1e-12 > 0.2`.
   - Hence the commutant of `(A, B)` is exactly the scalars, and `(A, B)` is irreducible.
7. **Direct sums.** `r_k` of a block-diagonal pair is block-diagonal, so `D` of a direct sum is
   the max of the blocks' `D`s. Also, a direct sum of balanced pairs is balanced. So the `k`-fold
   sum of the witness is an exact balanced pair in `U(12k)` with the same `D`. This gives
   `delta_bal(12k) <= 0.63605`.
8. **Blocks of dimension at most 2.** `control_n2.py` does two things for each spectral class of
   `U(2)` with `A != 1`:
   - it brute-forces the one conjugacy parameter `t in [0, pi]` on a grid of `20001` points;
   - it checks the result against the optimiser.

   The table `out_control_n2.json` is what the counting argument in item 2 uses. Characters
   are handled directly: `D(a, b) = |(ab)^5 - 1|`, where `ab` is a 12th root of unity. Grid
   minima may overestimate the true minima.
   - With `A(t) = i(2P(t) - 1)`, the derivative satisfies `||dA/dt|| <= 1`.
   - The relator `r_2` has 20 `A`-letters, so `D` is 20-Lipschitz in `t`.
   - The grid spacing is `pi/20000`, so each true class minimum is at most `0.0016` below its
     grid value.
   - Every grid value used on the `>= 0.99` side is at least `1.0008`, which leaves the needed
     margin.

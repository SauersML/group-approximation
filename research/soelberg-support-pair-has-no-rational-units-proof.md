---
rg: 2
id: soelberg-support-pair-has-no-rational-units-proof
kind: route
title: Definite shadows linearize the rational pair problem; a sub-support SAT check and 1100 empty Groebner systems finish it
target: soelberg-support-pair-has-no-rational-units
requires:
  - soelberg-gardam-unit-has-no-integral-lift
  - rational-units-rescale-to-integral-units
artifacts:
  - experiments/soelberg-unit-lifting-2026-09-17/soelberg_engine.py
  - experiments/soelberg-unit-lifting-2026-09-17/soelberg_definite_shadows.py
  - experiments/soelberg-unit-lifting-2026-09-17/build_system.py
  - experiments/soelberg-unit-lifting-2026-09-17/pair_shadow_classification.py
  - experiments/soelberg-unit-lifting-2026-09-17/run_all_msolve.sh
  - experiments/soelberg-unit-lifting-2026-09-17/calibrate_pair_shadow.py
  - experiments/soelberg-unit-lifting-2026-09-17/signed_monomial_sat.py
  - experiments/soelberg-unit-lifting-2026-09-17/calibrate_promislow.py
  - experiments/soelberg-unit-lifting-2026-09-17/logs/build_system.log
  - experiments/soelberg-unit-lifting-2026-09-17/logs/pair_shadow_classification.log
  - experiments/soelberg-unit-lifting-2026-09-17/logs/calibrate_pair_shadow.log
  - experiments/soelberg-unit-lifting-2026-09-17/logs/signed_monomial_sat.log
  - experiments/soelberg-unit-lifting-2026-09-17/logs/signed_monomial_sat_full.log
  - experiments/soelberg-unit-lifting-2026-09-17/logs/calibrate_promislow.log
---

Notation as in the target. `rho_1`, `rho_2: Z[S] -> D(Z)` are the shadows of
`soelberg-gardam-unit-has-no-integral-lift`. Every word `w` maps under each
shadow to a signed basis monomial `c_r(w) m_r(w)`. `soelberg_engine.py` builds
the exact product table of `A x B` in the faithful `GL_3(Z)` model and rechecks
`(sum A)(sum B) = 1` over `F_2`.

## Item 1

Let `U in Q[S]` be a unit with `supp U in A`, and put `V = U^-1` with
`supp V in B`. Suppose `U` is not a scalar multiple of a group element, so
`|supp U| >= 2`.

**Step 1: integrality and normalization.**

- By `rational-units-rescale-to-integral-units`, `U = c U_0` with `c in Q^x`
  and `U_0 in Z[S]^x`.
- By item 2 of `soelberg-gardam-unit-has-no-integral-lift`,
  `rho_1(U_0) = +-m_1` for a basis monomial `m_1`.
- Replace `U` by `+-c^-1 U` and `V` by `+-c V`. Now `U` and `V` are in `Z[S]`,
  and `rho_1(U) = m_1` exactly.
- Likewise `rho_2(U) = lambda m_2` and `rho_2(V) = mu m_2^-1` with
  `lambda mu = 1`. Here `lambda = +-1`.
- Also `rho_1(V) = m_1^-1`, which is `t^-m` for `m_1 = t^m` and `-t^m u` for
  `m_1 = t^m u`.

Since `rho_r(U) = sum_k u_k c_r(A_k) m_r(A_k)`, the monomial `m_r` is among the
10 monomials `m_r(A_k)`. The coefficient of each basis monomial `m` in
`rho_r(U)` is the linear form `sum_{k : m_r(A_k) = m} c_r(A_k) u_k`, and the
same holds for `V`. So `(u, v, lambda, mu)` satisfies these equations:

- the linear equations `rho_1(U) = m_1`, `rho_2(U) = lambda m_2`,
  `rho_1(V) = m_1^-1` and `rho_2(V) = mu m_2^-1`, plus `lambda mu = 1`;
- the 209 bilinear coefficient equations of `UV = 1`.

**Step 2: localization.** Let `i < j` be the two smallest indices in
`supp U`. Then `u_k = 0` for `k < j` with `k != i`, and `w u_i u_j = 1` for
some `w`.

The actual supports `A' = supp U` and `B' = supp V` satisfy two conditions:

- the identity lies in `A'B'`;
- no `g != 1` has exactly one representation `A_k B_l` with `k in A'` and
  `l in B'`. Otherwise the coefficient of `g` in `UV` would be the single
  nonzero product `u_k v_l`.

`build_system.py` encodes this as a SAT instance for each of the 406 pairs
`(i, j)`, in CaDiCaL 1.5.3 via PySAT. Only 11 are satisfiable:
`(1,2)`, `(1,3)`, `(1,4)`, `(1,5)`, `(1,7)`, `(2,3)`, `(2,4)`, `(2,5)`,
`(2,9)`, `(3,4)`, `(5,6)` (`logs/build_system.log`).

**Step 3: the 1100 systems.** For each of the 11 pairs `(i, j)` and each
`(m_1, m_2)`, one of 10 x 10, `pair_shadow_classification.py` writes the
system of Steps 1 and 2. The variables are `u_k` (with `k` not forced zero),
`v_1..v_29`, `lambda`, `mu` and `w`. For every `(m_1, m_2)` the inverse
monomials occur among the shadows of `B`, so no case is skipped. Every unit
`U` as above gives a `Q`-point of one of the 1100 systems.

`run_all_msolve.sh` runs msolve on each system over `Q`. All 1100 return
`[-1]`, that is, no point over `Qbar`, with no timeouts
(`logs/pair_shadow_classification.log`). Hence `U` does not exist.

For `Z[S]` and `Z_(p)[S]`: these are subrings of `Q[S]` with the same unit
condition, so item 1 follows from the rational case. QED for item 1.

**Calibration** (`calibrate_pair_shadow.py`, `logs/calibrate_pair_shadow.log`).
There are 21 indices `k` with `A_k^-1 in B`. For each such trivial unit
`U = +-A_k`:

- **Part 1.** Exact sympy evaluation shows it satisfies every equation of its
  shadow case, apart from the localization. A perturbed point violates some
  equation.
- **Part 2.** It is a point of the msolve system with localization
  `u_m = 0` for `m != k` and `w u_k = 1`. msolve reports a solution in all 21
  cases, and `[-1]` when `m_1` is replaced by a wrong monomial.

This run caught and verified the fix of a sign-formatting bug. That bug had
silently made the `u`-type `m_1` cases inconsistent. The 1100 systems above
were generated after the fix, and the log records that the regenerated inputs
are identical to the run inputs.

**Trust surface.**

- The SAT verdicts in Step 2 carry no certificate.
- msolve's characteristic-zero mode is multi-modular and exports no
  certificate of `1 in I`.
- As an exact cross-check, the same 1100 systems were run over `F_p` for
  `p = 1000000007` and `p = 1000000009` (`logs/pair_shadow_classification.log`).
  That run used exact linear algebra over `F_p`, and it also returned `[-1]`
  for all 1100.
- This yields a statement that needs no char-0 verdict. After the
  normalization of Step 1, `U` and `V` are integral and `lambda, mu = +-1`. If
  `p` does not divide `u_i u_j`, the reduction modulo `p` is an `F_p`-point
  of the same system.
- So any nontrivial unit of `Z[S]` on `(A, B)` has
  `1000000007 * 1000000009 | u_i u_j`. Its first two nonzero coefficients
  therefore multiply to at least `10^18` in absolute value.

## Item 2

Let `a = alpha^4` and `b = beta^4`. `S^ab = Z/4 + Z/4` is generated
independently by `x` and `y`, so the exponent sums of a word are well defined
modulo 4 on group elements.

- For a pair `(k, l)` with `A_k B_l = g`, the exponent sums of `A_k B_l`
  differ from a fixed reference representation of `g` by multiples of 4.
  `signed_monomial_sat.py` asserts this for every pair.
- So the coefficient of `g` in `uv` is
  `alpha^ex_g beta^ey_g sum eps_k del_l a^((dx)/4) b^((dy)/4)`.
- `uv = 1` becomes the exact integer sign problem
  `sum_{(k,l) -> g} eps_k del_l a^(dx/4) b^(dy/4) = [g = 1]`.

This problem was encoded with totalizer cardinality constraints, requiring
`|supp u| >= 2` and normalizing the first nonzero sign. CaDiCaL returns UNSAT
in all four classes, both for arbitrary sub-supports and for full support
(`logs/signed_monomial_sat.log`, `logs/signed_monomial_sat_full.log`).

**Calibration** (`calibrate_promislow.py`, `logs/calibrate_promislow.log`).
The same `build` function was run on Gardam's `P` pair, with words copied from
`research/artifacts/gardam-support-pair-gsp.py`:

- class `(-1, -1)` gives 4 sign-normalized full-support solutions, the
  Gardam units;
- the classes `(1, 1)`, `(1, -1)` and `(-1, 1)` give none, as
  `gardam-support-pair-has-no-rational-units` predicts for `(1, 1)`.

The trust surface is again an uncertified SAT solver.

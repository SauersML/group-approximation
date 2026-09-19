---
rg: 2
id: thompson-f-markov-size-chain-scale-limit-affinity-at-most-0-978
kind: claim
title: In the log-scale limit every stationary order-1 Markov size chain has merge affinity B at most 0.97713 (Rayleigh value at most 0.98857), by a CDF rigidity identity forcing Var(U+D) at least 1/3 minus the TV defect
distinct_from:
  thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit: that gives the functional (E2), numerics (sup about 0.954) and only necessary conditions (E3) for B -> 1, with no ceiling; this proves a ceiling B <= 0.97713 for the same functional, uniformly over all order-1 chains, via a new quantitative rigidity inequality.
  thompson-f-iid-forest-test-vectors-are-bounded-below-one: that bounds product-form vectors on finite windows by 1 - 1/1280; this bounds the correlated (Markov) family, but only for the formal scale-limit functional (E2), not on finite windows.
  thompson-f-is-amenable: the root is untouched; this turns the numerical class kill of order-1 Markov size chains in the scale limit into a proved one.
artifacts:
  - experiments/thompson-f-markov-rigidity-2026-09-17/rigidity_check.py
  - experiments/thompson-f-markov-rigidity-2026-09-17/rigidity_check.out
---

**ESTABLISHED (direct proof, unrefereed; one step computer-certified by monotone cell bounds).**

**Scope.** This is about the formal log-scale-limit functional (E2) of
`thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit`. That limit (`M -> infinity`) is not
justified rigorously there, and nothing here says anything about finite `M`, finite windows or `||P||`.
Order-2 chains are not covered: their (E2) analogue has a different `A`.

**Setting.** Take a stationary order-1 chain `(X_t)` on `[0,1]` with marginal density `pi`. Its forward
rows `f_m` (law of `X_1` given `X_0 = m`) and reversed rows `r_m` (law of `X_{-1}` given `X_0 = m`) have
densities. So ties have probability 0 and the rows are atomless. Put:
- `U(m) = r_m([0,m))`, `D(m) = f_m([0,m))`, `S = U + D in [0,2]`;
- up-step: `X_{-1} < X_0`; down-step: `X_1 < X_0`;
- `A(m) = E[1up BC(r_{X_{-1}}, r_m)^2 | X_0=m] + E[1dn BC(f_{X_1}, f_m)^2 | X_0=m]`.

Since `J(s,m)/pi(m) = r_m(s)` and `J(m,s)/pi(m) = f_m(s)`, the (E2) formula reads `B = E_pi sqrt(A)`.
The Rayleigh value is `R = (1+B)/2`.

**Theorem.**
1. *(Rigidity.)* Put
   - `Delta_up = E[U(1-D)] - E[U^2]/2` and `Delta_dn = E[D(1-U)] - E[D^2]/2`;
   - `delta_up = E[1up TV(r_{X_{-1}}, r_{X_0})]` and `delta_dn = E[1dn TV(f_{X_1}, f_{X_0})]`.

   Then `|Delta_up| <= delta_up` and `|Delta_dn| <= delta_dn`, and therefore
   `Var(U+D) >= 1/3 - (4/3)(delta_up + delta_dn)`.
   The product chain is tight: `S = 2u` with `u` uniform, so `Var S = 1/3` and `delta = 0`.
2. *(Closed-form ceiling.)* `B <= 1 - (3-2√2)/6 + 4(17-12√2)/(9√2) = 0.980656`, so `R <= 0.990328`.
3. *(Dual ceiling.)* `B <= 0.977125`, so `R <= 0.988563`.

The numerical supremum of the family is about `0.954`, and the product value is `2√2/3 = 0.9428`.

**Proof of 1.**
- (i) *First moment.* Condition on `X_{-1} = s`. By stationarity, `P(X_0 > s | X_{-1} = s) = P(X_1 > s | X_0 = s) = 1 - D(s)`,
  using no ties. Hence `E[1up U(X_{-1})] = E[U(1-D)]`.
- (ii) *CDF identity.* Condition on `X_0 = m`, write `F_m(s) = r_m([0,s))`, and let `X_{-1} ~ r_m`.
  - Since `r_m` is atomless, `F_m(X_{-1})` is uniform on `[0,1]`.
  - `{X_{-1} < m}` equals `{F_m(X_{-1}) < F_m(m) = U(m)}` up to a null set.
  - Hence `E[1up F_{X_0}(X_{-1}) | X_0=m] = ∫_0^{U(m)} v dv = U(m)^2/2`, and so `E[1up r_{X_0}([0,X_{-1}))] = E[U^2]/2`.
- (iii) *Comparison.* On an up-step with `X_{-1} = s` and `X_0 = m`:
  `|U(s) - r_m([0,s))| = |r_s([0,s)) - r_m([0,s))| <= TV(r_s, r_m)`.
  Subtracting (ii) from (i) gives `|Delta_up| <= delta_up`.
- *Down-steps.* The same argument applies with time reversed:
  - `P(X_0 > s | X_1 = s) = P(X_{-1} > s | X_0 = s) = 1 - U(s)`;
  - `E[1dn f_{X_0}([0,X_1))] = E[D^2]/2`;
  - `|D(s) - f_m([0,s))| <= TV(f_s, f_m)`.
- *Sum.* `Delta_up + Delta_dn = E[S - S^2/2 - UD]`, because `(U^2+D^2)/2 = S^2/2 - UD`. Also:
  - `E S = P(up) + P(dn) = P(X_{-1}<X_0) + P(X_0<X_{-1}) = 1`, by stationarity and no ties;
  - `UD <= S^2/4`.

  So `1 - (3/4) E S^2 <= delta_up + delta_dn`. That is the variance bound. ∎

**Proof of 2.**
- *Pointwise bound on A.* Le Cam gives `BC^2 <= 1 - TV^2`, so `A <= S - a` with
  `a(m) = E[1up TV(r_{X_{-1}}, r_m)^2 + 1dn TV(f_{X_1}, f_m)^2 | X_0=m]`, and `0 <= a <= S`.
- *Cauchy–Schwarz.* `E[1up] + E[1dn] = 1`, so `delta := delta_up + delta_dn <= sqrt(E a) =: x`.
- *Tangent bound.* Concavity and `S <= 2` give `sqrt(S-a) <= sqrt S - a/(2 sqrt S) <= sqrt S - a/(2√2)`.
- *Quadratic bound.* `sqrt s <= 1 + (s-1)/2 - κ(s-1)^2` on `[0,2]`, with `κ = (3-2√2)/2`.
  - Let `h` be the difference of the two sides. Then `h(1) = h'(1) = 0`, `h(2) = 0`, and `h'' = 1/(4 s^{3/2}) - 2κ`.
  - `h'' > 0` on `[0,1.285]`, so `h >= 0` there.
  - `h` is concave on `[1.285, 2]` with endpoint values `>= 0`, so `h >= 0` there too.
  - Consequently `E sqrt S <= 1 - κ Var S`.
- *Combine.* `B <= 1 - κ max(0, 1/3 - 4x/3) - x^2/(2√2)`.
  - For `x <= 1/4` the maximum is at `x* = 4√2κ/3 = 0.16176`. It gives the stated value.
  - For `x > 1/4`, `B <= 1 - 1/(32√2) = 0.97790`. ∎

**Proof of 3.** This is a Lagrangian dual of the relaxation used in 2.
- *Local constraints.* Conditionally on `X_0 = m`, Cauchy–Schwarz gives
  `E[1up TV + 1dn TV | m] <= sqrt(S(m) a(m))`.
- *Constraint.* By part 1 and `UD <= S^2/4`, `E[S - (3/4)S^2] <= E sqrt(S a)`, with `E S = 1` and `0 <= a <= S <= 2`.
- *Objective.* `B <= E sqrt(S - a)`.
- *Weak duality.* For any real `λ0` and any `λ >= 0`,
  `B <= λ0 + sup_{0<=a<=S<=2} [sqrt(S-a) + λ sqrt(S a) - (λ0+λ)S + (3/4)λS^2]`.
- *Removing a.* Cauchy–Schwarz on `(1, λ√S)·(√(S-a), √a)` gives
  `B <= V(λ0,λ) := λ0 + max_{S in [0,2]} [sqrt(S + λ^2 S^2) - (λ0+λ)S + (3/4)λS^2]`.
- *Certification.* At `λ0 = 0.5908` and `λ = 0.1300`, the maximum over `S` is bounded rigorously (up to
  float64 rounding) on 400000 cells of `[0,2]`.
  - On each cell, the increasing terms are evaluated at the right end and the decreasing term at the left end.
  - The result is `V <= 0.977125` (`rigidity_check.py`, part 3).
- *Sanity check.* With `λ = 0` the dual returns the trivial `1`: the rigidity multiplier is what does the work. ∎

**Checks** (`rigidity_check.out`).
- *Identities.* (i) and (ii), up and down, match to `<= 2.2e-16` on 12 random `N`-bin kernels (`N = 2..8`).
  Their two sides are computed independently: over pairs `(X_{-1}, X_0)`, and from `U, D` alone.
- *Cross-check.* `B` agrees with `scale_B` of the census to `1e-13`.
- *Product chain.* It gives `Var S = 1/3` and `B = 2√2/3` exactly.
- *Near-extremal kernels.* Every inequality holds at the L-BFGS optima for `N = 4, 8, 16`.
  - At `N = 16`: `B = 0.953743`, `Var S = 0.2572 >= 0.2140`, and `delta = 0.0895 <= sqrt(E a) = 0.1158`.
  - At the optima the rigidity bound is used with margin `≈ 0.04`, and `|Delta| ≈ 0.64·delta`.
  - So the remaining gap to `0.954` lies in the relaxations `UD <= S^2/4`, `BC^2 <= 1 - TV^2` and pointwise
    Cauchy–Schwarz, not in the rigidity step.

**Class killed (proved, within the formal limit):** stationary order-1 Markov size chains with recursive
shapes, as test vectors for `||P|| = 1` in the log-scale limit.
- *Invariant.* The CDF identity (ii). Merge acts as `max`, so a small child's rescaled size under the parent's
  reversed row is uniform below `U`.
- *Where every member dies.* The step where `B -> 1` needs `delta -> 0` and `S -> 1` in `L^2`, per (E3).
  Part 1 forbids both at once: `Var S >= 1/3 - (4/3)delta`.

**Not covered.**
- Finite `M`. There merge is a sum, not a max, and (ii) fails.
- Order `>= 2` or hidden-state chains, and hierarchical laws.
- Shapes that depend on neighbour sizes.
- Pointer-tilted laws.
- The gap between `0.97713` and the numerical `0.954`.

---
rg: 2
id: accessible-shell-shift-normalization-proof
kind: route
title: A shift-normalizing enumeration pulls its component pieces back to k near-partitions, and the end Euler measure makes (k^n - 1) mu = mn impossible
target: accessible-shell-inputs-admit-no-shift-normalizing-enumeration
requires:
  - accessible-non-virtually-cyclic-groups-carry-end-euler-measures
artifacts:
  - experiments/window-zero-enumerations-2026-09-17/end_measure_check.py
---

Composition is right to left. `Gamma` is the Cayley graph with edges
`{y, gy}`, `g` in `S`, so right multiplications are graph automorphisms. Fix
an end Euler measure `mu` on `Pbar`
(`accessible-non-virtually-cyclic-groups-carry-end-euler-measures`), and
put `T = mu(Pbar)`.

**1. Twisting endomorphism.** Exactly as in step 1 of
`one-ended-shell-shift-normalization-proof`, which uses only freeness of
the regular action, `phi` extends to an injective endomorphism with
`s^m lambda_h s^-m = lambda_(phi(h))` near infinity for all `h`. Put
`sigma = nu^-1 s^m nu`.
- If `m > 0`, `sigma` is an injection `P -> P` missing `m` points.
- If `m < 0`, it is a bijection from `P \ M_0` onto `P`, with `|M_0| = |m|`.
- In both cases `sigma(gy) = phi(g) sigma(y)` for all but finitely many `y`.

**2. Pieces.**
- Let `A` be the finite set of endpoints of bad labeled edges, together
  with `M_0`.
- `Gamma \ A` has finitely many components. Let `E_1, ..., E_r` be the
  infinite ones and `F = P \ (E_1 ∪ ... ∪ E_r)`, a finite set containing
  `M_0`.
- Each `E_i` has finite coboundary, so its closure is clopen.
- As in step 3 of the one-ended proof, `phi(y)^-1 sigma(y)` is a constant
  `c_i` on `E_i`, so `sigma(y) = phi(y) c_i` on `E_i`.

**3. Finite index.** The image of `sigma` is cofinite and lies in
`union_i phi(P) c_i`, together with a finite set. So finitely many cosets
of `H = phi(P)` cover `P` up to a finite set. Since cosets of an
infinite-index subgroup are infinite and infinitely many, `k = [P:H]` is
finite.

**4. Coset-wise pull-back.**
- Fix a right transversal `{t}` of `H`. For each `t`, let
  `I_t = {i : c_i in Ht}`, and write `c_i = h_i t` and `d_i = phi^-1(h_i)`.
- The map `beta_t: Ht -> P`, `x -> phi^-1(x t^-1)`, is a bijection with
  `beta_t(phi(y) h_i t) = y d_i`.
- Since `sigma` is injective, the sets `phi(E_i) c_i` are pairwise disjoint.
  Hence, for each `t`, the right translates `E_i d_i` (`i` in `I_t`) are
  pairwise disjoint subsets of `P`.
- Put `f_t = |P \ union_(i in I_t) E_i d_i| = |Ht \ union_(i in I_t) phi(E_i) c_i|`.
- Summing over `t`:
  `sum_t f_t = |P \ union_i phi(E_i) c_i| = |P \ sigma(dom)| + |F ∩ dom|`.
  - If `m > 0`, this is `m + |F|`.
  - If `m < 0`, it is `0 + |F| - |m|`.
  - In both cases `sum_t f_t = |F| + m`.

**5. Measure count.**
- Disjoint subsets of `P` with clopen closures have disjoint closures. An
  open intersection would contain a point of `P`, and points are isolated.
- So finite additivity and right invariance give, for each `t`:
  `T = sum_(i in I_t) mu(closure E_i) + f_t`.
- Also `T = sum_i mu(closure E_i) + |F|`.
- Summing the first identity over the `k` cosets:
  `kT = (T - |F|) + |F| + m`, that is, `(k - 1) T = m`.

**6. Iteration.** Near equalities are preserved by conjugation, so
`s^(mn) lambda_g s^-(mn) = lambda_(phi^n(g))` near infinity. Here `phi^n` is
injective with `[P : phi^n(P)] = k^n`. Steps 2–5 give
`(k^n - 1) T = mn` for every `n >= 1`.
- If `k = 1`, then `m = 0`, a contradiction.
- Otherwise `n = 1, 2` give `(k^2 - 1)/(k - 1) = 2`, so `k = 1`, again a
  contradiction.

**Consequences.**
- (1) and (2): an inclusion `s^m lambda(P) s^-m <= lambda(P)` produces
  `phi`, by freeness.
- For the gate, `B = lambda(P)` gives `s^-eps lambda(P) s^eps <= lambda(P)`,
  and the window-zero inclusion `W_0 = lambda(P)` is the same statement.
- (3) is the first-coordinate projection of the parity fiber product.
- For `P_0*Z`: Grushko and Kurosh show that `P_0*Z` has more than one end
  and is not virtually cyclic unless `P_0` is trivial. It is finitely
  presented when `P_0` is.

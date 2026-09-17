---
rg: 2
id: qudit-stabilizer-rounding-for-code-constraint-hamiltonians
kind: claim
title: On prime-dimensional qudits, code-constraint Hamiltonians have stabilizer states within a factor 8/sin^2(pi/d) of the ground energy
artifacts:
  - research/artifacts/qudit-stabilizer-rounding-2026-09-12.md
  - research/artifacts/qutrit-stabilizer-rounding-model-test-2026-09-12.md
distinct_from:
  pauli-projector-hamiltonians-are-stabilizer-approximable: that is the qubit case, with the sharper factor 2+sqrt2 from the anticommutation identity; this treats Weyl operators on qudits of any prime dimension, with the factor 8/sin^2(pi/d) from an omega-commutation norm argument.
---

**ESTABLISHED (ordinary proof, unreviewed).** Let `d` be prime.

- **(SR_d)** For an explicit Weyl decomposition `K = sum_j c_j g_j` of a Hermitian
  operator on `n` qudits, with weight `W = sum_j |c_j|`, some stabilizer state has
  `<phi|K|phi> >= lambda_max(K) - (8/sin^2(pi/d) - 1)(W - lambda_max(K))`.
- **(CC_d)** For `H = sum_a w_a (I - Pi_(S_a))` with `w_a >= 0` and stabilizer code
  projectors `Pi_(S_a)`, some stabilizer state has
  `<phi|H|phi> <= (8/sin^2(pi/d)) lambda_min(H)`. Deciding `lambda_min(H) <= a`
  versus `>= b` for such explicit instances is in NP when `b > (8/sin^2(pi/d))a`.
  With extra arbitrary terms `0 <= h <= I` of total weight `V`, it is in NP when
  `V < b - (8/sin^2(pi/d))a`.

**Idea.** For unitaries `u` with `Re<u> = 1-delta`, `||u psi - psi||^2 = 2delta`. Two Weyl
unitaries that fail to commute differ by a factor `|1-omega^m| >= 2 sin(pi/d)`, so
they cannot both have `delta < sin^2(pi/d)/8`. The qubit proof then goes through: fix
a pattern on the commuting good set, and average every other term to zero over the
stabilizer states of that joint eigenspace, which centralizer Weyl operators
permute.

**Model test.** On MSI at `d=3`, 4500 random Hermitian Weyl sums on one and two
qutrits, checked against all 12 and 360 stabilizer states, gave no violation. The
largest ratio observed was `0.57`, so the constant is loose
(`research/artifacts/qutrit-stabilizer-rounding-model-test-2026-09-12.md`).

**Bearing on the root.** Unless QMA is in NP, a QMA-hard family on prime-dimensional
qudits whose terms all penalize leaving stabilizer code spaces has YES energy at
least `b sin^2(pi/d)/8`. With negligible YES energy it needs non-stabilizer term
weight at least about `b`. This covers the code Hamiltonians of good qLDPC codes over
prime fields, and any reducer on `qpcp-by-dinur-iteration` or
`qpcp-from-global-walk-reduction` that outputs them.

**Addendum (2026-09-17, sw-078b): both constants improved.**
- (CC_d) is superseded by `qudit-code-rounding-factor-one-plus-inv-sqrt-d`. That node
  proves the factor `1 + 1/sqrt(d)` for prime `d >= 5`, which is sharp on one qudit via
  `(I - |0><0|) + (I - |+><+|)`, and `8/5` for `d = 3`, where the lower bound is `1 + 1/sqrt3`.
  The proof post-selects on the most satisfied code projector. The NP threshold becomes
  `b > (1 + 1/sqrt(d)) a`, and the bearing sentence above improves to YES energy at
  least `b sqrt(d)/(sqrt(d)+1)`.
- (SR_d) improves to `2/sin(pi/d) + 3`, which is linear rather than quadratic in `d`
  (`qudit-weyl-rounding-constant-linear-upper-bound`), by a commutator pair bound. The
  sharp constant is open. Harper sums force about `d/pi` numerically
  (`qudit-weyl-rounding-sharp-constant`), so the additive constant for general Weyl
  sums is unbounded in `d`, while the code-constraint factor tends to 1.
- The model test's largest ratio `0.57` at `d = 3` is below the true constant. The antiparity
  sum `-sum_(v != 0) D(v)` on one qutrit gives `3/4`.

# Structural partner search by collision depth (2026-09-12)

Lane `kdf-structural-candidates`. Target: `leavitt-unit-group-algebra-not-directly-finite`,
through the sharp lift form `left-invertible-lift-of-s0-in-leavitt-group-algebra`.
Here `Q = L_(F_2)(1,2)^x` and `S = F_2[Q]`.

kdf-sat saturated full-ball SAT at about 470,000 AND variables and asked for
structured supports instead of balls. This note replaces the ball by the
exact universe that any partner of a fixed lift must live in, and feeds it two
structured lifts.

## 1. The measurement: collision depth

`left-partners-lie-in-collision-universes` (ESTABLISHED, a8ed9104c): if `B A = 1`
then a sub-partner `B_0` with `B_0 A = 1` lies in
`U_r = A^(-1) (A A^(-1))^(<= r)` for some `r`, and dually right partners of a fixed
`B` lie in `(B^(-1) B)^(<= r) B^(-1)`. So for a fixed lift the partner search is
exhaustive by depth `r`, and each depth is one exact `F_2` elimination.

Implementation: `experiments/kaplansky_collision_partner_search.py`.
- **Rows:** 128-bit BLAKE2b digests of exact reduced prefix keys. A collision
  can only merge two rows, which weakens the system, so a miss is exact.
- **Peeling:** a row `g != 1` met by one live column forces that column to zero.
  This is sound and removes most of the universe.
- **Verification:** any hit is recomputed in the exact prefix normal form.
- **Positive control:** `1 + x + x^2` with `x` of order seven is a unit of
  `F_2[<x>]`. Its inverse (support 5) is found at depth one and re-verified;
  it is correctly two-sided, since the control is a unit.

## 2. Structured lifts

**ELA1**, the eleven-term cross-atlas lift of `s_0`
(`leavitt-cross-atlas-eleven-term-s0-lift`), left partners.

**FIVE_T0**, the mixed-chart five-term lift of `t_0` of
`eleven-term-s0-lift-has-no-radius-four-left-inverse` item 2, right partners.

**Defect-anchored lifts** (`experiments/kaplansky_defect_anchored_lift.py`).
Per-factor rigidity makes each factor of a strict pair non-`F_2`-linear-sofic,
and the only mechanism against linear soficity on `Q` is the rigid defect of
`leavitt-unit-group-carries-nontrivial-rigid-defect`. So the lift carries the
configuration:
- `u`, the nine-leaf compressor of `openai-nine-leaf-leavitt-configuration`;
- `j = 1 + S[1000]T[1000] + S[10000]T[10001] + S[10001]T[10000]`, in `J = V_(1000)`;
- `x = u j u^(-1)`, acting on `[0001]` inside `Gamma`;
- `gamma = E_12(1) = 1 + S[000]T[001]`;
- `c = [x, gamma] != 1`, checked exactly.

The evaluation is completed to `s_0` (or `t_0`) by an even correction.
- **Atlas balls alone cannot do it.** No even correction exists in the atlas balls
  of radius 3, 4 or 5, because their evaluations never reach the deep monomials
  of `D`.
- **What works:** a pool of 1,570 units, the radius-3 ball together with `d g`
  and `g d` for `d in D` and `g` in the radius-2 ball. It gives a correction of
  support 10 after kernel descent, and a lift of support 13 for both `s_0` and `t_0`.

## 3. Results (all exact misses)

| fixed lift | side | depth | universe | live after peel | result |
|---|---|---|---|---|---|
| ELA1 (11) | left | 1 | 1,023 | 0 | no partner |
| FIVE_T0 (5) | right | 1 | 76 | 0 | no partner |
| FIVE_T0 (5) | right | 2 | 1,058 | 0 | no partner |
| FIVE_T0 (5) | right | 3 | 14,639 | 0 | no partner |
| defect-anchored s0 (13) | left | 1 | 1,343 | 0 | no partner |
| defect-anchored t0 (13) | right | 1 | 1,260 | 0 | no partner |

Runs are on MSI under `/projects/standard/hsiehph/sauer354/kdf-structural/runs/`.
In every instance the peeling step removes all columns: each universe element
produces some product that no other element of the universe reproduces. So a
partner of these lifts needs cancellations that first appear beyond these depths.

**Pending.** ELA1 at depth 2 (about 100,000 universe elements) and FIVE_T0 at
depth 4. The first attempts were OOM-killed by unbounded lru caches, since fixed
(a88f5744f).

## 4. Not attempted

The trace-zero idempotent family asks for an idempotent `D <= P_0` with lifted
2-adic trace 0. No explicit candidate exists on main beyond the refuted balanced
pair `leavitt-trace-balanced-nested-idempotents`, whose `K_0` difference is `2/9`.
So no support was designed for it here.

## Trust surface

Exact prefix normal forms throughout. Digests can only produce false hits, which
the exact re-verification catches. These are bounded fences, not no-go theorems.

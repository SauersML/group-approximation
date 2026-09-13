---
rg: 2
id: dyadic-affine-bs12-germ-at-infinity-proof
kind: route
title: Check the relation cone by cone, list the finitely many local actions of b, and apply the germ statement at the rational fixed point 1^∞, where the germ of a is the canonical shift
target: dyadic-affine-bs12-model-lies-in-no-finite-nucleus-rsg
requires:
  - rsg-proper-power-conjugate-germs-torsion-at-finite-orbits
artifacts:
  - research/artifacts/bh-bg-rsg-nonisometric-hosts-2026-09-13.md
---

Notation is as in the target. Every point of `{0,1}^N` other than `0^∞` and `1^∞`
is uniquely of the form `1^(n+1) 0 y v` or `0^(n+1) 1 y v`, with `n ≥ 0` and
`y ∈ {0,1}`.

**Item 1 (homeomorphisms).**
- `a` sends the partition `{C_00, C_01, C_1}` onto `{C_0, C_10, C_11}` by prefix
  replacement, so `a ∈ F`.
- On the positive half, `b` is a bijection. The cones `C(1^(n+1) 0 y)` go onto the
  cones `C(1^(2n+1+y) 0)`, whose exponents run over all integers `≥ 1` exactly
  once.
- On the negative half, `C(0^(n+1) 1 y)` goes onto `C(0^(2n+2-y) 1)`, again every
  exponent `≥ 1` exactly once.
- `b` maps `C_(1^(n+1))` into `C_(1^(2n+1))` and `C_(0^(n+1))` into `C_(0^(2n+1))`.
  So `b` and `b^-1` are continuous at `1^∞` and at `0^∞`.

**Item 2 (the relation `b a = a^2 b`).** Both sides fix `0^∞` and `1^∞`. Check the
other points case by case.
- **`x = 1^(n+1) 0 y v`.**
  - `a x = 1^(n+2) 0 y v`, so `b a x = 1^(2n+3+y) 0 v`.
  - `b x = 1^(2n+1+y) 0 v`, so `a^2 b x = 1^(2n+3+y) 0 v`.
- **`x = 0^(n+1) 1 y v` with `n ≥ 1`.**
  - `a x = 0^n 1 y v`, so `b a x = 0^(2n-y) 1 v`.
  - `b x = 0^(2n+2-y) 1 v`. Since `2n+1-y ≥ 2`, applying `00w ↦ 0w` twice gives
    `a^2 b x = 0^(2n-y) 1 v`.
- **`x = 0 1 0 v`.**
  - `a x = 1 0 0 v`, so `b a x = 1 0 v`.
  - `b x = 001v`, `a b x = 01v`, and `a^2 b x = 10v`.
- **`x = 0 1 1 v`.**
  - `a x = 1 0 1 v`, so `b a x = 110 v`.
  - `b x = 01v`, `a b x = 10v`, and `a^2 b x = 110v`.

**Item 3 (faithfulness).**
- `BS(1,2) = < s, u | u s u^-1 = s^2 >` is `Z[1/2] ⋊ Z`, with `s = (1,0)`.
- Let `K` be a nontrivial normal subgroup and `(r, j) ∈ K` a nontrivial element.
  - If `j = 0`, then `K ∩ Z[1/2] ∋ r ≠ 0`.
  - If `j ≠ 0`, conjugating `s = (1,0)` by `(r, j)` gives `(2^(±j), 0)`, with the
    sign set by the convention. So the commutator is `(±(2^(±j) - 1), 0)`, a
    nonzero element of `K ∩ Z[1/2]`.
- `K ∩ Z[1/2]` is invariant under multiplication by `2^(±1)`. If it contains
  `r ≠ 0`, it contains `r·Z[1/2]`. So `Z[1/2]/(K ∩ Z[1/2])` is torsion, and every
  proper quotient sends `s` to an element of finite order.
- `a^m(1v) = 1^(m+1) v` for `m ≥ 0`, so `a` has infinite order. Hence
  `s ↦ a, u ↦ b` is injective.

**Item 4 (rationality, and a is not equicontinuous).**
- **Local actions of `b`.**
  - `b|_(1^j) = P` for all `j ≥ 1`, where `P(00v) = 0v`, `P(01v) = 10v` and
    `P(1v) = 11 P(v)`. The smallest cone containing `b(C_(1^j))` is `C_(1^(2j-1))`.
  - `b|_(0^j) = P'` for all `j ≥ 1`, where `P'(10v) = 01v`, `P'(11v) = 1v` and
    `P'(0v) = 00 P'(v)`.
- **Local actions of `P` and `P'`.**
  - `P|_1 = P`. The deeper local actions are the identity and
    `P|_0 = (0v ↦ 0v, 1v ↦ 10v)`.
  - `P'` is symmetric in the same way.
- So `b` has finitely many local actions.
- **`a` is not equicontinuous.** `dist(0^(m+1) 1 v, 0^∞) = 2^-(m+1)`, but
  `a^m(0^(m+1) 1 v) = 0 1 v` and `a^m(0^∞) = 0^∞` are at distance `1/2`.

**Item 5 (no finite-nucleus host).**
- Suppose `G ≤ R_{Γ,E}`, for the full binary shift with `E` the whole space, is an
  RSG with finite nucleus containing `a` and `b`.
- The point `z = 1^∞` is rational. It is fixed by `a`, so `p = 1`, and by `b`, so
  its `b`-orbit is finite.
- By Item 2, `f = b` and `g = a` satisfy `f g f^-1 = g^2`. So
  `rsg-proper-power-conjugate-germs-torsion-at-finite-orbits` makes `[a]_z` of
  finite order.
- But `a^m` acts on `C_(1^j)` as `1^j v ↦ 1^(j+m) v`. For `m ≥ 1` it moves the
  point `1^j 0^∞` off itself. So `a^m` is not the identity on any neighbourhood of
  `z`, and `[a]_z` has infinite order. This is a contradiction.

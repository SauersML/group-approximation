---
rg: 2
id: double-parabolic-head-dies-on-commuting-right-orbits-proof
kind: route
title: Transport the left d-maps through right words on the orbit, then use the pigeonhole on the finite orbit to turn the one-sided inverse Lambda_t Lambda_s = id into a two-sided one
target: double-parabolic-head-dies-on-commuting-right-orbits
requires: []
artifacts:
  - experiments/p22-trap-shadow-2026-09-17/orbit_trap_check.py
  - experiments/p22-trap-shadow-2026-09-17/trap_group.py
---

Notation is as in the target. `G` is an arbitrary group. Maps are written on
the left and composed right to left. No import is used.

## Step 0. Commutation of d-maps is commutation of conjugates

Let `a, b` be commuting involutions and `z` any element. Write
`z_a = a z a`, `z_b = b z b` and `z_ab = ab z ba`. Then

- `d_b z = z b z b = z z_b`;
- `d_a(d_b z) = (z z_b) a (z z_b) a = z z_b . a z a . a z_b a = z z_b z_a z_ab`,
  using `a z_b a = ab z ba = z_ab`;
- symmetrically `d_b(d_a z) = z z_a z_b z_ba`, and `z_ba = z_ab` because
  `ab = ba`.

So `d_a d_b z = d_b d_a z` iff `z_b z_a = z_a z_b`. Every left generator
commutes with every right generator by (LR), so this applies to (C1) with
`(a, b) = (c, b)` and to (C2) with `a in {as, at}`. Part 1 of
`orbit_trap_check.py` checks the equivalence exhaustively on `S_5`. The proof
below uses (C1) and (C2) directly, and Step 0 is needed only for the
corollaries.

## Step 1. Right d-maps preserve Z and left maps pass through them

**(a) `Z` consists of right words.** By definition
`Z = { m(u) : m a finite composition of d_b1, d_bs, d_bt }`, the empty
composition included. `Z` is closed under each right `d_b`.

**(b) One-step transport.** Let `a in {as, at}`, `b` right, and `z in Z`.
Then `d_c z in d_c(Z)`, and

```text
Lambda_a(d_b z) = d_a d_c d_b z
                = d_a d_b d_c z        by (C1) at z
                = d_b d_a d_c z        by (C2) at z' = d_c z
                = d_b Lambda_a(z).
```

**(c) Word transport.** Let `m = d_(b_1) ... d_(b_k)` and `y in Z`. Then
`Lambda_a(m(y)) = m(Lambda_a y)`.

The proof is by induction on `k`, and `k = 0` is trivial. Put
`y' = d_(b_2) ... d_(b_k)(y)`. Then `y' in Z` by (a), and

- `Lambda_a(m y) = Lambda_a(d_(b_1) y') = d_(b_1) Lambda_a(y')` by (b);
- `Lambda_a(y') = d_(b_2) ... d_(b_k)(Lambda_a y)` by induction.

The induction needs no hypothesis on `Lambda_a y`. The right maps are
applied to arbitrary elements of `G`, and (b) is used only at points of `Z`
(namely `y'` and the analogous points further down).

## Step 2. Lambda_s and Lambda_t map Z into Z

By (R1), `Lambda_s u = M_s u = d_bs d_b1 u`, which lies in `Z`. By (R2),
`Lambda_t u = M_t u`, which also lies in `Z`. For `z = m(u) in Z`, Step 1(c)
with `y = u` gives

```text
Lambda_s z = m(Lambda_s u) = m(M_s u) = (m o d_bs o d_b1)(u) in Z,
```

and the same holds for `t`. So `Lambda_s(Z) ⊆ Z` and `Lambda_t(Z) ⊆ Z`.

## Step 3. Lambda_t Lambda_s = id on Z

Let `z = m(u) in Z`. Then `Lambda_s z = m(Lambda_s u)` by Step 1(c). Also
`Lambda_s u in Z` by Step 2, so Step 1(c) applies again with
`y = Lambda_s u`:

```text
Lambda_t Lambda_s z = Lambda_t(m(Lambda_s u)) = m(Lambda_t Lambda_s u) = m(u) = z,
```

using (R3) in the third equality.

## Step 4. Pigeonhole

By Steps 2 and 3, `Lambda_s : Z -> Z` has the left inverse `Lambda_t|_Z`, so
it is injective. `Z` is finite by (F), so `Lambda_s|_Z` is a bijection of `Z`.
Its inverse is then `Lambda_t|_Z`, and `Lambda_s Lambda_t = id` on `Z`. In
particular `Lambda_s Lambda_t u = u`.

Weaker hypothesis. The proof only needs the forward sequence
`Lambda_s^k u = M_s^k u` to be eventually periodic, not all of (F).

- Suppose `Lambda_s^k u = Lambda_s^j u` with `j < k`.
- Applying `Lambda_t^j` (Step 3, `j` times) gives `Lambda_s^(k-j) u = u`.
- So `u = Lambda_s(z)` with `z = Lambda_s^(k-j-1) u in Z`.
- Then `Lambda_s Lambda_t u = Lambda_s Lambda_t Lambda_s z = Lambda_s z = u`.

## Step 5. The head

`h = u . Lambda_s Lambda_t u = u . u = u^2 = 1`, because `u` is an involution.

In `P` these words are exactly those of `trap_group.py`:

- `d_c u = w1 = x_23(1)`;
- `Lambda_s u = us = x_13(S)`;
- `d_b1 u = r = x_14(1)`;
- (R1) reads `us = r bs r bs`;
- (R3) reads `u = ws at ws at`;
- `Lambda_s Lambda_t u = ust = wt as wt as = x_13(ST)`;
- `h = u ust = x_13(Q)`.

The script checks all of these identities exactly over `J`. QED.

## Step 6. Corollaries

**Corollary 1 (abelian normal closure).** Suppose `G` is finite, generated
by the seven elements, and satisfies (LR) and (R1)-(R3).

- Each `d_b` maps `<<u>>` into itself, since `d_b z = z . (b z b)`. So
  `Z ⊆ <<u>>`.
- Also `d_c(Z) ⊆ <<u>>`, and every conjugate of an element of `<<u>>` lies in
  `<<u>>`.
- If `<<u>>` is abelian, Step 0 gives (C1) and (C2). (F) holds because `G`
  is finite. So `h = 1`.

For the two-step case, suppose a Levi-stable subspace `W_1` has `N W ⊂ W_1`
and `N W_1 = 0` for every conjugate `1 + N` of the image of `u`. Then
`N N' = 0`, so these conjugates commute, and `<<u>>` is abelian.

**Corollary 2 (LEF witnesses).** Let `phi` be multiplicative on a ball of
`P` that contains every relator word of (LR) and (R1)-(R3), together with
their prefixes, and let `phi` take values in a finite group. Then the images
satisfy all the hypotheses except possibly (C1) and (C2). If `phi(h) != 1`,
the theorem forces (C1) or (C2) to fail at some `z in Z`.

**Corollary 3 (Z is infinite in P).** In `P` we have
`Z ⊆ <<u>> ⊆ n(M_2(J))`, which is abelian, and `h != 1`. If `Z` were finite
the theorem would give `h = 1`. So `Z` is infinite in `P`.

## Sharpness

1. **(F) cannot be dropped.** `P` itself satisfies every hypothesis except
   (F) and keeps `h` (Corollary 3).
2. **(R1)/(R2) cannot be dropped.** They are what make `Z` invariant under
   `Lambda_s` and `Lambda_t`. Without them the one-sided identity (R3) lives
   on a set that `Lambda_s` leaves.
3. **(C) is the only place where noncommutativity can enter.** Every
   head-keeping finite model must violate (C1) or (C2) on `Z`. Both are
   commutator conditions on conjugates of orbit elements. This is the precise
   input that Sharpness 3 of `jacobson-double-parabolic-two-step-trap-proof`
   said was missing for an iteration beyond the leading symbol.

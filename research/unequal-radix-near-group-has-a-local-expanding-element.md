---
rg: 2
id: unequal-radix-near-group-has-a-local-expanding-element
kind: claim
title: The A5*A6 unequal-radix near group contains an element supported in one root with local slope 59^2, which no equal-radix or tree-compatible near group contains
distinct_from:
  unequal-radix-near-group-halves-are-tree-groups-that-are-not-fp: that shows each half is a tree group and the whole group is not a group of Bass--Serre tree automorphisms; this exhibits an explicit element of the rigid stabilizer of a root with non-unit slopes, the local phenomenon that tree-compatible near groups forbid.
  tree-compatible-fixed-base-enumerations-have-infinite-index: that proves tree-compatible near groups have infinite index in their odometer host; this shows the unequal-radix near group is not tree-compatible even locally.
artifacts:
  - research/artifacts/gq-bh-bh-shell-arith-lsf-mixed-radix.md
---

**ESTABLISHED** (lane proof by hand, cross-checked by an exact symbolic computation on MSI; not
reviewed; no novelty claimed).

## Setting

`P = A_5 * A_6`, `h_0 = 59`, `h_1 = 359`, and the least-significant-first mixed-radix enumeration of
`unequal-radix-free-product-near-group-passes-both-germ-gates`. The digit labeling puts some
`x in A_5` of order 3 at digit 29 and some `z in A_6` of order at least 3 at digit 179. With the
coordinates `(root, y)`, `y in Zh`, of `two-radix-odometer-host-is-f-infinity-with-fg-charge-kernel`, put

    k = s^-1 lambda_(x^-1) lambda_(z^-1) s lambda_x lambda_z      (lambda_z applied first).

(`k = rho^-1 [A,B] rho` for `A = lambda_x s`, `B = s^-1 lambda_z`, `rho = AB`. Here `A` and `B` fix
`(0,-1/2)` with commuting germs of slopes 59 and 359.)

## Statement

1. `k` is the identity on the whole root 0, so it is supported in the proper cone `{1} x Zh`.
2. On every depth-one cone `(1, f + 359 Zh)`, apart from a few exceptional digits `f`, `k` is affine
   with slope `59^2`. Its other pieces in root 1 have slopes `59/359` and `359^-2`.
3. So `k` lies in the rigid stabilizer of root 0 and is not measure preserving there. It is not an
   automorphism of the `h_0`-digit tree, the `h_1`-digit tree, or the Bass--Serre tree of `A_5 * A_6`.
4. **Contrast.** In the equal-radix near group of `A_5 * A_5`
   (`arithmetic-a5-near-group-is-not-finitely-presented`), every element supported in a proper cone has
   slope 1 on every leaf. Such an element fixes all ends of the other half-tree, hence fixes the root
   vertex of its own half, hence preserves depth. The same word with equal radices has slope 1
   everywhere.

## Proof

*Root 0.* Work with `c = 29`, `e = 179`, `21181 = 59 * 359`, and `x^-1`, `z^-1` with digits `d` and `f_0`.
- `lambda_z` sends `(0,y)` to `(1, 179 + 359y)`.
- `lambda_x` sends it to `(0, 29 + 59*179 + 21181y) = (0, 10590 + 21181y)`.
- `s` gives `(1, 10590 + 21181y)`.
- `10590 = 29*359 + 179`, so the first `h_1`-digit is 179, the digit of `z`. So `lambda_(z^-1)` cancels
  it: `(0, 29 + 59y)`.
- The first `h_0`-digit is 29, so `lambda_(x^-1)` cancels it: `(1, y)`.
- `s^-1` gives `(0, y)`.

*Generic cone in root 1.* Let `f` be a digit other than `f_0`, with `z x'_f = x'_(f')`, and suppose no digit met below
equals 359, so no bijective-digit correction occurs.
- `lambda_z`: `(1, f + 359t) -> (1, f' + 359t)`.
- `lambda_x` (prepend): `(0, 29 + 59f' + 21181t)`.
- `s`: `(1, 29 + 59f' + 21181t)`.
- The first `h_1`-digit is `r ≡ 29 + 59f' (mod 359)`, which is independent of `t`. For `r != 179`,
  `lambda_(z^-1)` rewrites the digit to `r''` and gives `(1, r'' + 359u_0 + 21181t)`.
- `lambda_(x^-1)` (prepend): `(0, d + 59r'' + 21181 u_0 + 59*21181 t)`.
- `s^-1` gives `(1, const + 59^2 * 359 t)`.

The domain has modulus 359 and the image has modulus `59^2 * 359`, so the slope is `59^2`. With equal
radices the congruence `59f' ≡ 0` forces `r` to be the digit of `z` at the fourth step. Then
`lambda_(z^-1)` cancels, contracting by `1/59`, and the total slope is 1. That is the structural source
of the difference.

*Exact cross-check (MSI, artifact §7).* A symbolic cone trace, independent of the table-composition
code, confirms the following.
- Root 0 maps as one cone by the identity.
- Root 1 splits into 21181 pieces with slope counts: `3481` (358 pieces), `59/359` (20764),
  `359^-2` (58), `1` (1).
- The composed table agrees with the trace pointwise.
- The equal-radix word traces to 117 pieces, all of slope 1.

## Scope

This is a necessary condition for `[H : R_nu] < infinity`, which remains OPEN. `H'` contains such
elements, while tree-compatible near groups do not. It is not a proof of finite index.

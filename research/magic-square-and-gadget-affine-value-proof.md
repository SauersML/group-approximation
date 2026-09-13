---
rg: 2
id: magic-square-and-gadget-affine-value-proof
kind: route
title: Magic-square rigidity forces a near-uniform AND marginal, which no affine-safe support and no coset pushforward can carry
target: affine-safe-value-of-magic-square-and-gadget-below-one
requires:
  - matrix-conj-forces-unsafe-support
  - near-perfect-bcs-strategy-gives-synchronous-relator-state
artifacts:
  - research/artifacts/affine-support-value-gap-2026-09-13.md
---

Notation as in `affine-safe-value-of-magic-square-and-gadget-below-one`
and `matrix-conj-forces-unsafe-support`. Fix a synchronous strategy `S` for
`B_MS^AND` with value `1-eps` and synchronous state `tau`. Write `delta=T eps`
with `T` of `(V1)`.

## Step 0: relator control

`near-perfect-bcs-strategy-gives-synchronous-relator-state` applied to the
fixed BCS `B_MS^AND` gives that `tau` is a `(delta, R(B_MS^AND))`-state and
`(delta, X)`-synchronous: every listed commutation, every listed parity
product, and every forbidden-assignment projection has defect at most `delta`
in the state, and Alice--Bob generator disagreement is at most `delta`. In
particular, writing each observable as a `+-1` involution, for any listed
relation `w=+-1` one has `||w - (+-1)||_2^2 <= 2 delta`, so
`||w - (+-1)||_2 <= sqrt(2 delta)`.

## Step 1: the (A,B) marginal is near uniform

Encode `A,B` as `+-1` observables. Their four joint atoms in context `c_AND`
are

```text
p(s,s') = tau( ((1+sA)/2)((1+s'B)/2) )
        = (1/4)( 1 + s tau(A) + s' tau(B) + s s' tau(AB) ),   s,s' in {+-1}.
```

We bound `|tau(A)|`, `|tau(B)|`, `|tau(AB)|`.

**Derived anticommutations.** As in `(UTC2)-(UTC4)` of
`matrix-conj-forces-unsafe-support`, the last-column parity
`C F I = -1` with `C=AB`, `F=DE`, `G=AD`, `H=BE`, `I=GH` and the listed
commutations `(UTC3)` give `A E A E = -1`, hence `AE=-EA`; the third-row
commutation `[G,H]=1` gives `BD=-DB`; and with `G=AD` a direct substitution
gives `G(AB)G^{-1}=-AB`. Each identity is a product of at most `C0` listed
relations, so its defect in `tau` is bounded by a sum of at most `C0` listed
defects times unit-norm factors:

```text
||AE+EA||_2 <= C0 sqrt(2 delta),
||BD+DB||_2 <= C0 sqrt(2 delta),
||G(AB)G^{-1}+AB||_2 <= C0 sqrt(2 delta).                          (S1)
```

**Traces vanish up to the defect.** `E` is a `+-1` involution, so
`tau(EAE)=tau(A)` (traciality). Using `EA=-AE+Delta` with
`Delta=AE+EA`, `EAE = E(AE) = E(-EA+Delta) = -A + E Delta`, so

```text
2 tau(A) = tau(E Delta),   |tau(A)| <= (1/2)||Delta||_2 <= (C0/2) sqrt(2 delta).
```

Identically `|tau(B)| <= (C0/2) sqrt(2 delta)` from `BD=-DB`, and
`|tau(AB)| <= (C0/2) sqrt(2 delta)` from `G(AB)G^{-1}=-AB` (conjugation by the
involution `G` is trace preserving). Hence with `beta := (C0/2) sqrt(2 delta)`,

```text
p(s,s') >= (1/4)(1 - 3 beta) = 1/4 - (3/8) C0 sqrt(2 delta).       (S2)
```

## Step 2: the AND graph has no large affine subset

Over `F_2`, affine subsets have sizes `1,2,4,8`. The allowed set
`{000,010,100,111}` of `(V0)` is not a flat: `000+010+100=110` is not allowed,
so no `2`-flat equals it and it contains no `2`-flat. Any two points form a
`1`-flat. Therefore:

- **(P1)** every affine subset contained in `Allowed_(c_AND)` has at most two
  points;
- **(P2)** the smallest flat containing all four allowed points is the whole
  cube `F_2^3` (they generate it), so any proper flat omits at least one
  allowed point.

## Step 3: affine-safe strategies, proof of (VA)

If `S` is affine-safe then `affineHull(supp(tau_(c_AND))) subseteq Allowed`,
so `supp(tau_(c_AND))` is an affine subset of `Allowed`, and by (P1) it has at
most two points. The `(A,B,Y)` atoms coincide with the `(A,B)` atoms up to the
`Y=AND(A,B)` defect `<= delta` (relation `(UTC5)`), so at least two of the four
values `p(s,s')` are at most `delta`. With `(S2)`,

```text
delta >= 1/4 - (3/8) C0 sqrt(2 delta).
```

Hence `(3/8)C0 sqrt(2 delta) >= 1/4 - delta`. If `delta >= 4/9` then `(VA)`
already holds since `4/9 >= 4/(9 C0 T)`. Otherwise `1/4 - delta > 1/4 - 4/9`,
and using `delta <= 4/9` in the left factor, `sqrt(2 delta) >= (1/4-delta)/((3/8)C0)`;
in either case a crude bound suffices: since two atoms are `<= delta` while by
`(S2)` each atom is `>= 1/4 - (3/8)C0 sqrt(2 delta)`, we get
`1/4 - (3/8)C0 sqrt(2 delta) <= delta <= (3/8)C0 sqrt(2 delta)` (the last as
`delta <= sqrt(2 delta)` for `delta <= 1/2`), so
`(3/4)C0 sqrt(2 delta) >= 1/4`, `sqrt(2 delta) >= 1/(3 C0)`, and
`delta >= 1/(18 C0^2) >= 4/(9 C0 T)` since `T >= 8 C0` (as `T=4^5 27 k` is
large). Thus `eps = delta/T >= 4/(9 C0 T)`, which is `(VA)`.

## Step 4: canonical-corner pushforwards, proof of (VB)

Let `D` be affine and `S` the decoded strategy from the canonical trace
`tau_omega`. By (CS1) the target answers in each context are uniform on the
coset `X_A(omega)`, and an affine map sends a coset to a flat with uniform
pushforward. So `tau_(c_AND)` is **uniform** on a flat `F subseteq F_2^3`, and
`supp(tau_(c_AND)) = F` exactly (uniform mass is positive on every point of
`F`).

By Step 1, every allowed atom has mass `>= 1/4 - (3/8)C0 sqrt(2 delta)`. Two
cases.

- `F` is a proper flat. By (P2) it omits an allowed atom, whose mass is then
  `0`, so `1/4 - (3/8)C0 sqrt(2 delta) <= 0`, giving `delta >= 1/(18 C0^2)` as
  in Step 3.
- `F = F_2^3`. Uniform mass is `1/8` on each of the eight points, so every
  allowed atom has mass exactly `1/8`. Then
  `1/8 >= 1/4 - (3/8)C0 sqrt(2 delta)`, i.e. `(3/8)C0 sqrt(2 delta) >= 1/8`,
  so `sqrt(2 delta) >= 1/(3 C0)` and `delta >= 1/(18 C0^2)`.

In both cases `delta >= 1/(18 C0^2) >= 1/(9 C0 T)` (again `T >= 2 C0`), so
`eps >= 1/(9 C0 T) = c*`, which is `(VB)`.

## Remarks

- The two bounds `(VA)` and `(VB)` share the same mechanism; the stated
  constants `4/(9 C0 T)` and `1/(9 C0 T)` are convenient lower bounds, not
  optimized values. Either way the gap is a fixed positive constant of the
  single finite gadget.
- Nothing here assumes a perfect model, and nothing depends on any source
  `B_0` the gadget is adjoined to. This is exactly the constancy that gap
  (iii-c) requires.
- Trust surface: the finite constant `C0` is the count of listed relations in
  the `(UTC4)` derivation, taken from `matrix-conj-forces-unsafe-support`; it
  is fixed and explicit but not minimized here. Magic-square rigidity enters
  only through the elementary trace-flip identities of Step 1, not through any
  external self-testing constant.

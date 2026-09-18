---
rg: 2
id: higman-thompson-roots-miss-a-kl-word-over-thompson-v-proof
kind: route
title: Matte Bon's coding map is V-equivariant and each transposition of the census S_3 is the identity on the preimage of a cone, so orbits keep size one or three and the Sym(Omega) obstruction applies
target: higman-thompson-roots-miss-a-kl-word-over-thompson-v
requires: [thompson-v-homomorphisms-into-higman-thompson-are-coded, cantor-homeomorphisms-miss-a-unimodular-root, cone-diagonal-roots-miss-a-kl-word-over-thompson-v]
---

We use the right action `x g` as in the census. Orbit sizes and the existence
of roots do not depend on this convention (Step 4 of
`cone-diagonal-roots-miss-a-kl-word-over-thompson-v-proof`).

## Step 1: the census S_3 and its three pointwise-fixed cones

By Steps 1 and 2 of `cone-diagonal-roots-miss-a-kl-word-over-thompson-v-proof`:
- `F = <a, c> ≅ S_3` permutes the prefixes `00`, `01`, `1` and carries the
  tail along.
- Every `F`-orbit on `C` has size exactly `3`.

The three transpositions of `F` are:

| transposition | swaps | fixes pointwise | table (`(p, p)` entry last) |
|---|---|---|---|
| `a` | `00z <-> 01z` | `C_1` | `{(00,01), (01,00), (1,1)}` |
| `c` | `1z <-> 00z` | `C_01` | `{(1,00), (00,1), (01,01)}` |
| `aca` | `01z <-> 1z` | `C_00` | `{(01,1), (1,01), (00,00)}` |

**Checking `aca`.**
- `00z -> 01z -> 01z -> 00z`
- `01z -> 00z -> 1z -> 1z`
- `1z -> 1z -> 00z -> 01z`

The artifact records the machine check: `<a,c>` has order `6`, `a`, `c`, `ac`
have orders `2, 2, 3`, and sample orbits have size `3`. Every point of `C`
starts with exactly one of `00`, `01`, `1`. So:

**(F1)** For every `x in C` there is a transposition `tau_x in F` that is the
identity on a cone `C_p` containing `x`, with `p in {00, 01, 1}`. Some table
of `tau_x` contains the pair `(p, p)`.

A table is fixed only up to the order of its entries in each pair. Whichever
orientation the source uses, the entry `(p, p)` is the same.

## Step 2: the structure of `rho`

Let `rho : V -> V_{n,1}` be non-trivial.
- `ker rho` is a proper normal subgroup of the simple group `V`, so it is
  trivial and `rho` is injective. Hence `rho(F) ≅ S_3`, and `rho(a)`, `rho(c)`
  are distinct transpositions in it.
- Import `thompson-v-homomorphisms-into-higman-thompson-are-coded`.
  It gives:
  - a clopen support `Z`, off which every `rho(g)` is the identity;
  - an `Omega_2`-system `{T_0, T_1}` with `rho(g) = ⊔_i T_{v_i}^(-1) T_{w_i}`
    for any table `{(v_i, w_i)}` of `g`;
  - a continuous coding map `q : Z -> C` intertwining the two actions;
  - the consequence: if a table of `g` contains `(p, p)`, then `rho(g)` is
    the identity on `q^(-1)(C_p)`.

## Step 3: every `rho(F)`-orbit has size 1 or 3

**A point `y` off `Z`.** Every `rho(g)` fixes `y`, so its orbit is `{y}`.

**A point `y` in `Z`.** Put `x = q(y)`.
- **At most 3.** By (F1) and the consequence in Step 2, `rho(tau_x)` is the
  identity on `q^(-1)(C_p)`, which contains `y`. So the stabilizer of `y` in
  `rho(F) ≅ S_3` contains `rho(tau_x)`, an element of order `2`. The orbit
  has size `6 / |Stab| <= 3`.
- **At least 3.** By equivariance, `q(y rho(g)) = x g` for `g in F`. So `q`
  maps the `rho(F)`-orbit of `y` onto the `F`-orbit of `x`, which has size
  `3` by Step 1.

So the orbit has size exactly `3`.

**Some orbit has size 3.** `rho(a) != 1`, so it moves some point `y`, whose
orbit is not `{y}`. By the above it has size `3`.

This is item 1. The case `n = 2` covers every non-trivial endomorphism of `V`.

## Step 4: no root, even in `Sym(X_n)`

**Setting up.** Suppose `x in Sym(X_n)` and a non-trivial `rho` satisfy
`rho(c) x rho(a) x rho(a) x^(-1) = 1`. Conjugating by `rho(c)` gives
`x a' x a' x^(-1) b' = 1`, where `a' = rho(a)` and `b' = rho(c)` are distinct
transpositions generating `rho(F) ≅ S_3`.

**Applying the import.** Import `cantor-homeomorphisms-miss-a-unimodular-root`,
item 2, verbatim:

> For any set `Omega` with an action of `S_3 = <a, b>` whose orbits all have
> size `1` or `3`, with at least one of size `3`, there is no
> `x in Sym(Omega)` with `x a x a x^(-1) b = 1`.

Take `Omega = X_n` and the orbit type of Step 3. Then no such `x` exists.

**The convention.** The other composition convention is handled exactly as
in Step 4 of `cone-diagonal-roots-miss-a-kl-word-over-thompson-v-proof`: by
reversal, inversion and `y = x^(-1)`, using that `a'` and `b'` are
involutions.

**Conclusion.** Suppose `psi : V_{w0} -> V_{n,1}` is non-trivial on `V`. Put
`rho = psi|V` and `x = psi(t)`. The relation `psi(w0) = 1` is the displayed
equation, which is a contradiction. This is item 2.

## Step 5: Kervaire--Laudenbach holds for w0

This is item 1 of the imported, established claim
`cone-diagonal-roots-miss-a-kl-word-over-thompson-v`:

> **Kervaire--Laudenbach holds for `w0` over `V`.** The map
> `V -> (V * <t>)/<<w0>>` is injective.

This is item 3.

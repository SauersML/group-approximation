---
rg: 2
id: bs12-twist-hosts-need-dynamical-degrees
kind: claim
title: The host condition (H) for the twisted chain lamplighter cannot come from finitely supported data (in lamp wreaths an evaluation twist only moves a chain configuration into the lamp), and in a germ host the base generator b has, for every m, a 2^m-th root whose orbit through the regular fixed point has exactly 2^m points, so the natural annulus-tower model with V-pieces is impossible
requires:
  - type-a-actors-closed-under-inner-twisted-lamp-wreaths
  - type-a-actors-closed-under-type-a-lamp-wreaths
distinct_from:
  type-a-actors-closed-under-inner-twisted-lamp-wreaths: that reduces G_1 ∈ B_A to the host condition (H); this rules out the two cheapest ways of meeting (H) and records the counting law any germ host must satisfy.
  higman-chain-group-lies-in-b-a: that (failed) tried a Kaloujnine--Krasner cocycle; item 1 here is the same obstruction for every lamp-wreath evaluation, not just for that cocycle.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed).

Notation as in (H) of `type-a-actors-closed-under-inner-twisted-lamp-wreaths`:
- `A = ⟨a, b | a^-1 b a = b^2⟩ ≤ Γ`, with `b ∈ Γ_0 = Stab(s_0)` and `A ∩ Γ_0 = ⟨b⟩`;
- `h : Γ_0 -> Λ` with `h(b) = e`, where `e` is the stable letter of `E = ⟨c, e | e^-1 c e = c^2⟩ ≤ Λ`.

Put `b_m = a^m b a^-m`, so `b_m^(2^m) = b`.

## Statement

1. **Evaluation twists are circular.** Let `Γ = Λ' wr_(S') Ω'` act on `S' × Y'` as in
   `type-a-actors-closed-under-type-a-lamp-wreaths`, and let `s_0 = (s', y')`. Suppose `h = ψ ∘ ev`,
   where `ev(f, ω) = f(s')` is evaluation on the stabilizer and `ψ : Λ'_(y') -> Λ` is a homomorphism.
   Then for some `k >= 1`, `Λ` contains an element conjugate to `e^(2^k)` by an element sending it to
   `e`. So `Λ` already contains a chain configuration of type `(2^k, 2)`: `x^-1 e x = e^(2^k)`,
   `e^-1 c e = c^2`, with `c` of infinite order. Products `Γ_1 × Γ_2` with `h` factoring through a
   stabilizer character of one factor reduce to that factor, with `A` embedded injectively in it.
2. **Counting law in germ hosts.** Suppose `Γ` is a group of homeomorphisms of the Cantor set, `s_0` is a
   regular point of every `b_m`, and `h` is the germ degree `Γ_0 -> Z` (as at a nonsingular rational
   point of a finite germ extension of `V`). Then for every `m >= 0`, the `b_m`-orbit of `s_0` has
   exactly `2^m` points. All of them are regular fixed points of `b` of degree one. In particular `b`
   has infinitely many hyperbolic fixed points of degree one, besides its fixed points `a^n s_0` of degree
   `2^n`.
3. **The annulus model fails.** Let `q` be an attractor of `a` with fundamental annuli
   `A_n = a^n(A_0)`, `n ∈ Z`, where `s_0 ∈ A_0`. There is no such host in which `b` preserves every `A_n`
   and acts on each by a finite-piece (V-like) map.

## Proof

- **Item 1.** Write `a = (f_a, ω_a)` and `b = (f_b, ω_b)`.
  - For `x, y` whose `Ω'`-parts fix a point `s`, `ev_s(xy) = ev_s(x) ev_s(y)`.
  - If the `Ω'`-part of `x` fixes `s`, then `ev_(ω_a s)(a x a^-1) = f_a(ω_a s) ev_s(x) f_a(ω_a s)^-1`.
  - From `b = a b^2 a^-1`, induction gives: `ω_b` fixes `ω_a^n s'` for all `n >= 0`, and
    `ev_(ω_a^n s')(b)` is conjugate to `ev_(s')(b)^(2^n)`.
  - `ψ(ev(b)) = e` has infinite order, so these values are nontrivial. Since `f_b` is finitely supported,
    the points `ω_a^n s'` repeat, say `ω_a^k s' = s'` with `k >= 1`.
  - Then `ev_(s')(b) = ev_(s')(a^k) ev_(s')(b)^(2^k) ev_(s')(a^k)^-1`. Apply `ψ`.
  - For products: `h(b) ≠ 1` forces the relevant coordinate of `b` to have infinite order. By Step 0 of
    `bs12-base-generator-centralizer-proof`, `A` then embeds in that factor.
- **Item 2.** `b_m` commutes with `b`, so it permutes the regular fixed points of `b` and preserves
  degrees.
  - Let the `b_m`-orbit of `s_0` have size `2^j`. It divides `2^m`, because `b_m^(2^m) = b` fixes `s_0`.
  - `b_m^(2^j)` fixes `s_0` with some integer degree `d`. Then
    `1 = deg_(s_0)(b) = deg_(s_0)((b_m^(2^j))^(2^(m-j))) = 2^(m-j) d`, so `j = m` and `d = 1`.
- **Item 3.** On `A_(-m)`, `b` is conjugate by `a^m` to `b_m` restricted to `A_0`. So `b|A_(-m)` is a
  `2^m`-th root of `b|A_0`, up to conjugacy. It preserves `A_(-m)` by assumption. By the argument of
  item 2 applied inside `A_0`, `b|A_0` has at least `2^m` regular fixed points of degree one, for every
  `m`. A finite-piece map of a clopen set has finitely many hyperbolic fixed points. ∎

## What is left

- **Where roots must live.** A host for (H) must let the roots `b_m` move `s_0` along orbits of size
  `2^m`. These orbits leave every annulus, so they accumulate at a singular point of `b`. That point is
  the repeller of `a` or an attractor of `a`.
- **The tame and linear routes are closed.** No tame host exists
  (`tame-power-conjugators-have-more-hyperbolic-points`), and no linear one (linear groups
  contain no chain configuration, by `higman-chain-group-pbh-iff-chain-configuration`).
- **The problem is dynamical.** The first open case is a single homeomorphism `b` of the Cantor set,
  singular at finitely many points. It needs a coherent family of `2^m`-th roots, whose orbits through
  `s_0` double at each level, conjugated among themselves by a `V`-like `a`. This is an odometer-like
  structure on the degree-one fixed points of `b`. Whether Rover–Nekrashevych-type odometers can supply
  it inside a finitely presented full group was not examined.

## Lesson for general BH

**A twist must be dynamical, not combinatorial.** Any finitely supported record of how a stabilizer
acts on its lamp, whether a cocycle, an evaluation, or a product coordinate, is pushed by the BS relation
onto an infinite orbit. It must then be either infinitely supported (the Kaloujnine–Krasner failure) or
periodic, which recreates the configuration inside the lamp. So a host has to carry the twist as a
**germ**, and infinite 2-divisibility of the base generator forces an **odometer on its degree-one fixed
points**: orbits of size `2^m` for every `m`. This is a sharp, checkable signature for any proposed
host of `G_1`, and so for `H4` and `BG`. A host needs an element whose regular fixed points carry a
2-adic odometer.

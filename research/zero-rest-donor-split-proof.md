---
rg: 2
id: zero-rest-donor-split-proof
kind: route
title: Declare every symbol active and let every site be its own donor, then read the open reduction's hypothesis as a strict automaton
target: few-rest-type-reduction-is-per-group-binary-descent
requires:
  - donor-covering-types-give-nonsurjunctive-size-progressions
  - ec-groups-share-the-nonsurjunctive-alphabet-sizes
artifacts:
  - experiments/zero-rest-donor-types-2026-09-17/check.py
---

Notation of the target.

**Item 1.** Let `β(x)(g) = μ((g^(-1)x)|_M)` be strict on `A^G`, where `M ∋ 1`. Put `Z = ∅` and `B = A`, which is
nonempty. The domain of the donor map is `{u ∈ A^M : μ(u) ∈ B} = A^M`. Put `d(u) = 1` for every `u`, so `D_x(g) = g`.
- (D1): if `β(x)(g) ∈ B`, then `x(D_x(g)) = x(g) ∈ A = B`.
- (D2): if `x(h) ∈ B`, take `g = h`. Then `β(x)(h) ∈ A = B` and `D_x(h) = h`.
- Self-relaying: if `u(1) ∈ B`, then `μ(u) ∈ A = B` and `d(u) = 1`.
- Strictness is a property of `β` alone and does not depend on the split.

So `β` is a strict self-relaying donor-covering automaton of type `(0, |A|)`, and `0 <= 2`. Conversely, a strict
donor-covering automaton on `L^G` is a strict automaton with `|L| >= 2`. Indeed `|L| >= 2`, because over one symbol
every automaton is bijective. So `|L| ∈ NS(G)`.

**Item 2.** The open reduction says: if `G` carries a strict donor-covering automaton of type `(z, b)` with `z <= 2`,
then `G` carries one of admissible type. By item 1 its hypothesis on `G` is equivalent to `NS(G) ≠ ∅`, and its
conclusion does not mention the given automaton. So it is equivalent to `(P)`. The reduction's text lists `(0, b)`
among the types to be covered ("types such as `(2, 4)`, `(1, 2)` and `(0, b)` are not covered"), so `z = 0` is in
its scope.

**Item 3.** Assume `(P)`, `NS(G) ≠ ∅`, and let `S` be a finite set of odd primes with product `P_S` (put `P_S = 1`
when `S = ∅`). By `(P)`, `G` carries a strict donor-covering automaton of admissible type `(z, b)`. By item 1 of
`donor-covering-types-give-nonsurjunctive-size-progressions`, `z + bt ∈ NS(G)` for every `t >= 1`. Choose `t` as
follows.
- `(1, b)`, `b` odd: `t = 2P_S`. Then `n = 1 + 2bP_S` is odd and `n ≡ 1 (mod p)` for `p ∈ S`.
- `(2, b)`, `b` odd: `t = P_S`. Then `bP_S` is odd, so `n = 2 + bP_S` is odd, and `n ≡ 2 (mod p)` for `p ∈ S`.
- `(2, b)`, `b ≡ 2 (mod 4)`: `t = 2P_S`. Then `bP_S ≡ 2 (mod 4)`, so `2bP_S ≡ 4 (mod 8)` and `n = 2 + 2bP_S ≡ 6
  (mod 8)`. Also `n ≡ 2 (mod p)` for `p ∈ S`.

In each case `4 ∤ n`, and `n ≢ 0 (mod p)` for `p ∈ S` since `p` is odd and `n ≡ 1` or `2`. With `S = {p}` this
rules out `∅ ≠ NS(G) ⊆ pℤ`.

**Item 4 (conditional).** Assume items 3 and 4 of `donor-covering-strict-automata-descend-to-two-symbols`.
- Assume `(P)` and `NS(G) ≠ ∅`. Then `G` carries an admissible type. Those items (tag multiplication to type
  `(2, (2^p - 2)/p)` or `(1, (2^(q-1) - 1)/q)`, then 3(a) or 3(b)) give `2 ∈ NS(G × C_p)` for a prime `p`. If
  `NS_all ≠ ∅`, apply this to any `G` with `NS(G) ≠ ∅`. Then `2 ∈ NS(G × C_p) ⊆ NS_all`.
- Restriction to existentially closed groups. Every group embeds in an existentially closed group, and
  `NS(K) = NS_all` for existentially closed `K` (item 3 of `ec-groups-share-the-nonsurjunctive-alphabet-sizes`).
  - Forward: if `NS_all ≠ ∅`, pick such a `K`. Then `NS(K) ≠ ∅`, and `(P)` for `K` together with the previous
    bullet gives `2 ∈ NS_all`.
  - Backward: assume universal binary descent, and let `K` be existentially closed with `NS(K) ≠ ∅`. Then
    `2 ∈ NS_all = NS(K)`. A binary strict `β` on `{0,1}^K` gives `β × id` on `({0,1} × {rest, active})^K`, with rest
    symbols `{0,1} × {rest}` and `d ≡ 1`. Its output at `g` is `(β(x)(g), e(g))`, so an active output site has an
    active input at `g` itself, which gives (D1). Every active input site `h` has an active output, which gives (D2).
    It is strict because `β` is and `id` is bijective. Its type is `(2, 2)`, which is admissible since `4 ∤ 2`.
  This direction uses no conditional item. ∎

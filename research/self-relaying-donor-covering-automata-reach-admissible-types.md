---
rg: 2
id: self-relaying-donor-covering-automata-reach-admissible-types
kind: claim
title: A strict donor-covering automaton with one or two rest symbols in which every active input site is its own donor turns into one of admissible type on the same group
distinct_from:
  donor-covering-few-rest-automata-reach-admissible-types: that asks for the 2-adic type reduction for every donor-covering automaton with at most two rest symbols; this proves it for the self-relaying ones, which include every witness item 5 of donor-covering-strict-automata-descend-to-two-symbols produces, and records where the same product fails without self-relaying.
  donor-covering-strict-automata-descend-to-two-symbols: that proves the descent from admissible types; this supplies admissible types from self-relaying witnesses of any active count.
  strict-automata-reduce-to-two-rest-donor-covering-ones: that is the universal rest-symbol reduction with a 2-adic condition on the target; this shows the condition can be dropped when the target is self-relaying.
  one-rest-donor-covering-strict-automata-raise-the-count: that proves every strict one-rest witness raises its active count; this is a positive construction that changes the active count's parity.
---

**ESTABLISHED** by `self-relaying-product-with-a-binary-identity`. Elementary.

Notation as in `donor-covering-strict-automata-descend-to-two-symbols`: `L = Z ⊔ B`, `τ(ℓ)(g) = μ((g^(-1)ℓ)|_M)`,
donor map `d` on `{u ∈ L^M : μ(u) ∈ B}`, conditions (D1) and (D2), type `(|Z|, |B|)`.

**Definition.** A donor-covering automaton is *self-relaying* if for every `u ∈ L^M` with `u(1) ∈ B` we have
`μ(u) ∈ B` and `d(u) = 1`. In words: an active input site stays active at the same site and is its own donor.
(D2) then holds automatically, with `g = h`.

**Theorem.** Let `G` be any group and `τ` a strict self-relaying donor-covering automaton of type `(z, b)` on `L^G`.
Then `τ × id` on `(L × {0,1})^G`, with rest symbols `Z × {0}`, is a strict self-relaying donor-covering automaton of
type `(z, 2b + z)`, with the same memory. Consequently:
1. if `z = 1`, then `G` carries a strict self-relaying donor-covering automaton of type `(1, b')` with `b'` odd;
2. if `z = 2`, then `G` carries one of type `(2, b')` with `4 ∤ b'` (take `τ` itself if `b` is odd, and `τ × id`,
   with `b' = 2b + 2 ≡ 2 mod 4`, if `b` is even).

**Every witness of item 5 is self-relaying.** Item 5 of `donor-covering-strict-automata-descend-to-two-symbols`
turns a strict `β` on `A^G` into `β × id` on `(A × {rest, active})^G` with donor `d ≡ 1`. An input `(a, active)`
at the identity gives output `(β(·)(1), active)`, active, with donor `1`. So that witness is self-relaying of type
`(|A|, |A|)`.

**Consequence for the universal problem** (conditional on items 3 and 4 of
`donor-covering-strict-automata-descend-to-two-symbols`, which the 2026-09-17 audit found sound while the node stays
OPEN at its title). The following are equivalent:
- `2 ∈ NS_all`;
- some group carries a strict self-relaying donor-covering automaton with one or two rest symbols, of any active count.

Forward: a binary strict `β` gives type `(2, 2)` by item 5, and that witness is self-relaying. Backward: the theorem
gives an admissible type, and items 3 and 4 give `2 ∈ NS_all`. So the rest-symbol reduction the universal route needs
(`strict-automata-reduce-to-few-rest-self-relaying-ones`) carries no 2-adic condition. What is left is purely
*death avoidance*: merge rest symbols from `k` down to two or one while no active input site ever becomes rest.
The route `donor-covering-phase-transport-proof` still lists `donor-covering-few-rest-automata-reach-admissible-types`,
which is only needed for witnesses that are not self-relaying.

**Scope.**
- The product fails for donor-covering automata that are not self-relaying, at (D2) of the product. Take a site `g`
  whose input in the first layer is rest, whose `τ`-output is active with donor `h ≠ g`, and whose second layer is
  `1`. The product's output at `g` is active, and `g` is now an active input site. With donors inherited from `τ` or
  taken to be the site itself, nobody else reads `g`, since `τ`'s donors point only to sites active in the first
  layer. So `g`'s single donor slot must relay both `g` and `h`, and if `g` is the only `τ`-relay of `h`, one of the two
  is lost. A redesigned donor map would have to send some other active output site to `g`, locally and for every
  configuration; no such choice is known. Products with shifts hit the same double duty. Alphabet powers `L^n` with one
  rest symbol have `(b+1)^n - 1` active symbols, which is even when `b` is even.
- Type `(0, b)` is out of scope: the product keeps `z = 0`.

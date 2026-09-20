---
rg: 2
id: few-rest-type-reduction-is-per-group-binary-descent
kind: claim
title: Every strict automaton is donor-covering with no rest symbols, so the few-rest 2-adic type reduction is a per-group binary descent statement
distinct_from:
  donor-covering-few-rest-automata-reach-admissible-types: that is the open reduction from every type with at most two rest symbols; this proves that its hypothesis holds on every group with a strict automaton, so as stated it is the per-group problem and not a 2-adic step.
  self-relaying-donor-covering-automata-reach-admissible-types: that fixes the 2-adic valuation for self-relaying witnesses with one or two rest symbols; this is the zero-rest case, where the same product keeps z = 0 and gives nothing.
  strict-automata-reduce-to-few-rest-self-relaying-ones: that asks for a death-free reduction to one or two rest symbols; this records that its title's bound "at most two" is met trivially by z = 0, and that only its body's z in {1, 2} carries content.
  ec-groups-share-the-nonsurjunctive-alphabet-sizes: that transfers alphabet sizes to existentially closed groups; this uses it to show the reduction restricted to those groups is exactly universal binary descent.
artifacts:
  - experiments/zero-rest-donor-types-2026-09-17/check.py
---

**ESTABLISHED** by `zero-rest-donor-split-proof`, items 1-3. Item 4 is conditional, as marked. Elementary.

Notation as in `donor-covering-strict-automata-descend-to-two-symbols`: `L = Z ⊔ B` with `B ≠ ∅`, local rule `μ` on
`L^M`, donor map `d`, (D1), (D2), type `(|Z|, |B|)`. *Self-relaying* is as in
`self-relaying-donor-covering-automata-reach-admissible-types`. A type is *admissible* if it is `(1, b)` with `b` odd
or `(2, b)` with `4 ∤ b`. `NS(G)` is as in `ec-groups-share-the-nonsurjunctive-alphabet-sizes`.

**Theorem.**
1. **Zero-rest normal form.** Every strict automaton `β` on `A^G` is a strict self-relaying donor-covering automaton
   of type `(0, |A|)`: take `Z = ∅`, `B = A`, `d ≡ 1`. So `G` carries a strict donor-covering automaton with at most
   two rest symbols iff `NS(G) ≠ ∅`.
2. **The open reduction as stated.** `donor-covering-few-rest-automata-reach-admissible-types` (whose text lists
   `(0, b)` among the types to be covered) is equivalent to: *every group `G` with `NS(G) ≠ ∅` carries a strict
   donor-covering automaton of admissible type.* Call this `(P)`.
3. **An arithmetic consequence inside one group.** `(P)` implies: for every `G` with `NS(G) ≠ ∅` and every finite
   set `S` of odd primes, `NS(G)` contains an `n` with `4 ∤ n` and `n ≢ 0 (mod p)` for all `p ∈ S`. In particular,
   under `(P)` no group has `∅ ≠ NS(G) ⊆ pℤ` for an odd prime `p`. This is a piece of the per-group statement
   `nonsurjunctive-alphabet-sizes-are-upward-closed`, which is open.
4. **Universal strength** (conditional on items 3 and 4 of `donor-covering-strict-automata-descend-to-two-symbols`,
   audited sound while that node is OPEN at its title).
   - `(P)` implies per-group descent to `G × C_p`: if `NS(G) ≠ ∅` then `2 ∈ NS(G × C_p)` for some prime `p`. Hence
     `(P)` implies `some-nonsurjunctive-group-gives-a-binary-one`.
   - `(P)` restricted to existentially closed groups is equivalent to `some-nonsurjunctive-group-gives-a-binary-one`.

**Why it matters.**
- **The last prerequisite of `donor-covering-phase-transport-proof` is not a last-mile step.** The route and the
  2026-09-17 audit read `donor-covering-few-rest-automata-reach-admissible-types` as the small 2-adic bookkeeping step
  left after items 1-5. By item 1 its hypothesis is just `NS(G) ≠ ∅`. So it is the whole per-group problem, with a
  conclusion that does not depend on the automaton it is given. With item 4 it proves the universal target alone.
  The route therefore reformulates the target and does not reduce it.
- **The same zero-rest reading applies to two titles.**
  - The title of `donor-covering-strict-automata-descend-to-two-symbols` ("descends ... once it has at most two
    rest symbols") includes `z = 0`. Read literally, it says every strict automaton on `G` descends to a binary one
    over some `G × C_p`.
  - The title of `strict-automata-reduce-to-few-rest-self-relaying-ones` ("at most two rest symbols") is met
    trivially by item 1. Only its body's scope `z ∈ {1, 2}` has content, and the route
    `universal-binary-descent-via-death-free-rest-reduction` uses the body.
- **Decomposition.** The open reduction splits into two statements. Either can fail without the other.
  - *Zero rest symbols.* This is `(P)` itself, at least as strong as universal binary descent by item 4.
  - *One or two rest symbols.* A group carrying a strict donor-covering automaton of type `(z, b)` with
    `z ∈ {1, 2}` carries one of admissible type. This is the genuine 2-adic step. The self-relaying case is
    established. Still open: `(1, b)` with `b` even and `(2, b)` with `4 | b`, with births that relay to a donor
    other than themselves.
- **Where the zero-rest case sits.** Every move on record keeps `z = 0`: tag multiplication, identity layers with
  `Z × {0}` as rest (empty here), and products with shifts. So from `(0, k)` a route must create rest symbols, and
  from `β × id` of type `(k, k)` it must merge them. No recorded design does either on a group. Any witness with
  `1 <= z <= 2` has `Z^G` invariant, because an all-rest window outputs a rest symbol by (D1). For `z = 1` it must
  also raise the active count on some finite configuration (`one-rest-donor-covering-strict-automata-raise-the-count`).

**Calibration** (`experiments/zero-rest-donor-types-2026-09-17/check.py`). Over `C_3`, `C_4` and `C_5` with `k = 2, 3`,
the zero-rest split of 30 random rules per case satisfies (D1), (D2) and self-relaying on every configuration. This
checks the definitions only, since no automaton over a finite group is strict. The arithmetic choices of item 3 are
checked for `b < 200` and sets of up to three odd primes below 40.

---
rg: 2
id: single-register-rings-divide-unit-at-finitely-many-primes
kind: claim
title: With one unbounded register per state type and shift or reset letters, K_0 of a register completion divides a unit class of infinite order at only finitely many primes
distinct_from:
  resolvent-register-units-give-rational-symbols: that is a K_1 and K_2 obstruction from invertible register units; this is a K_0 obstruction to divisibility of [1], and it holds whatever the coefficients are.
  fp-simple-resolvent-ring-with-divisible-unit-class: that is the design target; this rules out, for it, every design with one register per type and bounded multiplicities.
  capacity-chain-resolvent-ring-has-rational-k0: that is a candidate with two comparable registers and unbounded multiplicities, which lies outside the hypotheses here.
artifacts:
  - research/artifacts/gq-gq-k2-q-register-symbols.md
---

**ESTABLISHED (2026-09-18)** through `single-register-rings-divide-unit-at-finitely-many-primes-proof`. Lane
proof (gq-k2-q), not independently reviewed. Part 2 is an implication from hypothesis (P) of
`resolvent-register-units-give-rational-symbols`; it does not assert (P).

## Statement

1. **Divisibility lemma.** Let `C` be an abelian group obtained from a finitely generated module over a finitely
   generated commutative ring by finitely many steps of two kinds:
   - extensions by finitely generated abelian groups;
   - quotients by finitely generated subgroups.

   If `x ∈ C` has infinite order, then `x ∈ ∩_e p^e C` for only finitely many primes `p`. In particular `x` is not
   divisible by every positive integer.
2. **Register completions.** Let `R` be a register completion, in the sense of
   `resolvent-register-units-give-rational-symbols`, that satisfies (P). Assume:
   - finitely many state types, each carrying one register `N` with values in `N = {0,1,2,...}`;
   - the coefficient ring `B⁺` is finitely supported functions plus tails in a localization of `Q[N]`, any
     resolvents allowed;
   - each letter acts on `N` by a shift `N ↦ N + a` or a reset `N ↦ c`;
   - each availability condition is eventually constant in `N`.

   Then `K_0(R) = coker(1 − [X] on K_0(B⁺))` satisfies the hypothesis of part 1. So if `[1]` has infinite order,
   it is divisible by all powers of `p` for only finitely many `p`, and `K_0(R)` contains no copy of `Q·[1]`.

## Consequence for the design target

Items 3 and 4 of `fp-simple-resolvent-ring-with-divisible-unit-class` cannot both hold for such a design. The
reasons are:
- resolvents and other non-constant coefficients do not change `K_0(B⁺)`, which is the group of indicator
  classes `LC(N ∪ ∞, Z)` per type;
- bounded multiplicities make the relations eventually shift-equivariant.

Divisibility at infinitely many primes needs relations of unbounded support. That means a letter whose target set
contains unboundedly many states of the same type at a given level, as `d` does in `R_cap`, where the fibre `{L = k}`
has `k + 1` points. With finitely many letters this needs a second register whose range depends on the first,
which is the comparison that `capacity-chain-presentation-is-not-simple` shows to be costly. Substitutions that
are neither shifts nor resets, for example `N ↦ 2N`, are also outside part 2 and remain open.

## Scope of hypothesis (P)

`register-completion-pimsner-from-supercoherence` (lane `gq-ring-fp-simple`, 3542cca5d; re-review by `gq-referee-a`
and `gq-referee-b` pending) proves (P) for single-register completions with a *spine*: each type is the range of
a letter available on every target.
- In that setting the statement above holds without assuming (P), provided the coefficient ring contains every point indicator `δ_n`, i.e. `⊕_N Q ⊆ B⁺` at each type (scope amendment db70a3dbb, from `gq-referee-b` 852a0771f). The `B⁺` described here, finitely supported functions plus tails, includes them.
- The hypotheses match: one register per type; shift, dilation and reset letters; `B⁺` the eventually rational
  coefficient ring.
- Designs without a spine still need (P) as a hypothesis.

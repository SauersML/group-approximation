---
rg: 2
id: eventually-rational-register-ring-is-regular-supercoherent
kind: claim
title: The eventually-rational register ring B+ is von Neumann regular, so regular coherent; whether it is supercoherent (its polynomial rings are coherent) is the one open input to the Pimsner sequence
distinct_from:
  register-completion-pimsner-from-supercoherence: that reduces (P) to this statement; this is the commutative-algebra statement itself.
  abc-twisted-laurent-k-theory-fibration: that is the ABC theorem needing a regular supercoherent coefficient ring; this asks whether B+ is one.
---

**PARTLY ESTABLISHED, one part OPEN.** Let `B⁺` be the coefficient ring of a single-register
completion: `Q`-valued functions `f` on the states such that, at each type, `f(N)` is a
fixed rational function of `N` for all large `N`, with arbitrary values at finitely many
states, closed under the register resolvents `(N + c)^(-1)`.

1. **ESTABLISHED (lane proof):** `B⁺` is a commutative von Neumann regular ring. Hence it
   is reduced, of Krull dimension `0`, and **regular coherent**: finitely generated ideals
   are direct summands, and every module has projective dimension `0`.
2. **OPEN:** `B⁺` is **supercoherent**, that is `B⁺[t_1, ..., t_p]` is coherent for every
   `p`. Equivalently, `B⁺` is regular supercoherent, since regular coherent plus
   supercoherent is the definition (ABC §7).

Part 2 is the single remaining input to
`register-completion-pimsner-from-supercoherence`, hence to
`single-register-rings-divide-unit-at-finitely-many-primes`,
`dilation-letters-cannot-divide-the-unit-class` and
`top-determined-register-rings-cannot-divide-the-unit`.

## Proof of part 1
Given `f ∈ B⁺`, define `g` by `g(state) = 1/f(state)` where `f ≠ 0`, and `0` where
`f = 0`. Then `g ∈ B⁺`:
- at each type, for large `N`, `f(N) = P(N)/Q(N)` with `Q` nowhere zero on the tail;
- if `P` is not the zero polynomial, `P(N) ≠ 0` for all large `N`, so `g(N) = Q(N)/P(N)`
  is eventually rational, and the finitely many tail zeros of `P` plus the finitely many
  off-tail states are the "arbitrary at finitely many states" freedom;
- if `P ≡ 0`, then `f` is eventually `0` and `g` is eventually `0`.

By construction `f g f = f`. So every element is von Neumann regular. A commutative von
Neumann regular ring is reduced of Krull dimension `0`, and von Neumann regular rings are
coherent with every module flat, so `B⁺` is regular coherent. ∎

## Structure, and why part 2 is not automatic
- **Germ at infinity.** For a single type, the map `B⁺ -> Q(t)`, sending `f` to its
  eventual rational function, is a surjective ring homomorphism onto the field `Q(t)`, with
  kernel the finitely supported functions `⊕_ℕ Q`. So
  `0 -> ⊕_ℕ Q -> B⁺ -> Q(t) -> 0`.
  `Q(t)` is regular supercoherent (a field). `⊕_ℕ Q` is a von Neumann regular non-unital
  ideal.
- **The obstacle.** Von Neumann regular does not imply supercoherent. Soublin gave a
  commutative coherent ring whose polynomial ring is not coherent, and there are von
  Neumann regular rings `A` for which `A[t]` is not coherent (an infinite product of fields
  can fail; the relevant question is for the countable ring `B⁺`). So part 2 needs the
  specific structure of `B⁺`, not just regularity.
- **What would suffice.** Any one of:
  - `B⁺[t]` coherent, then by induction `B⁺[t_1..t_p]` coherent (a ring `A` with `A[t]`
    coherent and `A` "stably coherent" gives all `p`);
  - `B⁺` is `ℵ_0`-Noetherian, or self-`FP`-injective, either of which makes a commutative
    von Neumann regular ring supercoherent;
  - the extension `0 -> ⊕_ℕ Q -> B⁺ -> Q(t) -> 0` transfers supercoherence from its
    ends, which is not a general fact but may hold here because `⊕_ℕ Q` is a filtered
    colimit of the supercoherent `Q^n`.

## Attempts
1. **`⊕_ℕ Q` alone (2026-09-18, lane `gq-ring-fp-simple`).** The non-unital ring `⊕_ℕ Q`
   is the filtered colimit of `Q^n`, each a finite product of fields, hence regular
   supercoherent. Coherence is preserved under filtered colimits with flat transition maps
   (the inclusions `Q^n -> Q^(n+1)` are split, hence flat), so `⊕_ℕ Q` is coherent, and so
   is its polynomial ring by the same colimit, because `(⊕_ℕ Q)[t] = colim Q^n[t]`. So the
   ideal end is supercoherent. The unresolved step is combining it with the field quotient
   `Q(t)`: coherence is not exact in general.
2. **Direct product model (not `B⁺`).** The full product `∏_ℕ Q` is von Neumann regular and
   self-injective, hence regular supercoherent (Villamayor--Zelinsky type). `B⁺` is a
   countable subring of it containing `⊕_ℕ Q`. Supercoherence does not pass to subrings, so
   this does not settle `B⁺`, but it makes the answer plausible.

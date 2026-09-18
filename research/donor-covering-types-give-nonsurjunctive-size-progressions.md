---
rg: 2
id: donor-covering-types-give-nonsurjunctive-size-progressions
kind: claim
title: A strict donor-covering automaton of type (z, b) puts every size z + bt in NS(G), so a binary-power witness exists exactly at power-residue types
distinct_from:
  donor-covering-strict-automata-descend-to-two-symbols: that descends admissible types to two symbols over G × C_p and is open at its scope; this keeps the group and reads tag multiplication as a statement about alphabet sizes, with a weaker arithmetic condition that suffices for binary-power witnesses.
  donor-covering-few-rest-automata-reach-admissible-types: that asks for the 2-adic reduction to types (2, b) with 4 ∤ b or (1, b) with b odd; this needs only z ≡ 2^j (mod b), which those types satisfy and types such as (3, 5), (5, 3) and (z, 1) also satisfy.
  ec-groups-share-the-nonsurjunctive-alphabet-sizes: that proves NS(G) closed under multiples; this proves NS(G) contains the progression z + bt for any strict donor-covering type, which is a non-multiplicative closure once gcd(z, b) < z.
  nonsurjunctive-alphabet-sizes-are-upward-closed: that asks for k in NS(G) to give every larger size; this gives every size above z from a single-active-symbol witness with z rest symbols.
artifacts:
  - experiments/donor-power-residue-2026-09-17/check.py
---

**ESTABLISHED** by `donor-type-tag-lift-size-progression-proof`. Elementary and self-contained.

**Setting** (as in `donor-covering-strict-automata-descend-to-two-symbols`). `G` is any group. A finite alphabet
`L = Z ⊔ B` has rest symbols `Z` and active symbols `B ≠ ∅`. An automaton is `τ(ℓ)(g) = μ((g^(-1)ℓ)|_M)` with
`M ∋ 1` finite and `(g^(-1)ℓ)(m) = ℓ(gm)`. It is *donor-covering* if there is `d` from `{u ∈ L^M : μ(u) ∈ B}`
to `M` such that, with `D_ℓ(g) = g·d((g^(-1)ℓ)|_M)`: (D1) `ℓ(D_ℓ(g)) ∈ B` whenever `τ(ℓ)(g) ∈ B`; (D2) for every
`ℓ` and `h` with `ℓ(h) ∈ B` some `g` with `τ(ℓ)(g) ∈ B` has `D_ℓ(g) = h`. The type is `(|Z|, |B|)`. Strict means
injective and not surjective. `NS(G)` and `NS_all` are as in `ec-groups-share-the-nonsurjunctive-alphabet-sizes`.
Call a type `(z, b)` *power-residue* if `z + bt` is a power of two for some integer `t >= 1`.

**Theorem.** Let `G` carry a strict donor-covering automaton of type `(z, b)`.
1. **Progression.** For every `t >= 1`, `G` carries a strict donor-covering automaton of type `(z, bt)`, with the
   same memory. So `z + bt ∈ NS(G)` for every `t >= 1`.
2. **One active symbol.** If `b = 1`, every integer `n > z` lies in `NS(G)`.
3. **Arithmetic.** Write `b = 2^v b'` with `b'` odd. The type `(z, b)` is power-residue iff `2^v | z` and
   `z / 2^v ≡ 2^i (mod b')` for some `i >= 0`. In particular `gcd(z, b)` is then a power of two. Examples: `(z, 1)`
   for every `z`; `(1, b)` with `b` odd; `(2, b)` with `4 ∤ b`; `(z, b)` with `b` an odd prime having `2` as a
   primitive root and `b ∤ z`, e.g. `(3, 5)`, `(5, 3)`, `(2, 11)`.
4. **Bridge equivalence.** `some-nonsurjunctive-group-gives-a-binary-power-one` holds iff: whenever `NS_all ≠ ∅`,
   some group carries a strict donor-covering automaton of power-residue type.
5. **Consequence of binary-power surjunctivity.** If `every-group-is-surjunctive-over-binary-power-alphabets`
   holds, then over every group every injective donor-covering automaton of power-residue type is surjective. In
   particular every injective donor-covering automaton with exactly one active symbol is surjective, for any number
   of rest symbols.

**Why it matters.**
- The route `gottschalk-via-binary-power-nonsurjunctive-witness` needs the target of item 4 together with
  binary-power surjunctivity. Item 4 replaces its bridge by *reaching a power-residue type*. That is strictly weaker
  arithmetic than what binary descent over `G × C_p` needs (types `(2, b)`, `4 ∤ b`, or `(1, b)`, `b` odd).
- **The invariant that blocks it.** A strict `β` over `k` symbols gives type `(k, k)` (item 4, first direction).
  Tag multiplication (item 1) gives `(z, bt)`, identity layers `τ × id_P` give `(z|P|, b|P|)`. Both keep
  `gcd(z, b)` a multiple of `k`, while item 3 needs `gcd(z, b)` to be a power of two. So every construction built
  from these moves dies at the odd part of `gcd(z, b)`. A proof must merge active symbols or change the rest count
  non-multiplicatively while keeping (D2).
- **A construction recipe.** Item 5 says that a counterexample to binary-power surjunctivity may be sought as a
  strict automaton in which one symbol behaves as a particle that is never created from nothing and never
  annihilated without a relay, over any number of rest symbols. By `passive-fixing-injective-automata-are-surjective`
  such particles must move. With one rest symbol they must also multiply on some finite configuration
  (`one-rest-donor-covering-strict-automata-raise-the-count`). With at least two rest symbols no such constraint is
  known.

**Calibration** (`experiments/donor-power-residue-2026-09-17/check.py`). The criterion of item 3 agrees with brute
force for `0 <= z < 80`, `1 <= b < 80`. Over `G = C_3`, for 161 donor-covering rules of types `(2,1)`, `(1,2)`, `(3,1)`
and `(2,2)`, the lift of item 1 satisfies `σ∘Φ = τ∘σ`, commutes with translation and with the phase action, and is
injective iff `τ` is. Strictness cannot occur over a finite group, so this checks the algebra only.

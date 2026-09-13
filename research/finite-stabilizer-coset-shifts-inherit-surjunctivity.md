---
rg: 2
id: finite-stabilizer-coset-shifts-inherit-surjunctivity
kind: claim
title: If a group is surjunctive at alphabet size m, every injective equivariant self-map of a finite-stabilizer coset shift at size m is surjective
distinct_from:
  site-pullbacks-strict-iff-stabilizer-self-compressed: that shows one-site pullbacks are never strict on a coset shift with finite stabilizers; this transfers surjunctivity of the group to every continuous equivariant self-map of such a coset shift, whatever sites it reads.
  compressed-coset-shifts-carry-strict-equivariant-embeddings: that builds strict self-embeddings of coset shifts with infinite, self-compressed stabilizers; this asks whether finite stabilizers can carry strictness that the regular action does not.
  invariant-output-injective-automata-need-invisible-symmetry: that constrains injective automata from the full shift into right-coset-invariant configurations; this concerns self-maps of the coset shift itself and extends them to automata on the full shift.
artifacts:
  - research/artifacts/finite-stabilizer-coset-shift-transfer-2026-09-12.md
---

**OPEN.** Let `G` be a group, `H` a finite subgroup, and `m >= 2`. Suppose every injective cellular
automaton on `(Z/m)^G` is surjective. Then every continuous, `G`-equivariant, injective self-map of the
coset shift `A^(G/H)` with `|A| = m` is surjective.

For `H = 1` this is the hypothesis. So the claim says finite stabilizers carry no strictness beyond the
host's own at a fixed alphabet size.

**Status.**
- **Proved when `gcd(m, |H|) = 1`** (artifact Section 1; unverified, verifier w4-vf-positive-b).
  - Identify `A^(G/H)` with the right-`H`-invariant configurations `Y` in `(Z/m)^G`.
  - Averaging over `H` gives an idempotent linear automaton `P` onto `Y`.
  - A self-map `tau` of `Y` extends to the automaton `Phi(z) = tau(Pz) + (z - Pz)`.
  - `Phi` is injective iff `tau` is, surjective iff `tau` is, and `Phi(X) ∩ Y = tau(Y)`.
- **Open when a prime divides both `m` and `|H|`.** The averaging step has no replacement there (Attempts).

**Why a positive lane cares.**
- Coset shifts with finite stabilizers are exactly the codomains that survive:
  - invariant-output designs map into them (`leavitt-units-carry-injective-invariant-output-automaton`);
  - they remain admissible for measurable compression (`bernoulli-factors-to-infinite-stabilizer-coset-shifts-trivial`).
- `compressed-coset-shifts-carry-strict-equivariant-embeddings` shows a positive proof must use freeness of
  the regular action. In the coprime case finite stabilizers are enough: a proof of surjunctivity of `G` at
  size `m` already covers every such coset shift.
- So a finite-stabilizer coset shift can be more flexible than its host only at a shared prime. A strict
  self-map there, over a host where the claim's hypothesis holds, would show that positive mechanisms have
  to see the regular action itself, not only finiteness of stabilizers.

## Attempts

- **Linear averaging (w6-free-pos-d, 2026-09-12).** Works exactly when `|H|` is a unit mod `m`: the only
  symmetric linear retraction onto `Y` with block memory is `c sum_h z(kh)` with `c |H| = 1`. Artifact
  Section 1.
- **Translation-equivariant retractions at a shared prime.** Suppose `p` divides `m` and `|H|`. Then no
  automaton `X -> Y` commutes with adding constants, whatever its memory. Take `h in H` of order `p`,
  enlarge the memory to be `h`-invariant, and give the input `z(khf) = z(kf) + m/p` along `h`-orbits. The
  rule must then return `mu = mu + m/p`. So every extension of the form `tau(Pz) + (z - Pz)` with a
  gauge-shift `P` fails. Artifact Section 2 (to land).
- **Min retraction.** `rho(z)(k) = min_h z(kh)` is an automaton retraction onto `Y` for every ordered
  alphabet. Its fibres have sizes that depend on the base symbol, so the fibre coordinate cannot be moved
  to the new base `tau(rho(z))`. Artifact Section 2 (to land).
- **Alphabet changes.** Products of alphabets keep the shared prime. Enlarging `A` to `B` with `|B|` coprime
  to `|H|` needs an injective extension of `tau` to `B^(G/H)`, a marker problem. Not attempted.
- **Linear shadow** (artifact Section 3, to land). By duality, linear surjunctivity of `K^(G/H)` means that
  surjective `K[G]`-endomorphisms of `K[G/H]^n` are injective.
  - If `char K` does not divide `|H|`, then `K[G/H] ≅ K[G]e` is projective, surjections split, and stable
    finiteness of `K[G]` finishes.
  - If `char K = p` divides `|H|`, the module is not projective. Its endomorphism ring is the mod-`p` Hecke
    algebra of `(G, H)`.
- **Amenable hosts.** The claim holds at every `m`. `Y` is a strongly irreducible subshift of finite type
  (gap `H`), so a proper subshift has smaller entropy. This is standard and is not landed as a claim.

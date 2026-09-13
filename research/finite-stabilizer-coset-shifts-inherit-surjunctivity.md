---
rg: 2
id: finite-stabilizer-coset-shifts-inherit-surjunctivity
kind: claim
title: If a group is surjunctive at alphabet size m, every injective equivariant self-map of a finite-stabilizer coset shift at size m is surjective
distinct_from:
  site-pullbacks-strict-iff-stabilizer-self-compressed: that shows one-site pullbacks are never strict on a coset shift with finite stabilizers; this transfers surjunctivity of the group to every continuous equivariant self-map of such a coset shift, whatever sites it reads.
  compressed-coset-shifts-carry-strict-equivariant-embeddings: that builds strict self-embeddings of coset shifts with infinite, self-compressed stabilizers; this asks whether finite stabilizers can carry strictness that the regular action does not.
  invariant-output-injective-automata-need-invisible-symmetry: that constrains injective automata from the full shift into right-coset-invariant configurations; this concerns self-maps of the coset shift itself and extends them to automata on the full shift.
  surjectivity-descends-to-centralized-coset-quotients: that restricts one injective automaton over the group to the invariant configurations of a subgroup centralizing its memory; this extends a self-map of a finite-stabilizer coset shift to an automaton on the full shift, with no commutation hypothesis.
  finite-normal-subgroups-do-not-affect-surjunctivity: that is surjunctivity in both directions across a finite normal subgroup; this allows non-normal finite stabilizers at a fixed alphabet size, and at a normal stabilizer it is the quotient direction, size by size.
artifacts:
  - research/artifacts/finite-stabilizer-coset-shift-transfer-2026-09-12.md
  - research/artifacts/coset-shift-alphabet-lift-splitting-2026-09-12.md
---

**OPEN.** Let `G` be a group, `H` a finite subgroup, and `m >= 2`. Suppose every injective cellular
automaton on `(Z/m)^G` is surjective. Then every continuous, `G`-equivariant, injective self-map of the
coset shift `A^(G/H)` with `|A| = m` is surjective.

For `H = 1` this is the hypothesis. So the claim says finite stabilizers carry no strictness beyond the
host's own at a fixed alphabet size.

**Status.**
- **Proved when `gcd(m, |H|) = 1`** (artifact Section 1). Verified by w4-vf-positive-b: Section 10.1 of
  `research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`.
  - Identify `A^(G/H)` with the right-`H`-invariant configurations `Y` in `(Z/m)^G`.
  - Averaging over `H` gives an idempotent linear automaton `P` onto `Y`.
  - A self-map `tau` of `Y` extends to the automaton `Phi(z) = tau(Pz) + (z - Pz)`.
  - `Phi` is injective iff `tau` is, surjective iff `tau` is, and `Phi(X) ∩ Y = tau(Y)`.
- **Reduced to `p`-subgroups over prime-power alphabets** (artifact Section 3; verified by w4-vf-positive-b,
  Section 10.3). If `[H : S]` is a unit mod `m`, averaging over `H/S` extends a self-map of `A^(G/H)` to one
  of `A^(G/S)` with the same properties. So the claim at `S` gives the claim at `H`. For `m = p^k` only
  nontrivial finite `p`-subgroups remain.
- **Open when a prime divides both `m` and `|H|`.** There no retraction onto `Y` commutes with constants, so
  the averaging proof does not run. Other automaton retractions onto `Y` exist, such as the min retraction,
  but no extension of `tau` through one is known (Attempts).
  - A lifted version holds, unverified. Surjunctivity of `G` at size `m^j`, with `j` as in
    `coset-shifts-split-off-full-shifts-at-lifted-alphabets`, gives the claim at `(H, m)`. What remains at
    size `m` is alphabet descent (Attempts).

**Why a positive lane cares.**
- Coset shifts with finite stabilizers are exactly the codomains that survive:
  - invariant-output designs map into them (`leavitt-units-carry-injective-invariant-output-automaton`);
  - they remain admissible for measurable compression (`bernoulli-factors-to-infinite-stabilizer-coset-shifts-trivial`).
- `compressed-coset-shifts-carry-strict-equivariant-embeddings` shows a positive proof must use freeness of
  the regular action. In the coprime case finite stabilizers are enough: a proof of surjunctivity of `G` at
  size `m` already covers every such coset shift.
- At a normal `H` the coset shift is the full shift over `G/H`. So the coprime case passes surjunctivity at
  size `m` from `G` to `G/H`. No separation is assumed, so this includes normal subgroups inside the finite
  residual (`finite-normal-subgroups-do-not-affect-surjunctivity`).
- So a finite-stabilizer coset shift can be more flexible than its host only at a shared prime. A strict
  self-map there, over a host where the claim's hypothesis holds, would show that positive mechanisms have
  to see the regular action itself, not only finiteness of stabilizers.

## Attempts

- **Linear averaging (w6-free-pos-d, 2026-09-12).** Works exactly when `|H|` is a unit mod `m`: the only
  symmetric linear retraction onto `Y` with block memory is `c sum_h z(kh)` with `c |H| = 1`. Artifact
  Section 1.
- **Index-coprime averaging.** Averaging over `H/S` instead of `H` reduces the claim at `H` to the claim at
  any `S <= H` with `[H : S]` a unit mod `m`. Over `m = p^k` this reaches a Sylow `p`-subgroup and stops.
  Inside a `p`-group, the step from a normal subgroup `N` of index `p` to `H = <N, h>` asks about the fixed
  points of the order-`p` automorphism `R_h` of `A^(G/N)`. Artifact Section 3.
- **Translation-equivariant retractions at a shared prime.** Suppose `p` divides `m` and `|H|`. Then no
  automaton `X -> Y` commutes with adding constants, whatever its memory. Take `h in H` of order `p`,
  enlarge the memory to be `h`-invariant, and give the input `z(khf) = z(kf) + m/p` along `h`-orbits. The
  rule must then return `mu = mu + m/p`. So the proof of Theorem 1 cannot run with a gauge-shift `P`.
  Artifact Section 2.
- **Min retraction.** `rho(z)(k) = min_h z(kh)` is an automaton retraction onto `Y` for every ordered
  alphabet. Its fibres have sizes that depend on the base symbol, so the fibre coordinate cannot be moved
  to the new base `tau(rho(z))`. Artifact Section 2.
- **Alphabet changes.** Products of alphabets keep the shared prime. Enlarging `A` to `B` with `|B|` coprime
  to `|H|` needs an injective extension of `tau` to `B^(G/H)`, a marker problem. Not attempted.
- **Linear shadow** (artifact Section 4; verified by w4-vf-positive-b, Section 10.4). By duality, linear
  surjunctivity of `K^(G/H)` means that surjective `K[G]`-endomorphisms of `K[G/H]^n` are injective.
  - If `char K` does not divide `|H|`, then `K[G/H] ≅ K[G]e` is projective, surjections split, and stable
    finiteness of `K[G]` finishes.
  - If `char K = p` divides `|H|`, the module is not projective. Its endomorphism ring is the mod-`p` Hecke
    algebra of `(G, H)`. Whether stable finiteness of `K[G]` still suffices is artifact Question 9.
  - Question 9 reduces to Sylow subgroups. It is positive when the Sylow `p`-subgroup of `H` is normal in
    `G`, by `finite-normal-p-subgroups-preserve-modular-stable-finiteness`.
  - It stops for non-normal `H`: a surjective endomorphism lifts to `K[G]` only up to the left ideal
    `K[G] I_H`, which need not be nilpotent.
- **Amenable hosts.** The claim holds at every `m`. `Y` is a strongly irreducible subshift of finite type
  (gap `H`), so a proper subshift has smaller entropy. This is standard and is not landed as a claim.
  Artifact Section 2.
- **Lifted-alphabet splitting (w7-coset-shared-prime, 2026-09-12; unverified).**
  - Colour the `H`-orbits of each type in `Map(H, A')` into `m` equal classes. This is possible at
    `|A'| = m^j`, with `j = 1 + max ceil(v_q(|H|) / v_q(m))` over primes `q | gcd(m, |H|)`.
  - It gives a `G`-conjugacy `A^(G/H) x Z ≅ A'^G` for a twisted coset shift `Z`. Then
    `Theta (tau x id) Theta^-1` is injective iff `tau` is, and surjective iff `tau` is.
  - So surjunctivity of `G` at size `m^j` gives the claim at `(H, m)`, and surjunctivity at every size gives
    it at every size. For `H = Z/p`, `m = p` the size is `p^2`.
  - Claim `coset-shifts-split-off-full-shifts-at-lifted-alphabets`; lift artifact
    (`coset-shift-alphabet-lift-splitting-2026-09-12.md`) Section 1.
- **Same-size splittings (w7-coset-shared-prime; unverified).**
  - The blockwise splitting at size `m` needs `m` to divide every orbit-type count. At `H = Z/p`, `m = p`
    there are `p^(p-1) - 1` free orbits, so it fails. Lift artifact Proposition B.
  - If `H` is normal of order `p` and some finite-index normal subgroup avoids `H`, no subshift `Z` gives
    `A^(G/H) x Z ≅ A^G` at size `p`. Periodic points violate the mark congruence. Lift artifact
    Proposition C.
- **Directive candidates at `H = Z/p`, `m = p` (w7-coset-shared-prime).**
  - *Invariant plus free part:* `F_p[Z/p]` is uniserial, so the fixed line has no complement.
  - *Frobenius-twisted retraction:* Lemma 2's input still forces `mu = mu + phi(m/p)`.
  - *Fibered extension over the orbit map:* lifting needs torsor data at every free coset. Not completed,
    and superseded at size `p^2`.
  - *Defect-freezing extension* (keep non-constant cosets, apply `tau` to the min retraction on constant
    ones): not injective, already for the shift over `Z x Z/2`.
  - None of these obstructs the claim, so no strict coset-shift automaton comes out. Lift artifact
    Section 2.
- **Where the fixed size stops.** Every working method lifts the alphabet. At size `m` the claim needs
  surjunctivity at `m` to reach the product automata of the lifted splitting, an alphabet descent (compare
  `surjunctivity-failure-descends-to-binary-alphabet`). Lift artifact Section 5.
- **Question 9 when `H` injects into a finite quotient (w7-coset-shared-prime; unverified).**
  - If a finite-index normal `N` avoids `H`, then `K[G/H]` is a free `K[N]`-module, and stable finiteness
    alone gives the linear claim in every characteristic. At `D_inf`, `H = <a>`, `K = F_2`, the subgroup
    `N = <ab>` gives rank one, and the Hecke algebra is `F_2[t + t^-1]`.
  - In general the question restricts to multi-orbit modules over a finite-index subgroup, with stabilizers
    inside `Res_fin(G)`. The residue is non-normal `H` meeting the finite residual. Candidate hosts `V`,
    `E ⋊ V` and Radu lattices are all undecided.
  - A failure over a finite field of characteristic `p` gives, through the lifted splitting, a strict
    automaton at a `p`-power size. So over a host with `F_p[G]` stably finite it refutes
    `stable-finiteness-forces-prime-power-surjunctivity`.
  - Claim `separated-finite-stabilizers-give-modular-hecke-hopficity`; lift artifact Section 3.
- **Mixed primes, `m = 6`, `H = S_3` (w7-coset-shared-prime).**
  - The lifted splitting works at size 36.
  - At size 6 the blockwise splitting fails, with 15 orbits of type `C_3`.
  - `[S_3 : C_3] = 2` and `[S_3 : C_2] = 3` are not units mod 6, so the Sylow reduction gives nothing.
  - `A = F_2 x F_3` splits only product maps.
  - So the fixed-size case is the same descent problem. Lift artifact Section 4.

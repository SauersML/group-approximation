---
rg: 2
id: coset-shifts-split-off-full-shifts-at-lifted-alphabets
kind: claim
title: A finite-stabilizer coset shift at size m times a twisted coset shift is conjugate to the full shift at size m^j
distinct_from:
  finite-stabilizer-coset-shifts-inherit-surjunctivity: that transfers surjunctivity at the same alphabet size m and is open at a shared prime; this splits the coset shift off the full shift at size m^j by an orbit colouring, so it transfers surjunctivity from size m^j at every prime.
  strict-rule-pairs-pass-to-product-alphabets: that moves strictness from k symbols to multiples kl with the tables fixed; this moves strictness from a coset shift at size m to the full shift at size m^j through a nonlinear conjugacy.
artifacts:
  - research/artifacts/coset-shift-alphabet-lift-splitting-2026-09-12.md
---

**OPEN.** A candidate proof is in the artifact, Section 1. Verification requested from w4-vf-positive-b.

Let `G` be a group, `H` a finite subgroup and `m >= 2`. Put
`j = 1 + max ceil(v_q(|H|) / v_q(m))` over the primes `q | gcd(m, |H|)`, with `j = 1` when `m` and `|H|`
are coprime. Let `|A| = m` and `|A'| = m^j`.
- **Splitting.** There are a right `H`-set `W` and the twisted coset shift
  `Z = {w in W^G : w(kh) = w(k).h}` with a topological `G`-conjugacy `A^(G/H) x Z ≅ A'^G`.
- **Transfer.** Every continuous equivariant self-map `tau` of `A^(G/H)` gives the automaton
  `Theta (tau x id) Theta^-1` on `A'^G`.
  - Its memory is `FH ∪ H`.
  - It is injective iff `tau` is, and surjective iff `tau` is.
- **Consequences.**
  - A group surjunctive at size `m^j` satisfies `finite-stabilizer-coset-shifts-inherit-surjunctivity`
    at `(H, m)`.
  - A group surjunctive at every size has every finite-stabilizer coset shift surjunctive at every size.
  - For `H = Z/p` and `m = p`, `j = 2`.

**Why.**
- `Map(H, A')` splits `H`-equivariantly as `A x W` iff `m` divides the number of `H`-orbits of each
  type. That number is `e_S(x) / [N_H(S) : S]`, with `e_S(x) = sum_(T >= S) mu(S,T) x^[H:T]`.
- At `x = m^j` every term of `e_S` is a multiple of `m^j`. For each prime `q | m` this covers
  `v_q(m) + v_q([N_H(S) : S])`, since `v_q(|H|) <= (j-1) v_q(m)`.
- Colouring the orbits of each type into `m` equal classes gives the invariant coordinate onto `A`.

## Attempts

- **Same alphabet size.**
  - At `|A'| = m` the orbit counts would have to be divisible by `m`.
  - At `H = Z/p`, `m = p` the free orbits number `p^(p-1) - 1`, so the blockwise splitting fails
    (mark congruence, artifact Proposition B).
  - If `H` is normal of order `p` and some finite-index normal subgroup avoids `H`, no subshift `Z` gives
    `A^(G/H) x Z ≅ A^G` at size `p` (Proposition C, by periodic points).
  - So the fixed-size claim needs a `tau`-dependent construction or alphabet descent from `m^j` to `m`.
- **`m = 6`, `H = S_3`.** `j = 2`, and the orbit counts at size 36 are `36, 630, 46620, 362773530`, all
  multiples of 6 (artifact Section 4).

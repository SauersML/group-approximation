---
rg: 2
id: rcwa-groups-satisfy-boone-higman
kind: claim
title: Every finitely generated group of residue-class-wise affine permutations of Z embeds in a finitely presented simple group; for each finite prime set P the whole group RCWA_P(Z) embeds in one F_infinity simple odometer host
distinct_from:
  ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers: that identifies the class-transposition group CT(Z) with the RCWA permutations fixing N_0 setwise, a subgroup that already sits in the finitely presented simple groups CT_P(Z); this embeds all of RCWA(Z), including orientation-reversing pieces and pieces with nonzero shift, which lie in no CT_P(Z).
  odometer-2v-is-fp-simple-and-contains-bs12: that builds the host 2V_tau (the case P = ∅ here) to hold BS(1,2) and Q; this generalizes the host to every finite prime set and uses it for a whole class of groups, not one group.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that is Boone-Higman for two named families via their own hosts; this is Boone-Higman for the class of finitely generated RCWA groups.
---

**ESTABLISHED** by `rcwa-groups-bh-via-sign-doubling-and-odometer-host-proof`. Lane proof,
reviewed by gq-referee-a (proof-gap lens): PASS with three nits, all applied
(`research/artifacts/gq-referee-a-rcwa-groups-satisfy-boone-higman.md`). No citation-lens review yet.
- **Case `P = ∅`.** It needs only the refereed node `odometer-2v-is-fp-simple-and-contains-bs12`
  (both referees PASS).
- **General `P`.** It uses the same two theorems that node uses, Li arXiv:2110.04505v2
  Example ex:ZS (III) and Matui arXiv:1210.5800v3 Theorem simple2. Their hypotheses are
  checked for the higher-rank host in the route.

No priority is claimed. A bounded search found no prior Boone–Higman statement for RCWA
groups: two arXiv API queries on 2026-09-18 ("residue-class-wise", "RCWA", with math.GR
filtering), and grep of main. MathSciNet was not searched.

## Definitions

- **RCWA permutations.** A permutation `g` of `Z` is *residue-class-wise affine* (RCWA, Kohl)
  if for some `m ≥ 1` it is affine on every residue class mod `m`, `n ↦ (a n + b)/c`.
  `RCWA(Z)` is the group of all of them.
- **Prime data.** For a finite set `P` of odd primes, put `P' = P ∪ {2}`. `RCWA_P(Z)` is the
  subgroup of those `g` for which `m` and all `a`, `c` can be taken `P'`-smooth. Every `g` has
  finitely many data, so `RCWA(Z) = ⋃_P RCWA_P(Z)`, a directed union over finite `P`.
  `RCWA_P(Z)` is a subgroup (referee N1): a composite `gh` is affine on the classes of a
  modulus dividing `m_h m_g c`, and the inverse of a piece `r(m) → s(am/c)` has modulus
  `am/c`, so all data stay `P'`-smooth.
- **Hosts.** `H_P` is the topological full group of the groupoid of the self-similar action of
  `Z` by translation (the mixed-radix odometer) on the one-vertex `(|P'|+1)`-graph
  `Λ_P × F_2^+`, acting on `Ẑ_P × C`.
  - Here `Λ_P` is the class-transposition `k`-graph of `ct-p-z-is-a-one-vertex-k-graph-full-group`,
    with infinite paths `Ẑ_P = ∏_{p ∈ P'} Z_p`.
  - `C = {0,1}^N`, and the extra binary colour is fixed by the action.
  - Concretely, `H_P` is the group of homeomorphisms `f` of `Ẑ_P × C` such that, on the pieces
    `B(r_i, m_i) × C(w_i)` of a finite partition, `f(r_i + m_i z, w_i y) = (s_i + n_i(z + c_i), w'_i y)`
    with `c_i ∈ Z`. Here `B(r, m) = r + mẐ_P`, `m_i`, `n_i` are `P'`-smooth, and `w_i`, `w'_i`
    are binary words.
  - For `P = ∅`, `H_∅` is `2V_τ`.

## Statement

1. **The host.** For every finite set `P` of odd primes, `H_P` is of type `F_∞` and simple.
2. **The embedding.** There is an injective homomorphism `RCWA_P(Z) → H_P`.
3. **Consequence.** Every finitely generated subgroup of `RCWA(Z)` embeds in a finitely
   presented simple group. It lies in some `RCWA_P(Z)`, hence in `H_P`.

The embedding is the composite of two maps.
- **Sign doubling.** An injective homomorphism `RCWA(Z) → RCWA(Z)` whose image has only
  increasing affine pieces. Let `g` act on `Z × Z/2` by `(n, i) ↦ (g(n), i + ε_g(n))`, where
  `ε_g(n) = 1` iff `g` is decreasing on the piece containing `n`. Then pull back along
  `(n, 0) ↦ 2n`, `(n, 1) ↦ −2n − 1`.
- **Extension.** Extend to `Ẑ_P`, where a class-wise increasing piece
  `r + tm ↦ s + (t + c)n` becomes a canonical box map followed by a translation of the tail.
  Then take the product with `id_C`.

## Scope and remarks

- **Relation to CT_P.** `CT_P(Z) ≤ RCWA_P(Z)`, and inside `H_P` it is the image `h ↦ ĥ × id_C`
  of the class transpositions, where `ĥ` is `h` extended to `Ẑ_P` (no doubling is needed there).
- **What the host adds.**
  - Pieces with nonzero shift `c`, the "flux" across `0` that `CT_P(Z)` forbids, need the
    odometer.
  - Decreasing pieces need the sign doubling.
- **Other rings.** Kohl's other rings (number rings of class number one, `F_q[t]`, `Z_(π)`) are
  treated in `rcwa-groups-over-pids-satisfy-boone-higman`.
- **PBH.** `H_P` is highly transitive, so these groups satisfy the permutational conjecture:
  `rcwa-groups-satisfy-permutational-boone-higman`.

## Lesson for general BH

The finiteness of a host can be paid for by a small unit group. Here the only infinite
group the finiteness theorem sees is the odometer's `Z`. The "flux" that keeps
translations out of `CT_P(Z)` becomes one self-similar generator, and Li's theorem transfers
`F_∞` from `Z` to the whole full group. The general form of this principle, and what it
reduces BH to, is recorded in `pbh-via-degree-monoid-boundary-full-groups`.

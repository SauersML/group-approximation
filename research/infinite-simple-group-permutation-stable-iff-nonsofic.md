---
rg: 2
id: infinite-simple-group-permutation-stable-iff-nonsofic
kind: claim
title: An infinite simple group is permutation stable, strictly or flexibly, exactly when it is not sofic
distinct_from:
  binary-leavitt-unit-group-is-permutation-stable: that proves stability for one nonsofic group through its full character simplex; this is the equivalence for every infinite simple group, using only simplicity.
  almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial: that gives structural freeness of almost actions under IRS rigidity; this needs no IRS input and concludes that stability and nonsoficity coincide.
  sofic-stable-implies-residually-finite: that is the general principle that a sofic stable group is residually finite; this is the case of simple groups, where nonsoficity alone forces stability.
artifacts:
  - research/artifacts/un-stability-nonsofic-2026-09-13-part1.md
---

**ESTABLISHED.** Let `S` be a countably infinite simple group. An *almost homomorphism* is a
sequence `phi_n : S -> Sym(k_n)` with `d_H(phi_n(gh), phi_n(g) phi_n(h)) -> 0` for all `g, h`,
where `d_H` is normalized Hamming distance. The following are equivalent:

1. `S` is not sofic.
2. Every almost homomorphism satisfies `d_H(phi_n(g), 1) -> 0` for every `g ∈ S`.
3. `S` is strictly permutation stable: every almost homomorphism is pointwise `d_H`-asymptotic to
   genuine homomorphisms `rho_n : S -> Sym(k_n)`.
4. `S` is flexibly permutation stable: every almost homomorphism is pointwise asymptotic, on
   `[k_n]`, to restrictions of genuine homomorphisms `rho_n : S -> Sym(k'_n)` with `k'_n >= k_n`
   and `k'_n / k_n -> 1`.

The correcting homomorphisms in 3 and 4 are always trivial. Proof: `infinite-simple-group-permutation-stable-iff-nonsofic-proof`.

**Consequences.**
- **Dichotomy.** Every infinite simple group is sofic or permutation stable, never both. The
  answer does not depend on the variant of stability.
- **Firewall for the UN swarm.** "Prove `S = EL_N(A_k(𝒢))/Z` is permutation stable, then conclude
  nonsoficity from `sofic-stable-implies-residually-finite`" is a restatement of nonsoficity, not a
  route to it. A stability route must use a non-simple input, such as a stable Kazhdan subgroup.

**Calibration.**
- The Pestov 9.1 group `S = EL_3(LC(X,F_2) ⋊ Z)/Z` is LEF, hence sofic. By the theorem it is
  permutation unstable in every sense: its LEF approximations are far from the only genuine
  actions, which are trivial.
- `H = L_(F_2)(1,2)^x` is simple and nonsofic (`openai-leavitt-unit-nonsofic`). The theorem recovers
  `binary-leavitt-unit-group-is-permutation-stable` with no character input.

**Scope caveat.** Stability here is defined through almost homomorphisms of the group, as in
Bradford's senses used by `binary-leavitt-unit-group-is-permutation-stable`. For a finitely
presented `S`, the Arzhantseva–Păunescu definition via almost solutions of the relators is the
standard alternative. Its equivalence with the version here is recalled, not imported.

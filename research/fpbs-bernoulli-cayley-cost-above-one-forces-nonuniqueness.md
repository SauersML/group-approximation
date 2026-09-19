---
rg: 2
id: fpbs-bernoulli-cayley-cost-above-one-forces-nonuniqueness
kind: claim
title: If the Bernoulli Cayley subgraphing cost exceeds one at a single generating set, then p_c < p_u on every Cayley graph, so any failure of the Morse-deficit hole proves Benjamini-Schramm for that group
distinct_from:
  fpbs-non-fixed-price-one-has-nonuniqueness: that is Lyons' theorem with hypothesis C(b) = cost* > 1; here the hypothesis is C_sub^b(S) > 1 at one S, which is weaker because C_sub^b(S) >= C(b), and strictly weaker exactly when (Q3)(S) of fpbs-cost-is-limit-of-cayley-subgraphing-costs fails
  fpbs-sparse-spine-cost-bound: that bounds the group cost C* by an FIID spine at the same generating set; here the spine is first transported to every generating set, and the output is fixed-S Cayley subgraphing cost, the Morse-deficit hole at S and the Beringer-Pete-Timar question at S
  fpbs-hole-at-s-is-s-price-plus-invariant-cayley-cost: that splits the hole at S into (P1) and (P2) unconditionally; this proves (P1), (P2) and the hole at every S for every group with FIID sparse spines, and (P2) for every Cayley graph carrying invariant sparse spines
  fpbs-fiid-soft-collapse-iff-fiid-sparse-spines: that reads an FIID spine off the critical cluster and gives Corollary D (no FIID spines implies p_c < p_u); this re-proves the two parts it needs inline and converts spines into Cayley subgraphing cost, which links the Benjamini-Schramm lane to the Morse-deficit lane
  fpbs-invariant-cayley-cost-literature-status: that records c_inv(S) = 1 only for amenable and Kazhdan groups; this adds every Cayley graph with invariant sparse spines
---

**ESTABLISHED (agent-verified, not refereed).** Proof in
`fpbs-bernoulli-cayley-cost-above-one-forces-nonuniqueness-proof`.

**Notation.**
- `Gamma` is an infinite finitely generated group, and `S` is a finite symmetric generating set.
- `C_sub^b(S)` is the Bernoulli Cayley subgraphing cost of `fpbs-cost-is-limit-of-cayley-subgraphing-costs`.
- `c_inv(S)` is the invariant Cayley cost, and `beta_1` is `beta_1^(2)(Gamma)`.
- An *FIID* (respectively *invariant*) *sparse spine* on `Cay(Gamma,S)` is, for every `eps > 0`, an FIID (respectively
  `Gamma`-invariant) random subgraph that is a.s. connected and infinite, with `P(o in V) <= eps`.

**Theorem.**
1. **(Spines give Cayley cost one.)**
   - If `Cay(Gamma,S)` has FIID sparse spines, then `C_sub^b(S) = 1` and `beta_1 = 0`.
   - Hence the Morse-deficit hole `fpbs-morse-deficit-vanishes-for-full-presentations` holds at `S`, and both `S`-fixed
     price (P1) and (P2) of `fpbs-hole-at-s-is-s-price-plus-invariant-cayley-cost` hold at `S`.
   - If `Cay(Gamma,S)` has invariant sparse spines, then `c_inv(S) = 1 = cost(Gamma)`. That is a positive answer to the
     Beringer–Pete–Timár question at `S`.
2. **(Transport.)** FIID, respectively invariant, sparse spines on one Cayley graph of `Gamma` give the same kind of
   spines on every Cayley graph of `Gamma`.
3. **(Lyons at a fixed generating set.)** Let `Gamma` be nonamenable. If `p_c = p_u` on one Cayley graph of `Gamma`,
   then `C_sub^b(S) = 1` at every finite generating set `S`. Equivalently, if `C_sub^b(S) > 1` for a single `S`, then
   `p_c < p_u` on every Cayley graph of `Gamma`.
4. **(Cross-lane reduction.)** Let `Gamma` be nonamenable. If the Morse-deficit hole fails at a single `(Gamma, S)`,
   then `p_c < p_u` on every Cayley graph of `Gamma`.
   - The same conclusion holds if (P1) or (P2) fails at a single `S`.

**Profile of a Benjamini–Schramm counterexample.** Suppose `p_c = p_u` on some Cayley graph of a nonamenable `Gamma`.
Then at every `S` the following hold at once: `beta_1 = 0`, `C_sub^b(S) = C(b) = c_inv(S) = cost(Gamma) = 1`, the
Morse-deficit hole, and `S`-fixed price. So such a `Gamma` would be a positive instance of every one of these open
fixed-`S` statements. A group that refutes any of them at any `S` satisfies the flagship on all its Cayley graphs.

**Members (Theorem 1 applied to established spine nodes).**
- **Morse-deficit hole, (P1) and (P2) at every `S`.** These hold for every group with FIID sparse spines:
  - class `Z` of `fpbs-central-z2-groups-have-fiid-sparse-spines`, including the Kazhdan lattices in the universal cover
    of `Sp_2n(R)`;
  - by Corollary 3 of `fpbs-fiid-spines-lift-via-infinite-conjugate-intersection`: `Gamma_1 x Gamma_2` with elements of
    infinite order in both factors, `SL_n(Z)` for `n >= 3`, and extensions of FIID-spine normal subgroups.

  `SL_n(Z)` and the `Sp_2n` lattices are infinite Kazhdan groups. That is the instance class the Morse node lists as
  open, and here the hole is settled at every `S`.
- **Beringer–Pete–Timár positive, `c_inv(S) = cost = 1` at every `S`.** This holds for every group with invariant
  sparse spines. Those are:
  - groups with a surjection onto `Z` that has finitely generated kernel (Theorem B of
    `fpbs-soft-collapse-iff-invariant-sparse-spines`);
  - groups with a (C)-subgroup, including nonamenable Baumslag–Solitar groups and `SL_2(Z[1/p])`
    (`fpbs-soft-collapse-over-conjugate-intersection-subgroups`);
  - groups with a commensurated subgroup as in `fpbs-commensurated-subgroup-sparse-spines`;
  - wreath products and split extensions as in `fpbs-soft-collapse-on-wreath-and-split-extensions`.

**Calibration.**
- For `F_2`, `C_sub^b(S) >= C(b) = 2 > 1` at every `S`. Theorem 3 then gives `p_c < p_u`, which agrees with Lyons.
  The FIID spine hypothesis correctly fails.
- For groups with `beta_1 > 0`, Theorem 4 is Lyons' theorem again. The new content is the `beta_1 = 0` case, where a
  failure of the hole means `C_sub^b(S) > 1 = 1 + beta_1`.

**Not claimed.**
- No group is known with `C(b) = 1 < C_sub^b(S)`. So this does not yet prove the flagship for any new group.
- It moves the flagship's hard instances into the set where every fixed-`S` Cayley cost statement already holds. Any
  future counterexample to the Morse-deficit hole, to `S`-fixed price, or to the Beringer–Pete–Timár question
  automatically settles Benjamini–Schramm for its group.

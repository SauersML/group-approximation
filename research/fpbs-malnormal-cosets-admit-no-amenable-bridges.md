---
rg: 2
id: fpbs-malnormal-cosets-admit-no-amenable-bridges
kind: claim
title: An amenable subrelation of a free-group orbit relation meets at most one coset of a malnormal finitely generated subgroup in infinite pieces, so zero-cost amenable bridges over malnormal pairs do not exist
distinct_from:
  fpbs-malnormal-measured-absorption-cap: that caps chains of single partial isomorphisms having infinite contact with a subrelation of E_K; this concerns an arbitrary amenable subrelation E, none of whose partial isomorphisms need have infinite contact with E ∩ E_K, and it is proved by invariant boundary measures, not by coset counting.
  fpbs-malnormal-subgroup-relations-finite-contacts: that counts graphing edges between two subgroup classes; this is about amenable subrelations and their intersections with E_K.
  fpbs-hyperbolic-no-q-normal-hyperfinite-chain: that asks whether q-normalizer chains from a hyperfinite subrelation can exhaust the orbit relation of a hyperbolic group; this fixes a malnormal subgroup and shows every amenable subrelation with aperiodic trace on E_K stays inside E_K.
  fpbs-infinite-contact-zero-relative-cost: that is the positive zero-cost mechanism for infinite contact through subgroups; this shows its natural amenable-subrelation extension is empty for malnormal K.
---

**ESTABLISHED** through `fpbs-malnormal-cosets-admit-no-amenable-bridges-proof`.

Let `L` be a finitely generated free group, `K ≤ L` a finitely generated
malnormal subgroup (`K ∩ gKg^{-1} = 1` for `g ∉ K`), and `a` a free p.m.p.
action of `L` on `(X, μ)`. Write `R_L = E_a` and `R_K = E_{a|K}`. Let
`E ⊆ R_L` be an amenable Borel subrelation, and let
`Y = { x : [x]_{E ∩ R_K} is infinite }`.

1. **One coset per class.** For almost every `x`, the points of `[x]_E ∩ Y`
   lie in a single `R_K`-class. Equivalently `E|_Y ⊆ R_K`.
2. **Absorption.** If `E ∩ R_K` is aperiodic on an `E`-invariant set `Z`,
   then `E|_Z ⊆ R_K`. In particular every amenable subrelation of `R_L` that
   contains an aperiodic subrelation of `R_K` (for example `R_{<k>}` for any
   `1 ≠ k ∈ K`) is contained in `R_K`.
3. **No zero-cost amenable bridge.** If `K ≠ L`, there is no amenable
   `E ⊆ R_L` with `E ∩ R_K` aperiodic and `R_K ∨ E = R_L`. Indeed
   `E ⊆ R_K`, so `R_K ∨ E = R_K ≠ R_L` by freeness. So the reduction
   `relC(R_L ; R_K) ≤ relC(E ; E ∩ R_K)`, used with an amenable `E` whose
   trace on `R_K` is aperiodic, never applies.
4. **Non-malnormal version.** For arbitrary finitely generated `K`, if
   `x ~_E y` with `x, y ∈ Y` and `y = γx`, then `K ∩ γ^{-1}Kγ` is infinite.

**Scope.** This is an obstruction to one mechanism for the open case
(`K` malnormal, `relC = 0`) of `fpbs-relative-fixed-price-free-pairs`, for
every free action, Bernoulli included. It does not exclude approximate
bridges: amenable `E` whose trace on `R_K` has large finite classes, with
`relC(E ; E ∩ R_K)` small but positive. Nor does it bound `relC` from below.
It is the relational analogue of the group fact that an amenable subgroup of
`L` meeting `K` in an infinite set lies in `K`.

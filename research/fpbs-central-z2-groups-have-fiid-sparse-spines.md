---
rg: 2
id: fpbs-central-z2-groups-have-fiid-sparse-spines
kind: claim
title: Groups with a central Z inside a Z2 have arbitrarily sparse FIID connected spines on every Cayley graph, including the Kazhdan lattices in the universal cover of Sp_2n(R)
distinct_from:
  fpbs-finite-energy-fkg-collapse-over-central-z2-slabs: that selects whole slabs and is not a factor of iid; here every piece is a finite Bernoulli-thinned cross and the spine is FIID
  fpbs-soft-collapse-iff-invariant-sparse-spines: its Theorem B needs a surjection onto Z with finitely generated kernel, which no infinite Kazhdan group has; this needs a central Z inside a Z2 and gives FIID spines
  fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups: that is OPEN and its Kazhdan spines are invariant but not factors of iid; here the spines are FIID, on the central-Z-in-Z2 class
  fpbs-kazhdan-sparse-spines: that asks for FIID spines on all infinite Kazhdan groups; this settles the subclass of Kazhdan groups with a central Z inside a Z2
---

**ESTABLISHED (new class).** Proof in
`fpbs-central-z2-groups-have-fiid-sparse-spines-proof`.

**Class `Z`.** `Gamma` is finitely generated and has a central element `t` of
infinite order and an element `g` of infinite order with `<g> ∩ <t> = 1`.

**Theorem.** Let `Gamma ∈ Z`, `S` a finite symmetric generating set and
`G = Cay(Gamma,S)`. For every `eps > 0` there is a factor of iid random subgraph
`Lam` of `G` that is a.s. connected and infinite, with `P(o ∈ V(Lam)) <= eps`.

**Examples.** `Gamma~_n = p^-1(Sp_2n(Z)) ⊂ Sp_2n(R)~` for `n >= 2` has property
(T) (`deligne-universal-cover-lattice-is-non-rf-kazhdan`) and lies in `Z`: take
`t` a generator of the central `pi_1(Sp_2n(R)) ≅ Z` and `g` a lift of an
infinite-order element. So `fpbs-kazhdan-sparse-spines` holds for these
Kazhdan groups. Having property (T), they have no surjection onto `Z`, so
Theorem B of `fpbs-soft-collapse-iff-invariant-sparse-spines` does not apply to
them. Braid groups `B_n` (`n >= 3`) and `Lambda x Z` are further members.

**Construction in one paragraph.**

1. Declare each `u ∈ Gamma` occupied with probability `delta ≈ 3/(L/2)^2`.
2. An occupied `u` opens a cross, a path following `g^-L ... g^L` and one
   following `t^-L ... t^L` through `u`.
3. Inside a coset `uH` (`H = <g,t> ≅ Z^2`), two crosses whose centres are
   `H`-close meet. Box renormalization gives supercritical site percolation, and
   Burton–Keane gives a unique infinite chain of crosses `L_c`.
4. Neighbouring cosets `c` and `vsH` are joined by rare connectors with
   probability `eta/(r+1)`.
5. Centrality makes this work. `v t^k s = v s t^k`, so the whole central line
   `v<t> ⊂ c` points at the same neighbouring coset. The candidate link sites
   along that line form a `<t>`-invariant set, which is infinite when
   nonempty, so some connector succeeds a.s.

The density is `O(1/L) + O(eta)`.

**Consequence and calibration.** By `fpbs-sparse-spine-cost-bound` this
reproduces fixed price one for `Z`. That was already known from Gaboriau's
infinite-amenable-normal-subgroup theorem, so the new content is the FIID
spine. The FIID spine feeds the FIID collapse family of
`fpbs-kazhdan-spectral-data-realized-by-fiid-collapse`. `F_2` has fixed price
two and no central `Z`, and is correctly not covered.

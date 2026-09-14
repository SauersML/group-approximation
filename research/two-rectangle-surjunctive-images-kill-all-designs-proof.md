---
rg: 2
id: two-rectangle-surjunctive-images-kill-all-designs-proof
kind: route
title: Realize the design through the separating image, where surjunctivity makes the reverse table sufficient, and pull that table back unchanged
target: two-rectangle-surjunctive-images-kill-all-designs
requires: []
artifacts:
  - research/artifacts/canonical-table-groups-for-automaton-designs-2026-09-12.md
---

Notation follows Section 1 of
`research/artifacts/canonical-table-groups-for-automaton-designs-2026-09-12.md`.
A design `D` is a finite alphabet with rules `nu` on `S` and `mu` on `M`. A
realization `rho` sends addresses to elements of a group, identity addresses to `1`.

- Its **forward table** `E_rho` is the partition of `S x M` by `rho(s) rho(m)`, with
  the class of products equal to `1` marked.
- Its **reverse table** `F_rho` is the partition of `M x S` by `rho(m) rho(s)`, marked
  the same way.

The artifact shows:
- **Lemma 1:** `sigma tau = id` iff `E_rho` lies in the up-set `𝓕_D`, and
  `tau sigma = id` iff `F_rho` lies in `𝓡_D`.
- **Lemma 2:** both sets are closed under coarsening.
- **Lemma 3:** when `E_rho` is in `𝓕_D`, `tau_rho` is surjective iff `F_rho` is in `𝓡_D`.

Let `rho_G` be the given realization in `G`, with `sigma tau = id`, so `E_(rho_G)`
is in `𝓕_D`.

1. **The realization through `psi`.** Put `rho_K(a) = psi(x_(rho_G(a)))`. Identity
   addresses go to `psi(x_1) = 1`. Let `tau_K`, `sigma_K` be the automata over `K`
   with the same rules.
2. **The forward table only coarsens.** If `s m = s' m'` in `G`, the relator
   `x_s x_m = x_s' x_m'` gives `rho_K(s) rho_K(m) = rho_K(s') rho_K(m')`. If `s m = 1`,
   then `(s, m)` and `(1, 1)` are equal products, and the relator reads
   `x_s x_m = x_1 x_1 = 1`. So `E_(rho_K) >= E_(rho_G)`. By Lemma 2 it lies in `𝓕_D`,
   and by Lemma 1 `sigma_K tau_K = id`.
3. **Surjunctivity of `K`.** `tau_K` has a left inverse, so it is injective. `K` is
   surjunctive, so `tau_K` is surjective. By Lemma 3, `F_(rho_K)` lies in `𝓡_D`.
4. **The reverse table is unchanged.**
   - The relators `x_m x_s = x_m' x_s'` for `m s = m' s'` in `G`, including the
     products equal to `1` as in step 2, give `F_(rho_K) >= F_(rho_G)`.
   - The separation hypothesis gives the opposite inequality. If
     `psi(x_m x_s) = psi(x_m' x_s')`, then `m s = m' s'` in `G`. If
     `psi(x_m x_s) = 1 = psi(x_1 x_1)`, then `m s = 1`.
   So `F_(rho_K) = F_(rho_G)` as marked partitions.
5. **Conclusion.** `F_(rho_G)` lies in `𝓡_D`. By Lemma 3 over `G`, `tau` is surjective.
   This holds for every alphabet and every pair of rules, so no design on `(S, M)` is
   strict over `G`. QED

**Corollaries.**
1. **Sofic images combine.** A finite direct product of sofic groups is sofic, and a
   product homomorphism separates a pair exactly when some factor does. Take the
   contrapositive over the finitely many reverse pairs.
2. **Localization.** When `<S u M>` is sofic, apply the theorem to `x_a -> a` into
   that subgroup. It satisfies the relators, and separation is equality in `G`.
3. **Freeness.** A free group is residually finite. The `G`-distinct reverse products
   are distinct in `T`, since `T -> G` distinguishes them. Take one finite quotient per
   pair and combine as in Corollary 1.

**Where each hypothesis is used.**
- **Reverse relators and separation (step 4).** Lemma 2 moves membership in `𝓡_D`
  only to coarser tables. The conclusion needs `F_(rho_G)` itself, so the two tables
  must coincide, not just coarsen.
  - Without the reverse relators, `psi` need not be coarser on `M x S`.
  - Without separation, it may be strictly coarser. Reverse sufficiency of a coarser
    table says nothing about the finer one.
- **Surjunctivity of `K` (step 3).** No group model can make the conclusion fail
  without refuting Gottschalk's conjecture, so the test is on the hypothesis. Over the
  free group on the letters, the forward table of a design has the free reverse table.
  That table is reverse sufficient only for bijective designs
  (`free-memory-injectivity-forces-universal-bijectivity`), which agrees with free
  groups being sofic.

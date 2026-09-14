---
rg: 2
id: ec-groups-share-nonsurjunctive-alphabet-sizes-proof
kind: route
title: Carry strict data at a fixed alphabet into an existentially closed group through its finite table
target: ec-groups-share-the-nonsurjunctive-alphabet-sizes
requires:
  - surjunctivity-passes-to-subgroups
  - strict-rule-pairs-pass-to-product-alphabets
  - surjunctivity-is-axiomatized-by-rectangle-clauses
  - existentially-closed-groups-contain-every-finite-table
  - countable-groups-embed-in-countable-existentially-closed-groups
artifacts:
  - research/artifacts/gk3-alphabet-descent-2026-09-14.md
---

Complete proof from the prerequisites. Notation as in the target.

1. **Subgroups.** The proof of `surjunctivity-passes-to-subgroups` induces from an automaton `tau` over `H`
   an automaton `tau^G` over `G`. It keeps the alphabet, the memory and the rule. `tau^G` is injective when
   `tau` is, and on each coset it is a copy of `tau`, so it is not surjective when `tau` is not. Hence
   `NS(H) ⊆ NS(G)`.
2. **Multiples.** This is the group consequence of `strict-rule-pairs-pass-to-product-alphabets`: a group
   that is not `A`-surjunctive is not `(A x B)`-surjunctive.
3. **Existentially closed groups.** Let `n ∈ NS(G)`, witnessed over `A` with `|A| = n`, and let `K` be
   existentially closed.
   - Theorem 1 of `surjunctivity-is-axiomatized-by-rectangle-clauses` works at the fixed alphabet `A`. It
     gives strict data `D` over `A` and elements `x_a` of `G` (`a ∈ S ⊔ M`, both labels `1` sent to `1`).
     Their forward products `x_s x_m` coincide along at least `T_f`, and their reverse products `x_m x_s`
     coincide along at most `T_r`.
   - Let `F = {1} ∪ {x_a}`. By `existentially-closed-groups-contain-every-finite-table` there is an
     injective map `psi : F ∪ F.F -> K` with `psi(xy) = psi(x) psi(y)` for `x, y ∈ F`, and `psi(1) = 1`.
   - Put `y_a = psi(x_a)`. Then `y_s y_m = psi(x_s x_m)` and `y_m y_s = psi(x_m x_s)`. Since `psi` is
     injective on `F.F`, two such products coincide in `K` exactly when they coincide in `G`.
   - So `D` is realized in `K`, and the same theorem gives a strict automaton over `A` on `K`. Hence
     `NS_all ⊆ NS(K)`, and `NS(K) ⊆ NS_all` by definition.
4. **Consequences.**
   - Empty or closed under multiples: step 2.
   - (a) implies (c). If `NS(K) != ∅` then `NS_all != ∅`, so `2 ∈ NS_all = NS(K)`.
   - (c) implies (b). Existentially closed groups exist, by
     `countable-groups-embed-in-countable-existentially-closed-groups`.
   - (b) implies (a). If `NS_all != ∅`, then `NS(K) = NS_all != ∅`, so `2 ∈ NS(K) ⊆ NS_all`.
   - Even sizes: step 2 applied to `2`.

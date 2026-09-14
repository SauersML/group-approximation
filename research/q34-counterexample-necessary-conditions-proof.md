---
rg: 2
id: q34-counterexample-necessary-conditions-proof
kind: route
title: Each listed property would supply a finitely presented simple MIF overgroup
target: q34-counterexample-necessary-conditions
requires:
  - fp-simple-highly-transitive-groups-satisfy-pbh
  - simple-envelope-forces-solvable-word-problem
  - fp-simple-type-a-actions-iff-finite-bi-index-subgroups
  - centerless-fp-finitely-many-conjugacy-classes-gives-pbh
  - rybak-general-type-limit-set-topologically-free-iff-mif
  - pbh-passes-to-relative-free-group-automorphisms
---

Let `S` be a nontrivial finitely presented simple group. It has solvable word
problem by `simple-envelope-forces-solvable-word-problem`, so BFFHZ Theorem C
(`fp-simple-highly-transitive-groups-satisfy-pbh`) applies to `S`. Each item is
proved by contraposition: if the property fails, `S` embeds in a finitely
presented simple MIF group.

1. **Finite `S`.** If `S` is finite, its regular action on itself is of type (A):
   - faithful;
   - `S` finitely presented;
   - trivial stabilizers;
   - finitely many subsets of a finite set.

   Theorem C (i) ⟹ (iv) applies.
2. **MIF or highly transitive `S`.** If `S` is MIF, `S` is itself a finitely
   presented simple MIF overgroup of `S`. If `S` is highly transitive, then
   Theorem C (iii) holds with `S` as its own envelope, so (iv) holds.
3. **A type (A) action.** If `S` has one, Theorem C (i) ⟹ (iv) applies. The
   reformulation through double cosets is
   `fp-simple-type-a-actions-iff-finite-bi-index-subgroups`.
4. **Finitely many conjugacy classes.** By item 1, `S` is infinite; being simple,
   it is nonabelian, so `Z(S)` is a proper normal subgroup and hence trivial. If
   `S` had finitely many conjugacy classes, then
   `centerless-fp-finitely-many-conjugacy-classes-gives-pbh` would embed it in a
   finitely presented simple MIF group.
5. **A lim-free hyperbolic action.** By
   `rybak-general-type-limit-set-topologically-free-iff-mif`, (2) ⟹ (1), such an
   action makes `S` MIF, contradicting item 2.
6. **A type (A) envelope for `Aut_S(S * F_n)`.** By
   `pbh-passes-to-relative-free-group-automorphisms` (its corollary for finitely
   presented simple groups), for `n >= 2` such an embedding is equivalent to `S`
   embedding in a finitely presented simple MIF group. `∎`

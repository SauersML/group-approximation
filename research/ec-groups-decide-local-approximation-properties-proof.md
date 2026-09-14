---
rg: 2
id: ec-groups-decide-local-approximation-properties-proof
kind: route
title: Transport each finite table into the existentially closed group
target: local-approximation-properties-are-decided-by-ec-groups
requires:
  - local-approximation-properties-are-marked-closed
  - existentially-closed-groups-contain-every-finite-table
  - countable-groups-embed-in-countable-existentially-closed-groups
---

By definition in `local-approximation-properties-are-marked-closed`, tables are
taken up to isomorphism, and a model predicate passes to sub-tables:
`M(tab_G(F), eps)` implies `M(tab_G(F'), eps)` for `F' <= F`.

- **(a) ⇒ (c).**  Immediate.
- **(c) ⇒ (b).**  Existentially closed groups exist: apply
  `countable-groups-embed-in-countable-existentially-closed-groups` to the
  trivial group.
- **(b) ⇒ (a).**  Let `H` be existentially closed with `P_M(H)`.
  1. Take any group `G`, finite `F <= G` and `eps > 0`.  Put `F1 = F u {1}`.
  2. By `existentially-closed-groups-contain-every-finite-table` there is an
     injective `psi` that is an isomorphism `tab_G(F1) -> tab_H(psi(F1))`.
  3. `psi(F1)` is a finite subset of `H`, so `P_M(H)` gives
     `M(tab_H(psi(F1)), eps)`.  Hence `M(tab_G(F1), eps)`, because `M` only
     sees isomorphism classes.
  4. Passing to the sub-table of `F <= F1` gives `M(tab_G(F), eps)`.
  5. As `F` and `eps` were arbitrary, `P_M(G)` holds.

**Torsion-free version.**  Run the same argument with item 2 of
`existentially-closed-groups-contain-every-finite-table` and the torsion-free
case of the existence claim.

**Hyperlinear consequence.**  Take `M` = hyperlinear.  The contrapositive of
(b) ⇒ (a) says that one non-hyperlinear group makes every existentially closed
group non-hyperlinear.

**No existentially closed group is computable.**  Call a group computable if it
is isomorphic to a group on a decidable subset of `N` with computable
multiplication.
1. Suppose `H` is existentially closed and computable.  Let
   `G = <X | R>` be a finitely presented group with unsolvable word problem
   (Novikov, Boone).
2. For a word `w` in `X`, let `Sigma_w` be the system with unknowns
   `v_x (x in X)` and no constants:
   ```text
   r(v) = 1 for all r in R;    w(v) != 1.
   ```
3. **Claim: `w != 1` in `G` iff `Sigma_w` has a solution in `H`.**
   - If `v` solves it in `H`, then `x |-> v_x` defines a homomorphism
     `G -> H` sending `w` to a nontrivial element, so `w != 1` in `G`.
   - If `w != 1` in `G`, then `v_x = x` solves `Sigma_w` in `H * G`, which
     contains `H`.  So `Sigma_w` has a solution in `H`.
4. `H` is computable, so the set of `w` for which `Sigma_w` is solvable in `H`
   is computably enumerable: search over all tuples.  The set of `w` with
   `w = 1` in `G` is computably enumerable because `G` is finitely presented.
5. A set that is computably enumerable and has computably enumerable
   complement is decidable.  So `G` has solvable word problem, a
   contradiction.

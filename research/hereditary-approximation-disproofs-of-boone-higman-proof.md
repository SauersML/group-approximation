---
rg: 2
id: hereditary-approximation-disproofs-of-boone-higman-proof
kind: route
title: Test the separating property on the finitely presented simple witnesses, and pass a failing table into a host
target: hereditary-approximation-disproofs-of-boone-higman
requires:
  - fp-simple-nonsofic-group
  - fp-simple-full-mf-radical-group
  - mf-radical-functoriality
  - leavitt-unit-group-finitely-presented
  - binary-leavitt-unit-group-is-simple
  - openai-leavitt-unit-nonsofic
  - local-approximation-properties-are-marked-closed
  - fg-infinite-simple-groups-are-minimally-almost-periodic
  - infinite-simple-group-hs-stable-iff-nonhyperlinear
---

`P` is closed under isomorphism and subgroups. (S1) and (S2) are as in the
target. Write `fps` for the class of finitely presented simple groups.

## 1. Separation is exactly a disproof

Suppose `P` separates, and let `G` be the (S2) group. If `G` embedded in some
`K ∈ fps`, then `K ∈ P` by (S1), so `G ∈ P` by heredity. That contradicts (S2),
so `G` is a counterexample to `boone-higman-conjecture`.

Conversely, let `Q` be the class of groups isomorphic to a subgroup of a member
of `fps`. `Q` is closed under isomorphism and subgroups, and contains `fps`. If
the conjecture fails for `G`, then `G ∉ Q`, so `Q` separates. ∎

## 2. Class kill

- **Sofic case.** Suppose every member of `P` is sofic. `fp-simple-nonsofic-group`
  (ESTABLISHED) gives `K ∈ fps` that is not sofic, so `K ∉ P` and (S1) fails.
- **MF case.** Suppose every member of `P` is MF. `fp-simple-full-mf-radical-group`
  (ESTABLISHED) gives `K ∈ fps` with `Rad_MF(K) = K`. By the second formulation
  in `mf-radical-functoriality`, every homomorphism from `K` to an MF group is
  trivial. `K` is nontrivial, so the identity map is not trivial, and `K` is
  not MF. So `K ∉ P` and (S1) fails. ∎

## 3. Survivors contain L^x

Let `L = L_(F_2)(1,2)`. By `leavitt-unit-group-finitely-presented` and
`binary-leavitt-unit-group-is-simple`, `L^x ∈ fps`, so (S1) gives `L^x ∈ P`. By
`openai-leavitt-unit-nonsofic`, `L^x` is not sofic. ∎

## 4. Table-defined separators refute the local form

Let `P = P_M`, and suppose it separates with (S2) group `G = <y_1, ..., y_n>`,
which has solvable word problem. Clause 3 of
`local-approximation-properties-are-marked-closed` gives a radius `R`. Every
marked group whose words of length `<= R` satisfy the same equalities as in `G`
fails `P_M`. There are finitely many words `w` of length `<= R` in `y`. Let `E`
be the set of those with `w(y) = 1` in `G`, and `N` the set of the rest. The
system `E = 1, N ≠ 1` has the solution `y` in `G`.

If `local-boone-higman-conjecture` held, some `K ∈ fps` would contain a solution
`z`. The marked group `(<z>, z)` satisfies the same equalities as `G` on all
words of length `<= R`, so it fails `P_M`. By clause 1 (heredity), `K` fails
`P_M`, which contradicts (S1). So the finite system `(E, N)` refutes the local
conjecture. ∎

## 5. Hyperlinearity

`P = hyperlinear` is closed under isomorphism and subgroups (clause 1 of
`local-approximation-properties-are-marked-closed`, hyperlinear instance). So
it separates iff (S1) and (H2) hold, and it remains to show that (S1) is
equivalent to (H1).

- **Finite members of fps.** A finite group `S` is hyperlinear. Its left
  regular representation `S -> U(|S|)` is an exact homomorphism. Distinct
  elements go to distinct permutation matrices, and for `g ≠ 1` the matrix of
  `g` has no fixed basis vector, so `||λ(g) - 1||_2 = sqrt 2`. That is a
  hyperlinear model of every table with defect `0` and separation `sqrt 2`.
- **Infinite members of fps.** Let `S` be infinite, finitely presented and
  simple. It is finitely generated and countable. By
  `fg-infinite-simple-groups-are-minimally-almost-periodic`, `S` has no
  nontrivial finite-dimensional unitary representation. So
  `infinite-simple-group-hs-stable-iff-nonhyperlinear` applies to `S`: `S` is
  not hyperlinear iff it is strictly HS stable, and iff it is flexibly HS
  stable.

So (S1) holds iff no infinite member of `fps` is HS stable, which is (H1).

**Consequences.** (H1) applied to `L^x`, which is infinite by
`binary-leavitt-unit-group-is-simple` and lies in `fps` by §3, gives
`binary-leavitt-unit-group-hyperlinear`. Since `L^x` is nonsofic
(`openai-leavitt-unit-nonsofic`), it is then a hyperlinear nonsofic group, which
is `hyperlinear-nonsofic-group`. (H2)
is a nonhyperlinear group with solvable word problem. All three statements are
unresolved in this graph and in the literature it cites. ∎

## Scope

- Nothing here is evidence for or against Boone--Higman.
- The theorem does not say that the survivors (hyperlinearity, weak soficity,
  linear soficity) cannot separate. By §3, a separation through such a `P`
  makes the Leavitt unit group a nonsofic member of `P`. By (S2), it also
  produces a decidable group without `P`. For hyperlinearity these are Pestov
  Question 3.4 for `L^x` and a nonhyperlinear group, as in §5.
- Clause 4 uses only heredity and marked closedness, so it applies to every
  instance listed in `local-approximation-properties-are-marked-closed`.

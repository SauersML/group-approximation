---
rg: 2
id: bounded-depth-operator-groups-contain-every-fg-group
kind: claim
title: Every finitely generated group acts faithfully on the Cantor module by basis permutations of bounded depth shift, so depth-filtration invariants alone cannot exclude the Baumslag--Gersten group from Leavitt hosts
distinct_from:
  depth-distortion-obstructs-power-conjugates-in-leavitt-hosts: that proves necessary conditions on the depth profile of a Baumslag--Gersten generator in bounded-depth hosts; this shows the whole group of bounded-depth operators contains every finitely generated group, so those conditions are all a depth argument can give and DG must use the Leavitt algebra.
  leavitt-units-of-infinite-order-have-linear-depth-growth: that conjectures linear growth of algebraic depth for Leavitt units; this shows no such growth statement holds for the ambient operator group of bounded depth shift, in which distorted cyclic subgroups of every kind occur.
artifacts:
  - research/bounded-depth-operator-groups-contain-every-fg-group-proof.md
---

**ESTABLISHED** by `bounded-depth-operator-groups-contain-every-fg-group-proof`.
This is a sharpness result and a precise dead end for one class of obstructions. It does not settle the target.

## Setting

Notation is as in `depth-distortion-obstructs-power-conjugates-in-leavitt-hosts`:

- `K` is any field and `C_1 = C(X, K)` with `X = {1,2}^N`;
- `V_k` is the space of functions that depend only on the first `k` letters;
- `s(T)` is the depth shift, and `BDep_1(K)` is the group of invertible operators with `s(T), s(T^{-1}) < ∞`.

## Statement

1. **Universality.** Let `G` be a finitely generated group with finite symmetric generating set `S`. There is a
   faithful homomorphism `π : G → BDep_1(K)` such that
   - each `π(g)` permutes the nested basis `{1} ∪ {1_[w1] : w ∈ {1,2}^*}` of `C_1`;
   - `s(π(g)) ≤ ⌈(|g|_S + 1)·log₂(|S| + 1)⌉`.
   Every countable group embeds in a finitely generated one, so every countable group embeds in `BDep_1(K)`.
   The same holds in `BDep_d(K)` for every `d ≥ 1`.
2. **Consequence for the Baumslag--Gersten group.** `BG = <a,t | (tat^{-1}) a (tat^{-1})^{-1} = a^2>` embeds in
   `BDep_1(F_q)` for every `q`. For the image `A = π(a)`:
   - `E_A(n) ≤ C·(|a^n|_BG + 1)`, and in particular `E_A(N_i) ≤ C·2^i` along the tower;
   - by part 4 of `depth-distortion-obstructs-power-conjugates-in-leavitt-hosts`, `E_A(n) → ∞`.
   So a divergent but tower-irregular depth profile really occurs, and **DG fails for `BDep_1(F_q)`**.
3. **Dead class.** Any proof that `BG` does not embed in a Leavitt host `L_{F_q}(1,2)^{⊗d}` of the following kind
   cannot work:
   - it uses only the depth filtration `(V_k)` and the depth shifts `s(T^{±n})` of the image;
   - equivalently, it would apply to every subgroup of `BDep_d(F_q)`.
   It fails at the step "a divergent depth profile is regular", which is false in `BDep_1(F_q)` by part 2. The same
   holds for `H_3(Z)` and every `BS(1,k)`, whose distorted elements also get bounded-shift images there.

## What survives

DG for Leavitt units is still open. A proof must use structure that `BDep` lacks:

- the finite algebraic depth `ell` of a unit and its inverse (a unit is a finite combination of monomials, while
  `π(a)` above is not);
- the grading of `L(1,2)` and the nilpotence of extreme components
  (`leavitt-free-group-leading-term-forces-linear-depth`);
- Frobenius identities in characteristic `p`.

**Next falsifiable step.** Find the locality invariant that separates Leavitt units from the regular model. A
unit of algebraic depth `N` is *prefix-local*: for `|w| ≥ N` it maps `1_[w]` into the span of the indicators
`1_[p w']` with `w = q w'` and `|p|, |q| ≤ N`. The permutations `π(g)` above carry no such locality. The test is
whether prefix-locality of `A` and `A^{-1}`, together with the tower relation, forces a pointwise lower bound on
`E_A`, or whether a prefix-local unit with oscillating depth profile exists.

---
rg: 2
id: sofic-subgroups-carry-independent-cylinder-defects
kind: claim
title: Every sofic subgroup of the binary Leavitt unit group containing disjoint frames carries a free rank model with exactly multiplicative cylinder defects
distinct_from:
  sofic-subgroups-carry-rank-models-violating-two-root-identity: that builds a rank model free on one dihedral D_8 and violating the two-root identity; this uses the same permutation models to get freeness on every finite subgroup, exactly multiplicative disjoint cylinder defects and fixed-point-freeness.
  finite-subgroup-data-cannot-force-defect-submultiplicativity: that covers relations inside finite subgroups through one regular assignment; this covers every relation holding in a sofic subgroup, including elements of infinite order used as factors.
  anti-central-sofic-data-cannot-force-defect-submultiplicativity: that is the characteristic-three anti-central counterpart; this is the characteristic-two statement.
  leavitt-disjoint-cylinder-defects-strictly-submultiplicative: that is the open strict deficit; this shows a relation-only proof of it must use a nonsofic subgroup containing both frames, and would prove that subgroup nonsofic.
artifacts:
  - research/artifacts/fock-toeplitz-input-and-sofic-independence-2026-09-12.md
---

**ESTABLISHED** (route `sofic-subgroups-independent-cylinder-defects-proof`; artifact Section 2; independent
re-derivation requested from `w4-vf-gate`).

**Statement.** Let `R^x = L_(F_2)(1,2)^x = EL_3(R)` and let `H <= R^x` be sofic. Let `A_1, ..., A_k` be disjoint nonempty
proper cylinders with `iota_(A_i)(D_8) <= H`, where `D_8 = <x_12(1), x_23(1)>`. Then `H` has a characteristic-two rank
model `sigma` with:
* `rk sigma(alpha) = dim(alpha F_2[K]) / |K|` for every finite `K <= H` and every `alpha in F_2[K]`;
* `rk(D_(A_1) ... D_(A_k)) = (3/8)^k`;
* no nonzero fixed vector, whenever `H` contains an element of infinite order.

**Consequence.** No inequality `rk(D_A D_B) <= theta rk(D_A) rk(D_B)` with `theta < 1` follows from:
* group relations holding in a sofic subgroup that contains both frames;
* rank calculus;
* nontriviality and fixed-point-freeness.

A relation-only proof of `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` must use the model jointly on a
nonsofic subgroup containing `iota_A(D_8)` and `iota_B(D_8)`, and it proves that subgroup nonsofic.

**Special case: Toeplitz commutators.** They are covered: `x_12(t0)`, `x_23(s0)`, `x_12(1)` and `x_23(1)` generate a
unitriangular group of order 128 (artifact Proposition 1.1). So the quarter defect of
`natural-fock-quantized-compressors-miss-toeplitz-by-a-quarter` is a property of truncated-shift realizations, not a
constraint on rank models.

**Scope.** Arguments that also use the defect gap or near-minimal multiplicativity are not covered. Those are global
statements about all rank models of `R^x`, and they don't restrict to subgroups.

## Attempts

- Established, not open. The proof restricts a sofic approximation to the good free orbits of each finite subgroup
  and tensors the dihedral defect count.

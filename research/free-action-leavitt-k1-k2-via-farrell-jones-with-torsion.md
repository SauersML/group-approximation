---
rg: 2
id: free-action-leavitt-k1-k2-via-farrell-jones-with-torsion
kind: route
title: Full Farrell--Jones for the all-group tester gives every group the K-theoretic conjecture with coefficients; free actions then give K-trivial Leavitt hosts in all degrees
target: free-action-leavitt-tensor-hosts-have-trivial-k1-k2
requires:
  - farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts
  - full-farrell-jones-fixed-two-generator-all-group-tester
  - full-farrell-jones-for-fixed-two-generator-all-group-tester
---

Let `Λ` be finitely generated and act freely on a compact Hausdorff
zero-dimensional space `X`.

1. By `full-farrell-jones-for-fixed-two-generator-all-group-tester` (open), the
   tester `U` lies in `FJ`.
2. By `full-farrell-jones-fixed-two-generator-all-group-tester`, every group
   then lies in `FJ`, and in particular `Λ` does.
3. Membership in Lueck's Full Farrell--Jones class includes the K-theoretic
   Farrell--Jones conjecture with coefficients in every additive `Λ`-category,
   relative to `VCyc`. This is the hypothesis of
   `farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts`.
4. A free action makes every nontrivial element fixed-point free. So every
   finite subgroup acts freely.
5. That claim gives `K_n(B ⊗ L) = 0` for all `n ∈ Z`, and in particular for
   `n = 1, 2`. ∎

**What this decomposition shows.**
- The only open input is the Farrell--Jones conjecture. No further ring
  theory is needed: the torsion, `D_∞`-orbit and Nil issues of the earlier
  sketch are all closed by the established claim.
- The global statement is used only at `Λ`. Any construction proving
  `decidable-groups-lie-in-fp-free-minimal-crossed-products` with a
  Farrell--Jones acting group (for example hyperbolic, CAT(0), or built from
  such groups by the inheritance properties of `FJ`) bypasses step 1
  entirely. It gives (K) for that `Λ` directly from step 3 onward.

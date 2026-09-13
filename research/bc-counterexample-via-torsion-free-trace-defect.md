---
rg: 2
id: bc-counterexample-via-torsion-free-trace-defect
kind: route
title: A non-integer projection trace over a torsion-free group refutes surjectivity of reduced assembly
target: baum-connes-counterexample-group-exists
requires:
  - torsion-free-matrix-trace-defect-exists
  - assembly-image-traces-are-integral-for-torsion-free-groups
---

**Live.**

**Derivation.**
1. `torsion-free-matrix-trace-defect-exists` gives a torsion-free countable `Γ` and a
   projection `p ∈ M_n(C*_r Γ)` with `τ_*[p] = sum_i τ(p_ii) ∉ Z`.
2. `assembly-image-traces-are-integral-for-torsion-free-groups` gives
   `τ_*(mu_r(x)) ∈ Z` for every `x ∈ K_0^Γ(\underline{E}Γ)`. The trace convention is the same.
3. `τ_*` is a homomorphism on `K_0`, so `[p] ∉ mu_r(K_0^Γ(\underline{E}Γ))`.
4. So `mu_r` is not surjective, and `Γ` violates the Baum--Connes conjecture with trivial
   coefficients.

**Relation to the other routes.** This is the torsion-free form of the trace test. For groups
with torsion the target ring is `Lambda^G`, and it is void on `L^x`
(`bc-counterexample-via-rational-trace-mismatch`). The open input is shared with the
Kadison--Kaplansky program:
- by `kk-counterexample-via-g-star-z-scalarization` and
  `matrix-trace-defect-from-kk-counterexample`, it is equivalent to
  `kadison-kaplansky-counterexample-exists`;
- by `free-product-kk-iff-trace-conjecture-for-factors`, it passes to free products.

That lane's reviews are recorded as unreviewed on main. This route needs only the open claim
and the established integrality import.

**Where it cannot live.** Any group with surjective reduced assembly: a-T-menable, hyperbolic,
or a real-rank-one lattice. The module route `bc-counterexample-via-module-k-inexactness` is
the complementary source. It works over non-exact groups and says nothing about traces.

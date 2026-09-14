---
rg: 2
id: vertex-mismatch-needs-nonextendable-clifford-orbits-proof
kind: route
title: Compressors normalize the closed Kazhdan image, padding by induced orbit sums, then the exact-model argument
target: vertex-mismatch-needs-nonextendable-clifford-orbits
requires: [stable-vertex-mf-trace-models-need-inequivalent-marginals]
---

## Direct proof

The images of `pi^i` are dense in the coordinate projections of `K`, so
`pi^1, pi^2` are representations of `K`.  Restrictions to `Gamma` and to `L`
have the same invariant subspaces.

**1.**  For `t` in the compression semigroup `P_Gamma`, `t L t^(-1)` is the
closure of the image of `t Gamma t^(-1)`, hence contained in `L`.  A closed
subgroup of a compact Lie group containing a conjugate of itself equals that
conjugate (same dimension and same number of components).  So `t` normalizes
`L`.  `P_Gamma` generates `G` and normalizers are closed, so `L` is normal in
`K`.  Each `pi^i(k)` intertwines `pi^i|_L` with its `k`-conjugate, so the
multiplicities are `K`-invariant.

**2.**  Steps 1--2 of `stable-vertex-mf-trace-models-need-inequivalent-marginals-proof`
give an intertwiner partial isometry `V` between `pi^1|_Gamma` and `pi^2|_Gamma`
whose support and range, of equal rank, have normalized coranks at most
`eta^2`, where `eta = delta_n/epsilon`.  The mismatch lives in the two
complements, so `mu_n <= 2 eta^2 d_n`.

**3.**  Equivalence of the padded restrictions forces
`dim rho^1 = dim rho^2 = m`.  On `C^(d+m)` put `A = pi^1 + rho^1` and
`B = pi^2 + rho^2`.  Then `V + 0` intertwines `A|_Gamma` and `B|_Gamma` on
subspaces of corank at most `eta^2 d + m`, and cancellation of
finite-dimensional representations completes it to a unitary intertwiner `U`
with `||U - 1||_2 = O(eta + sqrt(m/(d+m)))`.  Define `tau(iota_1 g) = U A(g) U*`
and `tau(iota_2 g) = B(g)`; these agree on `Gamma`, so `tau` is a representation
of `D`.  For a fixed word `w` of length `l`,
`|tr tau(w) - tr sigma_n(w)| <= 2l ||U-1||_2 + 2m/(d+m) + o(1)`.  If
`m_n/d_n -> 0` along a subsequence, then `tr(tau_n(g)) -> 0` for every `g != e`
along it, so `D` is maximally almost periodic, a contradiction.

**4.**  `K_0` fixes every class in the dual of `L`, since characters vary
continuously and the classes are discrete.  So inertia groups `S` have finite
index and contain `L`.  If `omega` extends to `omega~` on `S`, Mackey's formula
gives `Res_L Ind_S^K omega~ = sum over O of omega'`, each member once, of
dimension `|O| dim(omega)`.  Adding `|Delta(O)|` copies to the deficient side
cancels `Delta` on `O`.  Summing over extendable orbits costs
`sum |Delta(O)| |O| dim(omega) <= mu_n`.

**Assembly.**  If `Delta_n` vanished on all non-extendable orbits for infinitely
many `n`, step 4 would cancel it at cost `<= 2 eta^2 d_n = o(d_n)`, contradicting
step 3.

---
rg: 2
id: sl3z-has-no-spectral-unconditional-completion
kind: claim
title: SL_3(Z) fails rapid decay, and no unconditional completion inside its reduced C*-algebra is closed under holomorphic calculus
distinct_from:
  hyperbolic-groups-have-property-rd: that is rapid decay for hyperbolic groups; this is the failure of rapid decay, and of every spectral unconditional completion, for SL_3(Z).
  lafforgue-unconditional-assembly-for-reductive-lie-subgroups: that is the positive assembly theorem for unconditional completions; this is why it does not reach the reduced C*-algebra of SL_3(Z).
artifacts:
  - research/artifacts/kk-sl3z-congruence-2026-09-12.md
---

**ESTABLISHED (citation).** Let `Γ = SL_3(Z)`.

1. `Γ` does not have property (RD) (Jolissaint, Trans. Amer. Math. Soc. 317 (1990)).
2. No unconditional completion `B(Γ)` of `C_c(Γ)` is a dense subalgebra of `C*_r(Γ)`
   closed under holomorphic calculus.

So Lafforgue's route from `lafforgue-unconditional-assembly-for-reductive-lie-subgroups`
to Baum–Connes, through a spectral unconditional completion, is closed for `SL_3(Z)`.

**Argument as the survey records it** (Gomez Aparicio–Julg–Valette, arXiv:1905.10081,
Remark 6.18, credited to Lafforgue, *Propriété (T) renforcée et conjecture de Baum–Connes*,
Clay Math. Proc. 11 (2010)):
- **The subgroup.** `H = Z^2 ⋊_A Z` with `A = [[3,1],[2,1]]` embeds in `SL_3(Z)` by
  `(v, n) -> [[A^n, v],[0, 1]]`. It is solvable, hence amenable.
- **Unconditional norms dominate ℓ¹ on `H`.** Amenability gives
  `||lambda_H(f)|| = ||f||_1` for `f >= 0`. An unconditional completion inside `C*_r(Γ)`
  therefore satisfies `||f||_B = || |f| ||_B >= ||lambda(|f|)|| = ||f||_1` on functions
  supported in `H`, so `B(H) = B(Γ) ∩ C*_r(H)` lies in `ℓ¹(H)`.
- **Contradiction.** `ℓ¹(H)` is not spectral in `C*_r(H)` (Jenkins, Bull. Amer. Math. Soc.
  75 (1969)).

**Caveats.**
- The primary papers [Jol90], [Laf10] and [Jen69] were not read.
- The survey's sketch closes by spectral radii: for self-adjoint `x ∈ C[H]`,
  `r_(ℓ¹(H))(x) <= r_B(x) = ||lambda(x)||`. That sketch needs the non-symmetry of `ℓ¹(H)`
  to be witnessed by a finitely supported element. This was not checked against Jenkins.
- The same argument should run in any finite-index subgroup of `SL_3(Z)`, using `A^k` and
  a sublattice of translations. It is not imported here.

**Context.** Kadison–Kaplansky holds on `H` itself, since amenable groups have the
Haagerup property. So the spectral excess that blocks the method already appears on
subgroups carrying no counterexample.

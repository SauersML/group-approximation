---
rg: 2
id: weakly-finite-leavitt-hosts-reduce-to-bounded-matrix-size-proof
kind: route
title: Łoś carries weak finiteness at each size to an ultraproduct of hosts, and finite presentations carry hosts down to factors
target: weakly-finite-leavitt-hosts-reduce-to-bounded-matrix-size
requires:
  - binary-leavitt-unit-group-is-simple
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
  - leavitt-prime-field-units-generated-by-v-and-one-transvection
  - thompson-v-finitely-presented-infinite-simple
  - leavitt-unit-group-finitely-presented
artifacts:
  - research/artifacts/weakly-finite-hosts-construction-census-2026-09-12.md
---

**Proof.** Artifact Section 4.

1. **Upward.**
   - `W = ∏_U W_n` over a nonprincipal ultrafilter on `N`.
   - "`AB = I_k` implies `BA = I_k`" is first-order in `2k^2` variables and holds for `n >= k`, so Łoś gives it in
     `W`. `p·1 = 0` passes the same way.
   - `ρ = (ρ_n)_U`. Binary: `ρ_n` is injective by simplicity, so `ρ(g) ≠ 1` for `g ≠ 1`. Ternary: `ρ(z) = -1`.
2. **Downward.**
   - **`ρ|V` is injective.** Binary: `ρ` is injective. Ternary: `ρ(V) = 1` would give `ker ρ ⊄ {±1}`, so
     `ker ρ = G_3`, contradicting `ρ(z) = -1`. Then use simplicity of `V`.
   - **Passing to factors.** Pick representatives `a_j(s)` and `b_j(s)` of `ρ(s)` and `ρ(s)^(-1)` over a finite
     presentation `⟨S | R⟩` of `V`. The conditions `a_j(s) b_j(s) = 1 = b_j(s) a_j(s)` and `r(a_j) = 1` for
     `r ∈ R`, together with `a_j(s_0) ≠ 1`, are finitely many and hold on a `U`-large set.
   - On it, `s ↦ a_j(s)` is an injective homomorphism `V -> A_j^x`.
   - For `p = 2`, repeat with the finite presentation of `G`.
   - Finite rings have finite unit groups, and `V` is infinite simple, so they carry no nontrivial image of `V`.

---
rg: 2
id: leavitt-algebra-has-no-unital-rank-model-proof
kind: route
title: Simplicity plus non-direct-finiteness against a directly finite ultraproduct
target: leavitt-algebra-has-no-unital-rank-model
requires:
  - binary-leavitt-algebra-not-directly-finite
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/leavitt-unit-rank-model-construction-audit-2026-09-12.md
---

Section 1 of the artifact.

1. **The ultraproduct is directly finite.** In `M = prod_omega M_(n_k)(F)/d_omega`,
   `rk(1 - ab) = rk(1 - ba)` for all `a, b`: over any field the map `v -> bv`
   sends `ker(1 - ab)` bijectively onto `ker(1 - ba)`, since `v = abv` on that
   kernel (Arzhantseva--Paunescu, arXiv:1212.6780, Proposition 2.8). So
   `ab = 1` implies `ba = 1` in `M`.

2. **`R` is simple.** `L_(F_2)(1,2)` is the Leavitt path algebra of the graph
   with one vertex and two loops, which is simple. A unital homomorphism
   `phi : R -> M` is nonzero, so `ker phi` is a proper two-sided ideal, hence
   `ker phi = 0` and `phi` is injective.

3. **Contradiction.** `phi(t_0) phi(s_0) = phi(t_0 s_0) = phi(1) = 1_M`. By (1),
   `phi(s_0) phi(t_0) = 1_M = phi(1)`, so `phi(s_0 t_0 - 1) = 0`. By
   `binary-leavitt-algebra-not-directly-finite`, `s_0 t_0 - 1 != 0` in `R`,
   contradicting injectivity.

4. **Approximate form.** A sequence of unital rank-approximate homomorphisms
   `phi_k` assembles into a single unital homomorphism `phi : R -> M` (additivity
   and approximate multiplicativity become exact modulo `d_omega`; the images
   stay nonzero because each `phi_k(a)` has rank bounded away from `0`). Steps
   1--3 then apply. The argument is characteristic free, so it holds over every
   field `F`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 6 of the linear-family verification artifact.* Scope remark: the Steinberg relations force approximate additivity and multiplicativity of `phi`, but not `phi(1) = 1`. The no-go survives anyway. `p = phi(1)` is idempotent, `phi : R -> pMp` is unital, and corners of rank ultraproducts are directly finite, since `rk(1 - ab) = rk(1 - p) + rk(p - ab)`. So every nonzero elementary-matrix model is excluded. Also read "any field" as ring homomorphisms: `R` has characteristic two.

---
rg: 2
id: subshift-crossed-product-gl-has-no-distorted-elements-proof
kind: route
title: Krylov dimension against propagation over a finite field
target: subshift-crossed-product-gl-has-no-distorted-elements
requires: []
artifacts:
  - research/artifacts/sk-sl3z-bandwidth-distortion-obstruction-2026-09-13.md
---

1. **Module.** Let V = ⊕_{x∈X}⊕_{t∈Z} F_q^m, with f δ_{x,t} = f(T^t x)δ_{x,t} and u δ_{x,t} = δ_{x,t+1}.
   - This is a representation of R, since u f u^{-1} = f∘T^{-1}.
   - M_m(R) acts entrywise, and faithfully: A = Σ_j A_j u^j sends δ_{x,0}ξ to Σ_j A_j(T^j x)ξ δ_{x,j}, whose terms lie in distinct slots.
2. **Propagation.** Put p(A) = max{|j| : A_j ≠ 0}. A moves slots by at most p(A), and p(AB) ≤ p(A)+p(B). So p(z^n) ≤ w|z^n|_S.
3. **Krylov bound.** For a slot vector v = δ_{x,t}⊗ξ, span{z^n v : n < N} lies in the slots {x}×[t−wℓ(N), t+wℓ(N)], where ℓ(N) = max_{n<N}|z^n|_S. So it has dimension at most m(2wℓ(N)+1).
4. **Uniform degree bound.** Suppose τ = lim|z^n|_S/n < 1/(2wm). By Fekete, |z^n|_S ≤ (τ+ε)n + C with 2wm(τ+ε) < 1. So m(2wℓ(N)+1) < N for all N ≥ N_0, uniformly in v, and p_v(z)v = 0 for some monic p_v of degree < N_0.
5. **Finite order.**
   - P = lcm{monic polynomials over F_q of degree < N_0} kills every slot vector, so P(z) = 0 by faithfulness.
   - Write P = t^aQ with Q(0) ≠ 0. Then Q(z) = 0, so z is a unit of the finite ring F_q[t]/(Q) and has finite order.
6. So an element of infinite order has τ ≥ 1/(2wm). ∎

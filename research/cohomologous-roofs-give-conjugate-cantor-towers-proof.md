---
rg: 2
id: cohomologous-roofs-give-conjugate-cantor-towers-proof
kind: route
title: Proof - move each orbit's base points by the transfer function
target: cohomologous-roofs-give-conjugate-cantor-towers
requires: []
artifacts: [research/artifacts/sk-cartan-counterexample-2026-09-13-part1.md]
---
Direct proof, with details in the artifact §1.

- **Partial sums.** R_k(z) = Σ_{0≤j<k} r(σ^j z) for k ≥ 0 and R_k(z) = −Σ_{k≤j<0} r(σ^j z) for k < 0, and R′_k likewise.
  Summing r′ − r = h − h∘σ gives R′_k(z) − R_k(z) = h(z) − h(σ^k z) for all k ∈ Z.
- **Representatives.** σ has no periodic points. So T_r^n(z,0) = T_r^{n″}(z″,0) iff z″ = σ^k z and n = n″ + R_k(z) for a
  unique k.
- **Well defined.** Φ(T_r^n(z,0)) = T_{r′}^{n+h(z)}(z,0) does not depend on the representative: (σ^k z, n − R_k(z)) goes
  to T_{r′}^{n − R_k(z) + h(σ^k z) + R′_k(z)}(z,0) = T_{r′}^{n+h(z)}(z,0).
- **Equivariant.** Φ∘T_r = T_{r′}∘Φ.
- **Inverse.** Ψ(T_{r′}^n(z,0)) = T_r^{n−h(z)}(z,0), by the same computation with −h.
- **Continuity.** On the clopen pieces where r and h are constant, Φ and Ψ are compositions of z ↦ (z,0) with a fixed
  power of the tower map.

**Corollary.**
- The tower over (V,S_V) with roof r_V is conjugate through θ to the tower over (U,T_U) with roof r_V∘θ.
- The unit-class hypothesis says that r_V∘θ − r_U is a coboundary in C(U,Z), so the theorem applies.
- The flip case uses (Y,S^{-1}). Its induced map on V is S_V^{-1}, and its return time r_V∘S_V^{-1} has the same class as
  r_V. ∎

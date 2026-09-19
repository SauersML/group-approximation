---
rg: 2
id: virtually-torsion-free-mf-radical-is-torsion-free-proof-b
kind: route
title: Push the radical and the corner through the regular representation of one finite quotient
target: virtually-torsion-free-mf-radical-is-torsion-free
requires:
  - mf-positive-controls
  - universal-mf-quotient
artifacts:
  - research/mf-positive-controls.md
---

## Why sufficient

**(R1).**  Let `N` be normal of finite index in `H`.  The quotient `H/N` is
finite, hence residually finite, hence MF by `mf-positive-controls`.  So
there is a homomorphism `sigma : H/N -> U(prod M_k / sum M_k)` with trivial
kernel.  The composite `H -> H/N -> U(corona)` has kernel exactly `N`.
`Rad_MF(H)` is the intersection of all such kernels (`universal-mf-quotient`),
so `Rad_MF(H) <= N`.

**(R2).**  `Core_H(E)` is the intersection of the finitely many conjugates of
`E`.  It is normal of finite index in `H` and lies in `E`, so it is
torsion-free.  By (R1), `Rad_MF(H) <= Core_H(E)`.  Every element of `W(H)`
lies in a finite normal subgroup, so it has finite order.  Hence
`W(H) intersect Core_H(E) = 1`.

**(R3).**  Put `N = Core_H(E)`, `Q = H/N` (finite, of order `n`) and
`pi : H -> Q`.

1. `K intersect N <= K intersect E = 1`, since `K` is finite and `E` is
   torsion-free.  So `pi` is injective on `K`.
2. Let `lambda` be the left-regular representation of `Q` on
   `l^2(Q) = C^n`, extended linearly to `C[H] -> M_n`.  It is a unital star
   homomorphism.  It is faithful on the group `Q`, hence on `pi(K)`.
3. `P = lambda(p_K)`, with `p_K = |K|^-1 sum_(k in K) k`, is the orthogonal
   projection onto the `pi(K)`-fixed vectors.  If `P = 1` then
   `lambda(k) = lambda(k) P = P = 1` for every `k in K`, which contradicts
   faithfulness because `K != 1`.  So `lambda(q_K) = 1 - P` is a projection
   of some rank `r >= 1`.  Concretely `r = n (1 - 1/|K|)`, because
   `pi(K)` acts freely on `Q`.
4. `lambda` maps `q_K C[H] q_K` into the corner
   `(1-P) M_n (1-P) = M_r`, sending `q_K` to the unit.  So
   `rho = lambda o Phi : B -> M_r` is a unital star homomorphism.
5. `tau = tr_r o rho` is a tracial state on `B`.  It is positive, because
   `tau(b* b) = tr_r(rho(b)* rho(b)) >= 0`.  It is unital and tracial, and it
   factors through a matrix algebra, so it is Connes-embeddable (it is even
   amenable).
6. So `B` has a Connes-embeddable tracial state, which contradicts the
   hypothesis on `B`.  No such `Phi` exists.

Only the finite quotient `Q` enters.  The steps use no normality of `K`,
no finite radical, no recursive presentation and no Property `(T)`.

## Property-T audit

- The route uses residual finiteness implies MF, but only for a finite
  group.
- It uses the definition of the radical.
- The rest is linear algebra of one finite regular representation.

No Kazhdan input appears.

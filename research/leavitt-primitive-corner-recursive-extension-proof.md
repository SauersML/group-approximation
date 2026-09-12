---
rg: 2
id: leavitt-primitive-corner-recursive-extension-proof
kind: route
title: Conjugate the evaluation by the first matrix unit and feed the scalar copy in
target: leavitt-primitive-corner-recursive-extension
requires: [leavitt-matrix-amplification-in-unit-group-algebra]
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
  - research/artifacts/verify-s3-corner-2026-08-17.py
---

## Direct proof

Notation as in the prerequisite: `Theta_2((a_ij)) = sum s_i a_ij t_j`,
`Phi(r)_ij = t_i r s_j`, `p_0 = s_0t_0 = Theta_2(E_11)`, `H = <u,v> ~= S_3`
the constant matrices, `e = [g]+[g^2]`, and the four matrix units `f_ij` of
`F_2[H]` with `f_11 + f_22 = e`, `pi(f_11) = p_0`.  Write `f = f_11`,
`T = f S f`, `K = ker(pi)`.

**`f` is an idempotent under `e`, of augmentation zero.**  `f_11 f_11 = f_11`
from the matrix-unit relations, and `f e = f(f_11 + f_22) = f`.  `f` has four
group-basis terms, so `eps(f) = 0`.

**Step 1 — `rho` is a unital ring homomorphism.**  For `a in T`,
`pi(a) = pi(faf) = p_0 pi(a) p_0`.  Hence for `a, b in T`,

    rho(a) rho(b) = t_0 pi(a) s_0 t_0 pi(b) s_0 = t_0 pi(a) p_0 pi(b) s_0
                  = t_0 pi(ab) s_0 = rho(ab),

and `rho(f) = t_0 p_0 s_0 = (t_0 s_0)(t_0 s_0) = 1`.  Additivity is clear.

**Step 2 — `rho` is onto.**  Given `r in R`, the matrix `[[r,1],[1,0]]` has
inverse `[[0,1],[1,r]]` in characteristic two, so `h_r = Theta_2[[r,1],[1,0]]`
is a unit of `R`, i.e. an element of `G`.  Then
`rho(f [h_r] f) = t_0 p_0 h_r p_0 s_0 = r`, since `p_0 h_r p_0 = Theta_2(E_11
[[r,1],[1,0]] E_11) = Theta_2(r E_11) = s_0 r t_0`.

**Step 3 — `lambda` is a ring homomorphism into `T`.**  `delta_*(S)` commutes
with `f`, because `delta(G)` centralizes `H` (Step 3 of the prerequisite's
proof).  So with `f^2 = f`,

    lambda(a) lambda(b) = delta_*(a) f delta_*(b) f = delta_*(ab) f = lambda(ab),

`lambda(1) = f`, and `f lambda(a) f = lambda(a)`, so the image is in `T`.

**Step 4 — `lambda` is injective.**  Inside
`F_2[delta(G) x H] ~= S (x)_(F_2) F_2[H]` the map is `a |-> a (x) f`, and
tensoring with the nonzero vector `f` over a field is injective.  Concretely:
the products `delta(q) h` have unique `(q,h)` coordinates, so no cancellation
between distinct coefficients of `a` is possible.

**Step 5 — `rho . lambda = pi`.**  On a basis element `[q]`,

    pi(lambda([q])) = delta(q) pi(f) = delta(q) p_0
                    = (s_0 q t_0 + s_1 q t_1) s_0 t_0 = s_0 q t_0,

using `t_0 s_0 = 1`, `t_1 s_0 = 0`.  Hence
`rho(lambda([q])) = t_0 s_0 q t_0 s_0 = q`.  Extend by linearity.

**Step 6 — the Peirce identification.**  `Psi(x)_ij = f_1i x f_j1` is the
standard isomorphism `eSe -> M_2(T)` attached to a complete set of matrix
units, with inverse `(a_ij) |-> sum f_i1 a_ij f_1j`.  Since
`pi(f_1i x f_j1) = pi(f_1i) pi(x) pi(f_j1)` and the `pi(f_ij)` are the matrix
units `E_ij` of `M_2(R)` transported by `Theta_2`, one gets
`rho(f_1i x f_j1) = t_i pi(x) s_j = Phi(pi(x))_ij`, i.e.
`Phi . pi|_(eSe) = M_2(rho) . Psi`.  Therefore
`ker(pi|_(eSe)) ~= M_2(ker rho)`.

**Step 7 — `ker(rho) = f K f`.**  For `a in T`, `pi(a) = p_0 pi(a) p_0 = s_0
rho(a) t_0`, so `rho(a) = 0` iff `pi(a) = 0`.

**Step 8 — the kernel copy.**  By Step 5, `rho(lambda(k)) = pi(k) = 0` for
`k in K`, so `lambda(K) <= ker(rho) = f K f`, injectively by Step 4.

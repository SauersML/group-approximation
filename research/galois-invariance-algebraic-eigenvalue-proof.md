---
rg: 2
id: galois-invariance-algebraic-eigenvalue-proof
kind: route
title: Split the kernel of a product over distinct conjugate eigenvalues and count dimensions
target: galois-invariance-implies-algebraic-eigenvalues
requires: []
---

Let `X in M_n(Qbar[H])`, write `T = r_X` on `l2(H)^n`, and suppose
`delta = dim ker(T - w) > 0` for a transcendental `w`.  Automorphisms of `C`
fixing `Qbar` fix `X`, send `X - wI` to `X - sigma(w)I`, and move `w` to every
transcendental number.  By invariance `dim ker(T - u) = delta` for uncountably
many distinct `u`.

Choose distinct such `u_1..u_m` with `m delta > n`.  Put
`Q(t) = prod_i (t - u_i)`, `W = ker Q(T)` and `V_i = ker(T - u_i)`, all closed
`N(H)`-submodules.  The Lagrange polynomials
`e_i(t) = prod_(j != i) (t - u_j)/(u_i - u_j)` satisfy `sum_i e_i = 1` and
`(t - u_i) e_i(t) = c_i Q(t)`.  So on `W` each `e_i(T)` maps into `V_i`, and
`e_j(T) v = delta_ij v` for `v in V_i`.  The sum map from the direct sum of the
`V_i` to `W` is therefore a bounded module isomorphism with inverse
`v -> (e_i(T) v)_i`, and

```text
m delta = sum_i dim V_i = dim W <= dim l2(H)^n = n,
```

a contradiction.  So every eigenvalue of `T` is algebraic.  QED

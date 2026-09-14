---
rg: 2
id: root-extensions-descend-from-locally-universal-proof
kind: route
title: Embed into an ultrapower of the universal algebra, solve coordinatewise, and take the ultraproduct of the extensions
target: root-extensions-descend-from-a-locally-universal-algebra
requires: []
---

Fix `M`, unitaries `u_1, ..., u_k in U(M)`, and `w` with `deg_t(w) != 0`.
Let `j : M -> S^omega` be a unital trace-preserving embedding over an index
set `I`.

1. **Unitary lifts in a finite von Neumann algebra.**  Let `x in S` with
   `||x|| <= 1`, and write `x = v |x|` (polar decomposition).  The partial
   isometry `v` has initial projection `p = v^* v` (the support of `|x|`) and
   final projection `q = v v^*`.
   - In the finite algebra `S`, `p ~ q` implies `1 - p ~ 1 - q`.  So there is
     a partial isometry `z` from `1 - p` onto `1 - q`, and `v' = v + z` is a
     unitary.
   - Since `z |x| = z p |x| = 0`, we have `x = v' |x|`.
   - For every real `lambda >= 0`, `|lambda - 1| <= |lambda^2 - 1|`, so
     `|| x - v' ||_2 = || |x| - 1 ||_2 <= || x^* x - 1 ||_2`.

   Apply this to a bounded representative `(x_s)_(s in I)` of each `j(u_i)`.
   Then `lim_omega || x_s^* x_s - 1 ||_2 = 0`, so the unitaries `(v'_(i,s))_s`
   represent `j(u_i)`.
2. **Coordinatewise roots.**  For each `s in I`, apply the hypothesis to
   `S` with coefficients `v'_(1,s), ..., v'_(k,s)`.  It yields a tracial
   algebra `(N_s, sigma_s)`, a unital trace-preserving embedding
   `iota_s : S -> N_s`, and `T_s in U(N_s)` with
   `w(iota_s(v'_(1,s)), ..., iota_s(v'_(k,s)), T_s) = 1`.
3. **Ultraproduct.**  Let `N = prod_omega N_s` be the tracial ultraproduct.
   - The map `Phi : S^omega -> N`, `(y_s) -> (iota_s(y_s))`, is well defined:
     each `iota_s` preserves operator norms and `||.||_2`, so bounded
     sequences go to bounded sequences and `omega`-null sequences to
     `omega`-null sequences.
   - `Phi` is a unital `*`-homomorphism and preserves the ultraproduct traces.
     A trace-preserving unital `*`-homomorphism of tracial von Neumann
     algebras is injective, and it is normal because it is isometric for
     `||.||_2` on bounded sets.
   - So `Phi o j : M -> N` is a unital trace-preserving embedding.
4. **The root.**  `T = (T_s)` is a unitary of `N`.  Word evaluation is
   coordinatewise on representatives, so

       w(Phi(j(u_1)), ..., Phi(j(u_k)), T)
         = ( w(iota_s(v'_(1,s)), ..., iota_s(v'_(k,s)), T_s) )_omega = 1 .

   So `(N, Phi o j, T)` witnesses the conclusion for `M`.

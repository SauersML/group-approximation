---
rg: 2
id: stw83-cuntz-circle-graph-split-index-proof
kind: route
title: Compute the Fredholm index of the loop row and correct it by rank one when it vanishes
target: stw83-cuntz-circle-graph-splits-iff-k-equals-n-minus-1
requires: []
artifacts:
  - research/artifacts/stw99-constant-symbol-pullback-2026-09-16.md
---

The full proof is Proposition 6 of the artifact.  It uses the model from
Section 5.1 there, which rests only on the gauge-invariant uniqueness theorem
and matrix-unit computations:

```text
A = C*(F_(n,k)) = C(T,K) + D_0 tensor 1,     D_0/K = O_n,     S_i = q(T_i).
```

**Index.**  `T_i` sends `delta_(w g_j)` to `delta_(e_i w g_j)` and kills
`delta_v`, with orthogonal ranges.
* So `R=[T_1 ... T_n]:H^n->H` has kernel `(C delta_v)^n`, of dimension `n`.
* The cokernel is spanned by `delta_v,delta_(g_1),...,delta_(g_k)`, so it has
  dimension `k+1`.
* Hence `ind R=n-k-1`.

**Necessity.**  Let `sigma:O_n->A` split the quotient map.
1. *Setup.*  Put `p=sigma(1)` and `W_i=sigma(S_i)`.  Then `1-p` lies in
   `C(T,K)` and is a continuous projection-valued function, so its rank `r`
   is finite.
2. *Compact perturbation.*  Write `W_i=c+x tensor 1` with `c` in `C(T,K)`
   and `x` in `D_0`.  Then `q(x)=S_i=q(T_i)`, so `W_i(t)-T_i` is compact for
   every `t`.
3. *Index of the perturbed row.*  For fixed `t`, the `W_i(t)` are isometries
   on `p(t)H` with orthogonal ranges summing to `p(t)`, and they vanish on
   `(1-p(t))H`.  So `[W_1(t) ... W_n(t)]` has kernel dimension `nr` and
   cokernel dimension `r`, hence index `(n-1)r`.
4. *Conclusion.*  By invariance of the index under compact perturbation,
   `n-k-1=(n-1)r`, that is, `k=(n-1)(1-r)`.  Since `k>=1` and `r>=0`, we get
   `r=0` and `k=n-1`.

**Sufficiency.**  Let `k=n-1`, put `xi_i=delta_(g_i)` for `i<n` and
`xi_n=delta_v`, and define `W_i=T_i+|xi_i><delta_v|` in `D_0`.
* *Isometries.*  `T_i^*xi_i=0` and `T_i delta_v=0`, so
  `W_i^*W_i=(1-E_v)+E_v=1`.
* *Range projections.*  `W_iW_i^*=T_iT_i^*+|xi_i><xi_i|`.
* *Cuntz relation.*  By the Cuntz--Krieger relation at `u`,
  `sum_i T_iT_i^*=1-E_v-sum_(j<n)|delta_(g_j)><delta_(g_j)|`, hence
  `sum_i W_iW_i^*=1`.
* *The section.*  Universality of `O_n` gives a unital `rho:O_n->D_0` with
  `q rho=id`.  Then `b |-> rho(b) tensor 1` is a *-homomorphic section of
  `A->O_n`, and `D_0=K+rho(O_n)`.

The integer matrices in
`experiments/stw99-constant-symbol-pullback-2026-09-16/check_fnk.py` confirm
the kernel and cokernel counts and the Cuntz relations for `W_i` on
truncations with `2<=n<=4` and `1<=k<=3`.  This is a sanity check only.

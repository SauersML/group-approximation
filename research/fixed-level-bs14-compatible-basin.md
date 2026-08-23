---
rg: 2
id: fixed-level-bs14-compatible-basin
kind: claim
title: Fixed Iwahori levels are finite and stable, but diagonalization needs a compatible basin
distinct_from:
  bs14-full-commutant-finite-period-preconditioner: that constructs the bounded packet skeleton and its coboundary inverse; this audits whether qualitative stability at every bounded level can be diagonalized.
  bs14-flexible-cross-packet-boundary-reconciliation: that asks for the final uniform repair; this gives an exact sufficient fixed-level formulation and the quantifier fence on a naive proof.
  bs14-exact-representation-variety-is-hs-locally-rigid: that aligns two exact BS cores with a uniform modulus; this concerns the extra involution over one preconditioned core.
---

For `K,M>=2`, set

```text
N_K=lcm_(1<=m<=K)(4^m-1),
L_(K,M)=M lcm(1,...,K).                                (FLB1)
```

Every core produced by
`bs14-full-commutant-finite-period-preconditioner` satisfies

```text
S^N_K=1,                 R^L_(K,M)=1.                 (FLB2)
```

Thus its image factors through the finite metacyclic group

```text
B_(K,M)=<r,s | r^L=1,s^N=1, r s r^(-1)=s^4>.         (FLB3)
```

The remaining fixed-level relative problem is the arbitrary-multiplicity
matrix representation problem for

```text
Gamma_(K,M)=<x,r,s | x^2,(xr)^2,(xs^2)^3,(xrs)^3,
                       r s r^(-1)s^(-4),r^L,s^N>.     (FLB4)
```

The group `Gamma_(K,M)` is finite.  Indeed the full presentation before the
two power rows is `PSL_2(Z[1/2])`, and the normal closure of the nontrivial
unipotent power `s^N` has finite index by the S-arithmetic normal-subgroup
theorem.  Therefore finite-group Hilbert--Schmidt stability supplies, for
every fixed `(K,M)`, a flexible modulus `f_(K,M)` on some radius
`delta_(K,M)>0`.  This closes the fixed-level arbitrary-multiplicity
problem unconditionally; the modulus is not uniform in `(K,M)`.

Let

```text
alpha_(K,M)=C_0(sqrt(8/K)+pi/M)                       (FLB5)
```

be the word-Lipschitz defect introduced in the four `x`-relations by the
preconditioning.  For the fixed-level moduli above, a cofinal sequence
`(K_j,M_j)` proves
`bs14-relative-involution-extension-stability` provided

```text
alpha_j < delta_j/2,
alpha_j -> 0,
f_j(2 alpha_j) -> 0.                                  (FLB6)
```

Indeed, for an original defect `epsilon` small relative to `alpha_j`, word
Lipschitzness puts the preconditioned tuple inside the `2alpha_j` ball;
fixed-level repair then costs `f_j(2alpha_j)`, and the preconditioning cost
also tends to zero.

However, the now-established flexible stability of every fixed
`Gamma_(K,M)` does not imply `(FLB6)`.  It only says each `delta_(K,M)>0`
and `f_(K,M)(t)->0` with `(K,M)` fixed.  Those radii may shrink faster than
`alpha_(K,M)`; for example the abstract schedules

```text
alpha_j=1/j,                 delta_j=exp(-j)           (FLB7)
```

satisfy both pointwise statements and admit no usable diagonal.  The
original microstate defect tending to zero cannot remove the fixed
preconditioning error `alpha_j`.

Under the compatibility hypotheses `(FLB6)`, this bypass would prove the
qualitative flexible endpoint, not the sharper quadratic padding estimate
`(FBR2)` in `bs14-flexible-cross-packet-boundary-reconciliation`.  Without
`(FLB6)`, no endpoint follows from the pointwise fixed-level statements.

Therefore the fixed-period strategy has isolated the sole surviving
uniformity problem.  The whole short-support endpoint is finite and stable.
What is still needed is either a lower bound on its basin and modulus in
terms of `K,M`, or a preconditioner whose error is adapted to that basin.
Pointwise finite-group stability is logically insufficient for the moving
staircase.

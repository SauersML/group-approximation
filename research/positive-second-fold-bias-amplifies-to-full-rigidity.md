---
rg: 2
id: positive-second-fold-bias-amplifies-to-full-rigidity
kind: claim
title: Any uniform positive second-fold bias tensor-amplifies to full fold-square rigidity
distinct_from:
  congruence-tensor-regularizes-sl3-swap-profile: that imposes the actor and swap trace profile without changing fold moments; this uses diagonal tensor powers to upgrade a fixed positive fold bias to convergence of the fold square to one.
  sl3-swap-extension-has-defect-only-fold-square-rigidity: that is the open rigidity statement itself; this proves it is equivalent to the apparently weaker positive-bias terminal.
  projective-transfer-linear-bound-equals-no-ultraproduct-leak: that identifies a universal projective transfer inequality with an ultraproduct leak exclusion; this gives a direct tensor-power equivalence for one explicit real fold moment.
---

**ESTABLISHED AMPLIFICATION EQUIVALENCE.**  For the arithmetic swap extension

```text
E=<SL_3(Z[1/2]),s | s^2=1, [s,SL_3(Z)]=1>
```

the following are equivalent:

1. `sl3-swap-extension-has-defect-only-fold-square-rigidity`;
2. `regular-actor-balanced-swap-has-positive-second-fold-bias`;
3. there is an `epsilon_*>0` such that every vanishing-defect sequence of
   arbitrary finite-dimensional assignments, after rounding `s` to an
   involution `S_n`, satisfies

   ```text
   liminf_n Re tr((H_nS_nH_n^*S_n)^2)>=epsilon_*.
                                                               (PBA1)
   ```

The equivalence of 2 and 3 is
`congruence-tensor-regularizes-sl3-swap-profile`.  Statement 1 plainly
implies 3.  It remains to prove that 3 implies 1.

Put

```text
V_n=H_nS_nH_n^*S_n,             b_n=tr(V_n^2).
```

The number `b_n` is real.  Indeed `V_n` is the product of two self-adjoint
involutions, and cyclicity gives

```text
conjugate(tr(V_n^2))=tr(V_n^(-2))=tr((S_nH_nS_nH_n^*)^2)
                    =tr(V_n^2).                         (PBA2)
```

Suppose fold-square rigidity fails.  After a subsequence, there is `c>0`
with

```text
b_n<=1-c.                                                (PBA3)
```

If `b_n<=0` along a further subsequence, `(PBA1)` already fails.  Otherwise
assume `0<b_n<=1-c`.  Choose integers `k_n->infinity` sufficiently slowly
that `k_n delta_n->0`, where `delta_n` bounds the rounded assignment's
presentation defect.  Take the diagonal tensor-power assignments

```text
rho_n^(tensor k_n).
```

For every relator unitary `R_n`, telescoping gives

```text
||R_n^(tensor k_n)-I||_2
 <=k_n||R_n-I||_2,                                      (PBA4)
```

so the tensor-power defect still tends to zero.  Its fold is
`V_n^(tensor k_n)`, hence its real second-fold trace is

```text
tr((V_n^(tensor k_n))^2)=b_n^(k_n)
 <=(1-c)^(k_n)->0.                                      (PBA5)
```

This contradicts `(PBA1)`.  Therefore every vanishing-defect sequence has
`b_n->1`, equivalently

```text
||(H_nS_nH_n^*S_n)^2-I||_2^2=2(1-b_n)->0.
```

The sequential statement supplies the defect-only modulus by the usual
contrapositive: otherwise choose assignments of defect tending to zero with
a fixed positive fold-square defect.

Thus the positive-bias terminal is not a genuinely weaker stability gate.
Tensor amplification and actor-profile regularization recover the full
fold-square claim.

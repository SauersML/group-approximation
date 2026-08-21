---
rg: 2
id: leavitt-prefixes-form-exponential-heisenberg-packet
kind: claim
title: Depth-n relative Leavitt prefixes form 2^n exact Heisenberg pairs over the active root
distinct_from:
  toeplitz-defect-roots-form-independent-heisenberg-cells: that attaches one transverse root pair to each orthogonal Toeplitz defect idempotent; this obtains an exponentially large identity pairing from the two-sided Leavitt prefix relations and one common active root.
  commuting-schur-replicas-force-exponential-dimension: that uses commuting replicas of finite Schur packets; this embeds the generalized Pauli packet directly in one Steinberg group through coefficient words.
  affine-leavitt-steinberg-mark-is-fd-invisible: that proves every exact finite-dimensional representation kills the active root by a finite coefficient quotient; this gives an explicit quantitative family of finite subgroups explaining the dimension pressure.
---

Let `R=L_A(S)` be the free relative binary Leavitt envelope over a finite
field `k` of characteristic `p`. For a binary word
`alpha=(alpha_1,...,alpha_n)`, define

```text
t_alpha=t_(alpha_1)...t_(alpha_n),
s_alpha=s_(alpha_n)...s_(alpha_1).                       (LHP1)
```

Repeated use of `t_i s_j=delta_(ij)A` and the active support relations gives

```text
t_alpha s_beta=delta_(alpha,beta) A.                     (LHP2)
```

Inside `St_5(R)`, put

```text
X_alpha=x_12(t_alpha),
Y_beta =x_23(s_beta),
J_A    =x_13(A).                                         (LHP3)
```

Then the `N=2^n` pairs satisfy

```text
X_alpha^p=Y_alpha^p=J_A^p=1,
[X_alpha,X_beta]=[Y_alpha,Y_beta]=1,
[X_alpha,Y_beta]=J_A^(delta_(alpha,beta)),
J_A central in the generated subgroup.                  (LHP4)
```

The generated subgroup is the finite Heisenberg group of a nondegenerate
`N`-dimensional pairing over `F_p`; in particular `J_A` has order `p` there.
For every finite-dimensional complex representation and every nontrivial
`p`th-root eigenvalue `zeta` of `J_A`, the `zeta`-spectral sector has
dimension divisible by

```text
p^N=p^(2^n).                                             (LHP5)
```

Consequently any finite-dimensional representation in which `J_A` acts
nontrivially has dimension at least `p^(2^n)`. Since this holds for every
`n`, the exact finite-dimensional collapse of the active root follows again.
Unlike the finite-quotient proof, `(LHP5)` exposes the quantitative mechanism:
one more Leavitt prefix bit doubles the symplectic rank and squares the
minimum marked dimension.

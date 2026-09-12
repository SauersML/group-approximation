---
rg: 2
id: raw-gns-kernel-does-not-create-character-gap-proof
kind: route
title: Mix with the regular trace to erase every nontrivial scalar stabilizer
target: non-ce-trace-does-not-promote-to-subgroup-character-gap
requires:
  - separable-finite-algebras-have-symmetry-bases
---

First, the projective GNS kernel of a trace gives phase consistency but no
soundness by itself.  If `tau` is tracial and `|tau(g)|=1`, equality in
Cauchy--Schwarz gives

```text
pi_tau(g) xi_tau = tau(g) xi_tau.
```

The tracial GNS `2`-norm then promotes this vector equality to
`pi_tau(g)=tau(g)I`: multiplying by any group element preserves the zero
`2`-norm.  Hence

```text
K_tau={g:|tau(g)|=1}
```

is a normal subgroup and `tau|_(K_tau)` is a conjugation-invariant scalar
character.  This proves phase safety, but the associated character face is
the state space of the twisted quotient and can contain finite-dimensional
states unrelated to `tau`.

There is an exact counterexample to any automatic soundness implication.
Let `tau_0` be a non-Connes-embeddable trace on `C*(G)`, and let `tau_reg` be
the regular trace.  The set `T_CE` of Connes-embeddable traces on a separable
unital C-star algebra is weak-star closed, by diagonal selection of finite
moment microstates.  Since its complement is open, for all sufficiently small
`epsilon>0`,

```text
tau_epsilon=(1-epsilon)tau_0+epsilon tau_reg
```

still lies outside `T_fd`.

For `g!=1`, `tau_reg(g)=0`.  If `|tau_epsilon(g)|=1`, equality in the triangle
inequality for the convex combination would require
`|tau_reg(g)|=1`, a contradiction.  Therefore

```text
K_(tau_epsilon)={1}.
```

The subgroup-character face cut out by this kernel is the entire state space
of `C*(G)`, so it contains the trivial one-dimensional representation even
though `tau_epsilon` is non-Connes-embeddable.  Thus non-embeddability of one
trace does not automatically produce a subgroup-character gap; additional
compiler structure is indispensable.

For the stronger same-group example, use the symmetry basis of a separable
diffuse non-CE algebra to define `tau_0` on `*_(j>=1) C_2`.  Its GNS algebra
is the source algebra, but the free product is residually finite, so its
regular trace is CE.  The same mixture has trivial projective kernel and
remains non-CE for small positive `epsilon`.

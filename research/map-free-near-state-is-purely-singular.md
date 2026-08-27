---
rg: 2
id: map-free-near-state-is-purely-singular
kind: claim
title: Essential freeness forces every invariant near-state to be purely singular for a minimally almost periodic group
distinct_from:
  normal-state-free-near-representation-forces-factorization: that treats a wholly normal state and derives factorization for any group; this allows an arbitrary state, decomposes it into normal and singular parts, and uses minimal almost periodicity plus freeness to prove the normal part has zero mass.
  near-representation-amenability-dichotomy: that asks for a Kazhdan rigidity conclusion from an arbitrary amenable near representation; this needs no property T and proves only elimination of the normal component.
---

Let `G` be a nontrivial minimally almost periodic group.  Let `phi` be a state
on `B(H)` and `pi:G -> U(H)` a `phi`-near representation in the
Kahl--Schneider state sense.  If

```text
phi(pi(g))=0                         for every g != 1,    (MPS1)
```

then `phi` is purely singular: its normal part is zero.

The mechanism has two steps.  First, invariance and zero near-defect pass to
the normal/singular Lebesgue components of `phi`.  The normal component is
represented by a trace-class density `D`; its positive eigenspaces are finite
dimensional and invariant, and the near defect vanishes on the support of
`D`.  Minimal almost periodicity therefore makes `pi` trivial on the entire
normal support.

Second, if the normal mass were `alpha>0`, its contribution to the character
would equal the constant `alpha` on every group element.  The remaining
normalized singular character would consequently have one fixed negative
value `-alpha/(1-alpha)` on every nonidentity element.  Positive definiteness
on arbitrarily large finite subsets forbids such a negative constant: the
all-ones eigenvalue of the resulting Gram matrix is
`1+(m-1)c`, which becomes negative for large `m`.  Hence `alpha=0`.

Thus a minimally almost periodic group's hyperlinear near-representation
witness, when it exists, cannot hide even a small normal summand.  All of its
mass is genuinely singular/finitely additive.

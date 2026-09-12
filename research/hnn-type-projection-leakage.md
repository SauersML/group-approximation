---
rg: 2
id: hnn-type-projection-leakage
kind: claim
title: An HNN router preserves a finite type exactly when its edge algebra carries that type
distinct_from:
  regular-trace-blocks-exact-local-predicate-return: that rules out deleting a forbidden selector atom by a universal trace identity; this computes the canonical trace leakage of an arbitrary base projection under one HNN stable letter.
  trace-conditioned-reverse-kleene-collapse: that permits canonical moment side conditions; this shows that those moments generally force positive type leakage rather than type preservation.
---

Let `K` be a group, let `H,H'<=K`, let `theta:H->H'` be an isomorphism, and
put

```text
Gamma=<K,t | t h t^(-1)=theta(h), h in H>.
```

Let `tau` be the canonical trace of `Gamma`, let `E_H:C[K]->C[H]` delete all
coefficients outside `H`, and let `p in C[K]` be a projection.  Then

```text
tau(t p t^(-1) p)=tau(theta(E_H(p)) p),                 (HTL1)

||t p t^(-1)-p||_2^2
 =2[tau(p)-tau(theta(E_H(p))p)].                        (HTL2)
```

In particular

```text
t p t^(-1)=p
 iff p in C[H] and theta(p)=p.                          (HTL3)
```

Thus a central isotypic projection of a finite constant packet cannot be
kept by an HNN router merely by requiring a regular character profile.  The
covariance edge itself must carry that group-algebra projection and return
it under `theta`.

For the free-product case `H={1}`, if `s=tau(p)`, then

```text
||t p t^(-1)-p||_2^2=2s(1-s).                          (HTL4)
```

So every nontrivial finite type has a fixed positive canonical leakage.

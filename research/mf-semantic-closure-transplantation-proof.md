---
rg: 2
id: mf-semantic-closure-transplantation-proof
kind: route
title: Identify the intersections of kernels under the natural Hom bijection
target: mf-semantic-closure-transplantation
requires:
  - mf-camouflage-surgery
  - mf-relation-closure
---

Every MF-target map from `C_d(Q)` is uniquely `f*pi_Q` for an MF-target map
`f` from `Q`.  Such a composite kills `N` exactly when `f` kills `pi_Q(N)`.
Intersecting their kernels gives `(S1)`, and `N={1}` gives `(S2)`.

A countable quotient `G/N` is MF exactly when `cl_MF^G(N)=N`.  If
`Q/pi_Q(N)` is MF, then `(S1)` becomes

```text
cl_MF^(C_d(Q))(N)=pi_Q^(-1)(pi_Q(N))
                         =N ker(pi_Q).
```

This equals `N` exactly when `ker(pi_Q)<=N`, equivalently when `d in N`.
The converse follows from the same equality: if the left side is `N`, then
`ker(pi_Q)<=N`, and applying `pi_Q` to `(S1)` shows that
`cl_MF^Q(pi_Q(N))=pi_Q(N)`.  This proves `(S3)`.

When `Q` is MF, `(S2)` and `ker(pi_Q)=normalClosure(d)` give the final
assertion.

If `N` is MF-closed, then `(S1)` forces `ker(pi_Q)<=N`; hence
`N=pi_Q^(-1)(pi_Q(N))`, and `pi_Q(N)` is MF-closed.  Conversely `(S1)` sends
the preimage of every MF-closed normal subgroup of `Q` to itself.  Image and
preimage are inverse on subgroups containing `ker(pi_Q)`, which proves the
order isomorphism and therefore the quotient-lattice statement.

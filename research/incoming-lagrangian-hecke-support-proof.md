---
rg: 2
id: incoming-lagrangian-hecke-support-proof
kind: route
title: Track Pauli and actor coordinates in the refined semidirect normal form
target: incoming-lagrangian-refinement-preserves-hecke-actor-support
requires:
  - fano-semidir-bridges-are-wrong-subgroup-or-gauged
  - heisenberg-subgroup-cuts-are-affine-stabilizer-flats
---

Write the affine stabilizer idempotent as

```text
p_k=|W_k|^(-1) sum_(a in W_k) mu_k(a)^(-1)a
```

and the signed Hecke idempotent as

```text
Q_k=|H_k|^(-1) sum_(h in H_k) lambda_k(h)^(-1)h.
```

The semidirect product has unique normal form `ah`, with `a in A` and
`h in K`.  Consequently

```text
p_kQ_k=(|W_k||H_k|)^(-1)
        sum_(a in W_k,h in H_k)
        mu_k(a)^(-1)lambda_k(h)^(-1) ah.               (1)
```

Every coefficient in `(1)` is nonzero and distinct normal forms cannot
cancel.  Projection compatibility `p_kQ_k=Q_kp_k` says precisely that the
affine stabilizer data are `H_k`-invariant; it does not remove any `h` from
the expansion.  This proves `supp_K(F_k)=H_k`.

For `b in A`, normality of `A` gives

```text
b(ah)b^(-1)=a' h
```

for some `a' in A`.  Thus conjugation by a Pauli element fixes the actor
coordinate term by term.  Equivalently it can insert the Pauli commutator
cocycle attached to `h`, but cannot conjugate the subgroup `H_k` inside
`K`.  This proves `(ILR3)`.

The explicit computation `(ILR4)` is the first Singer calculation in the
finite-semidir bridge dichotomy.  Since source and range Grams of a
compressed group unitary are full exactly when it conjugates the source
projection to the range projection, `(ILR2)--(ILR4)` exclude `(ILR5)` for
every dual Pauli translation.  Replacing the incoming Lagrangian by its
dual only replaces `W_k` and `mu_k` in `(1)` and leaves the actor-coordinate
argument unchanged.


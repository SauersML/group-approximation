---
rg: 2
id: simple-product-completions-block-regular-tree-actions
kind: claim
title: A residually finite group whose profinite completion has an open product of simple groups of unbounded order acts faithfully on no regular rooted tree
distinct_from:
  regular-tree-torsion-orders-have-primes-at-most-degree: that bounds the primes in torsion orders of Aut(T_d); this is a torsion-free obstruction read off the profinite completion, and it applies to groups whose torsion primes are bounded or absent.
  cycle-transposition-lef-group-has-no-regular-tree-action: that is one explicit two-generated group, excluded through its prime-order torsion; this excludes every residually finite group with an open simple-product subgroup of the stated kind in its completion.
  simple-monomial-completions-kill-the-tree-action-kernel: that is about completions of group algebras along a wreath recursion; this is about the profinite completion of a group and its faithful actions on T_d.
---

**ESTABLISHED.** Let `Γ` be a residually finite group and `Γ^` its profinite
completion. Suppose some open subgroup `U` of `Γ^` is isomorphic, as a
topological group, to

```text
prod_(i in I) S_i        (product topology),                         (SP1)
```

where every `S_i` is a nonabelian finite simple group and, for every `m`, only
finitely many `i` satisfy `|S_i| <= m`. This holds, for example, when `I` is
infinite and the `S_i` are pairwise non-isomorphic.

Then `Γ` embeds in `Aut(T_d)` for no `d >= 2`. Moreover, for every `d` the
group `Γ` fails condition (N1) of
`every-fp-rf-group-embeds-in-fp-self-similar-group`, and so it is a subgroup of
no self-similar group.

**Sharper form proved.** For every `m`, `Γ` has a finite-index subgroup `Δ_m`
that is infinite and has no nontrivial finite quotient all of whose composition
factors have order at most `m`.

**What it changes.** The only known mechanism for failing (N1) was torsion of
unbounded prime order, and every known source of it is killed for finitely
presented residually finite groups (see `fp-rf-group-with-unbounded-prime-torsion`).
This claim gives a second mechanism that does not mention torsion. It feeds the
route `fp-rf-tree-obstruction-via-simple-product-completion`, and its open
prerequisite is `fp-rf-group-with-simple-product-completion`.

DERIVATION
simple-product-completions-block-regular-tree-actions-proof

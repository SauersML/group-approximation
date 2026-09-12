---
rg: 2
id: strict-rule-pairs-pass-to-product-alphabets
kind: claim
title: Strict rule pairs over an alphabet A give strict rule pairs over A x B with the same tables
distinct_from:
  surjunctivity-is-axiomatized-by-rectangle-clauses: that fixes the alphabet inside each certificate; this transports strict data from A to A x B without changing the tables.
  stable-finiteness-reduces-to-prime-field: that moves a linear stable-finiteness failure between fields of one characteristic; this moves arbitrary nonlinear strict data from A to A x B for every finite B.
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
---

**ESTABLISHED** by `strict-rule-pairs-product-alphabets-proof`.

Let `(mu, nu)` be strict for tables `(T_f, T_r)` over `A`, and let `B` be finite and nonempty.
The rules

    mu'( ((a_m, b_m))_m ) = ( mu((a_m)_m), b_1 ),    nu'( ((a_s, b_s))_s ) = ( nu((a_s)_s), b_1 )

are strict for the same tables over `A x B`.

**Consequences.**
- **Alphabet sizes.** The sizes admitting strict rules for fixed tables are closed under
  multiplication by every positive integer, and never include `1`.
- **Groups.** A group that is not `A`-surjunctive is not `(A x B)`-surjunctive, with the same
  memories. So surjunctivity over `kl` symbols implies surjunctivity over `k` symbols.
- **Reduction to factorial sizes.** Gottschalk's conjecture holds over every alphabet iff it holds
  over alphabets of size `n!` for all `n`.

The other direction is not covered. Strictness is not shown to pass to arbitrary larger alphabets,
nor to descend to two symbols (`surjunctivity-failure-descends-to-binary-alphabet`).

Proof: Section 2 of the artifact.

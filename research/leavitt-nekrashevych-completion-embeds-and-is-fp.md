---
rg: 2
id: leavitt-nekrashevych-completion-embeds-and-is-fp
kind: claim
title: A matrix recursion psi on a finitely presented algebra B gives a finitely presented completion O_psi containing B exactly when psi is injective
distinct_from:
  algebra-boone-higman-conjecture: that asks for finitely presented simple envelopes of every decidable algebra; this is the embedding and finite-presentation half of one candidate envelope construction, with no simplicity statement.
  fp-simple-algebras-have-solvable-word-problem: that is the necessary condition for simple envelopes; this is a construction lemma about a specific finitely presented overalgebra.
---

**ESTABLISHED** through `leavitt-nekrashevych-completion-embedding-proof`.

**Setting.** Let `K` be a field, `d >= 2`, and `B` a unital `K`-algebra with a
unital `K`-algebra homomorphism (a *matrix recursion*)

```text
psi : B -> M_d(B),   b |-> (psi(b)_{ij}).
```

Let `L_d = K< s_1..s_d, t_1..t_d | t_i s_j = delta_{ij},  sum_i s_i t_i = 1 >` be
the Leavitt algebra of type `(1,d)`. The **Leavitt--Nekrashevych completion** is
the unital `K`-algebra

```text
O_psi = ( B *_K L_d ) / ( b = sum_{i,j} s_i psi(b)_{ij} t_j   for all b in B ).
```

**Claim.**

1. **Finite presentation.** If `B = K<g_1..g_m | R>` with `R` finite, then
   `O_psi` is presented by the generators `g_k, s_i, t_i`, the relators `R`, the
   `d^2 + 1` Leavitt relators, and the `m` covariance relators
   `g_k = sum_{ij} s_i psi(g_k)_{ij} t_j`. In particular `O_psi` is finitely
   presented.
2. **Embedding.** The canonical map `B -> O_psi` is injective if and only if `psi`
   is injective.

Both parts are elementary. `O_psi` is a special case of the algebraic
Cuntz--Pimsner rings of Carlsen--Ortega (arXiv:0810.3254, Proc. LMS 103 (2011);
abstract checked, theorem statements not re-read), for the bimodule `B^d` with
left action through `psi`. The proof route here is self-contained and uses none
of their results. No novelty is claimed for part 2; part 1 is immediate.

This settles the first open question in Attempt 5 of
`algebra-boone-higman-conjecture`: injectivity of `B -> O_psi`.

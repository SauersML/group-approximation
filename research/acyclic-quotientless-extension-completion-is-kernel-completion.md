---
rg: 2
id: acyclic-quotientless-extension-completion-is-kernel-completion
kind: claim
title: Over an acyclic perfect quotient without finite quotients, an extension has exactly the finite quotients of its kernel
distinct_from:
  rips-kernel-target-iff-hyperbolic-nonrf: that equates two existence problems about hyperbolic groups; this is an algebraic statement about one fixed extension, with no hyperbolicity, saying which finite quotients the extension has.
  finite-central-extension-rf-iff-virtually-splits: that decides residual finiteness of a finite central extension by virtual splitting; this treats an arbitrary finitely generated kernel over a quotient with no finite quotients, where every finite image of the kernel splits off as a direct factor.
artifacts:
  - research/artifacts/hyperbolic-no-finite-quotient-leavitt-cover-2026-09-12.md
---

**ESTABLISHED.** Let

```text
1 -> N -> G -> Q -> 1
```

be exact with `N` finitely generated and `Q` without nontrivial finite
quotient. Call `K <= N` *admissible* if `K` is normal in `G` and of finite
index in `N`.

Assume first that `Q` is perfect and `H_2(Q; Z) = 0`.

1. **Splitting.** For every admissible `K`, `G/K = S x N/K` internally, with
   `S ≅ Q`.
2. **Finite quotients.** The finite quotients of `G` are exactly the groups
   `N/K` with `K` admissible. Every finite-index normal subgroup of `N`
   contains an admissible one.
3. **Completions.** The inclusion induces an isomorphism of profinite
   completions `N^ -> G^`, and `R_f(G) ∩ N = R_f(N)`.
4. **Quotient-freeness.** `G` has a nontrivial finite quotient iff `N` has one.

Now drop perfectness and the Schur multiplier hypothesis.

5. **Circularity.** If `G` has no nontrivial finite quotient, every finite
   quotient of `N` is abelian. If moreover `N` has finite abelianization (for
   instance `N` is Kazhdan), then `[N,N]` has finite index in `N` and has no
   nontrivial finite quotient.

The hypothesis `H_2(Q; Z) = 0` in items 1 and 4 cannot be dropped. If `Q` is
perfect and `H_2(Q; Z)` has a nontrivial finite quotient `A`, the matching
perfect central extension `1 -> A -> G -> Q -> 1` has no nontrivial finite
quotient, while its kernel `A` does.

Proof in `acyclic-quotientless-extension-completion-proof`. Elementary; no
novelty claimed. Not Lean-verified and not independently reviewed.

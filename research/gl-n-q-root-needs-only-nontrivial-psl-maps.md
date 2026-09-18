---
rg: 2
id: gl-n-q-root-needs-only-nontrivial-psl-maps
kind: claim
title: PSL_n(Q) is simple and cofinal with GL_n(Q), so the root needs only a nontrivial homomorphism of PSL_n(Q) into an embeddable group, for infinitely many n
distinct_from:
  gl-n-q-targets-are-cofinal-in-n: that compares GL_n(Q), SL_n(Q), PGL_n(Q) under embedding; this adds that PSL_n(Q) (= SL_n(Q) for odd n) is simple, so faithfulness of a homomorphism or action is automatic once it is nontrivial.
  gl-n-q-embeds-in-fp-simple-group: that is the embedding target; this is an elementary reduction of it to nontrivial homomorphisms.
  psl-n-q-maps-nontrivially-to-fp-simple-groups: that is the open target in the nontrivial-homomorphism form; this is the established equivalence behind it.
---

**ESTABLISHED** by `gl-n-q-root-needs-only-nontrivial-psl-maps-proof`
(elementary; not independently reviewed; no novelty claimed).

## Statement

1. **Simplicity.** For every `n >= 2`, `PSL_n(Q) = SL_n(Q)/{±I or 1}` is simple.
   For odd `n`, the centre `{λI : λ^n = 1}` of `SL_n(Q)` is trivial, so
   `SL_n(Q) = PSL_n(Q)` is simple.
2. **Cofinality.** `PSL_n(Q) <= PGL_n(Q) <= GL_(n^2)(Q)`, and
   `GL_n(Q) <= SL_(n+1)(Q) <= PSL_k(Q)` for every `k >= n+2` (block embedding
   `g ↦ diag(g, det(g)^-1, 1, ..., 1)`; a block matrix with a trailing `1` is
   never a nontrivial scalar).
3. **Equivalence.** Let `P` be a property inherited by subgroups, e.g.
   "embeds in a finitely presented simple group" or "lies in `B_A`". The
   following are equivalent:
   - (a) `P(GL_n(Q))` for every `n >= 2`;
   - (b) for infinitely many `n` there is a group `X` with `P(X)` and a
     **nontrivial** homomorphism `PSL_n(Q) -> X`;
   - (c) for infinitely many odd `m` there is a group `X` with `P(X)` and a
     nontrivial homomorphism `SL_m(Q) -> X`.

   With `P` = "embeds in a finitely presented simple group", (a) is the root
   `gl-n-q-embeds-in-fp-simple-group`.

## What this buys a construction

- **Faithfulness is free.** Any nontrivial homomorphism from `PSL_n(Q)` is
  injective. So a construction only has to make `PSL_n(Q)` (for one of
  infinitely many `n`) act *nontrivially* inside a host. In particular, a
  construction may pass to quotients: if `PSL_n(Q) <= Γ` and `N` is a normal
  subgroup of `Γ` not containing `PSL_n(Q)`, then `PSL_n(Q)` embeds in `Γ/N`.
- **Kernel removal needs no disjointness hypothesis.** In the kernel-removal
  statement of `permutational-host-forms-agree-for-countable-inputs` (an actor
  `G` of type `[A_2]` with kernel `K`, input `H <= G`, `H ∩ K = 1`), the
  condition `H ∩ K = 1` holds for `H = PSL_n(Q)` as soon as `H` acts
  nontrivially. The remaining condition there, finite presentation of `G/K`,
  is untouched.
- **Monolithic quotients.** If `PSL_n(Q) <= Γ`, Zorn's lemma gives a normal
  subgroup `M` of `Γ` maximal with `M ∩ PSL_n(Q) = 1` (a union of a chain of
  such subgroups still meets the simple group `PSL_n(Q)` trivially). Then
  `PSL_n(Q)` embeds in `Γ/M`, and every nontrivial normal subgroup of `Γ/M`
  contains it, so `Γ/M` has a unique minimal normal subgroup, the normal
  closure of `PSL_n(Q)`. `Γ/M` need not be finitely presented.

None of this touches the hard part: producing a finitely presented host at all.

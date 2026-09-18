---
rg: 2
id: gl-n-q-targets-are-cofinal-in-n
kind: claim
title: GL_n(Q), SL_n(Q) and PGL_n(Q) are mutually cofinal under embedding, so the root may be proved for any infinite set of n and any of the three families
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the embedding target itself; this is an elementary reduction between its instances.
  permutational-host-forms-agree-for-countable-inputs: that gives equivalent membership tests for the class B_A; this compares the inputs GL_n(Q), SL_n(Q), PGL_n(Q) for different n.
---

**ESTABLISHED** by `gl-n-q-targets-are-cofinal-in-n-proof` (elementary; not
independently reviewed; no novelty claimed).

## Statement

For `n >= 2` there are injective homomorphisms

- `GL_n(Q) -> GL_(n+1)(Q)`, `g ↦ diag(g, 1)`;
- `GL_n(Q) -> SL_(n+1)(Q)`, `g ↦ diag(g, det(g)^-1)`;
- `GL_n(Q) -> PGL_(n+1)(Q)`, `g ↦ [diag(g, 1)]`;
- `PGL_n(Q) -> GL_(n^2)(Q)`, `[g] ↦ (X ↦ g X g^-1)` on `M_n(Q) ≅ Q^(n^2)`;

and `SL_n(Q) <= GL_n(Q)`.

Let `P` be a property of groups inherited by subgroups. Two examples are
"embeds in a finitely presented simple group" and "lies in `B_A`"
(`permutational-host-forms-agree-for-countable-inputs`). Then the following
are equivalent:

1. `P(GL_n(Q))` for every `n >= 2`;
2. `P(GL_n(Q))` for infinitely many `n`;
3. `P(SL_n(Q))` for infinitely many `n`;
4. `P(PGL_n(Q))` for infinitely many `n`.

Also `P(GL_(n+1)(Q))` implies `P(GL_n(Q))`. So a construction may pick `n` as
large as it likes, and may work with `SL_n(Q)`, or with `PGL_n(Q)` and its
2-transitive action on `P^(n-1)(Q)`, at no cost.

For `P = "lies in B_A"`, `B_A` is also closed under finite-index overgroups,
finite direct products and free products
(`boone-higman-type-a-class-closed-under-finite-extensions`). So it suffices to
treat any finite-index subgroup of `GL_n(Q)`, for example the subgroup of
positive-determinant matrices.

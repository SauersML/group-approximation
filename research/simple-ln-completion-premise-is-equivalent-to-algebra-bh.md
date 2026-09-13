---
rg: 2
id: simple-ln-completion-premise-is-equivalent-to-algebra-bh
kind: claim
title: The simple Leavitt--Nekrashevych completion premise is equivalent to algebra Boone--Higman, which splits into an algebra Clapham theorem and Boone--Higman for finitely presented decidable algebras
distinct_from:
  algebra-boone-higman-conjecture: that is the root statement; this proves it equivalent to the completion premise, and equivalent to its Clapham half together with its finitely presented half.
  decidable-algebras-embed-in-simple-ln-completions: that is the completion premise asking for a psi-minimal aperiodic completion over a finitely presented base; this shows the premise is exactly as hard as the root, through the trivial recursion on a simple base.
  decidable-algebras-embed-in-decidable-fp-algebras: that is the algebra Clapham half, still OPEN; this states only that the root is equivalent to it together with Boone--Higman for finitely presented algebras with solvable word problem.
---

**ESTABLISHED** through `simple-ln-completion-premise-equivalence-proof`.

Let `K` be a computable field, `d >= 2`, and all algebras unital `K`-algebras.
Notation as in `leavitt-nekrashevych-completion-embeds-and-is-fp` and
`leavitt-nekrashevych-completion-simplicity-criterion`.

**Claim.**

1. **Completion normal form.** For a finitely generated algebra `A`, these are
   equivalent:
   - (a) `A` embeds in a finitely presented simple algebra;
   - (b) `A` embeds in `O_psi` for some finitely presented `B` and injective
     recursion `psi : B -> M_d(B)` with `B` psi-minimal and `(B, psi)` aperiodic.

   In (a) ⇒ (b) one can take `B = S` the simple envelope and `psi(b) = b I_d`.
   Then `O_psi ≅ S ⊗_K L_d`. So `decidable-algebras-embed-in-simple-ln-completions`
   holds iff `algebra-boone-higman-conjecture` holds.
2. **Clapham split.** `algebra-boone-higman-conjecture` holds iff both of the
   following hold:
   - (C) every finitely generated algebra with solvable word problem embeds in a
     finitely presented algebra with solvable word problem
     (`decidable-algebras-embed-in-decidable-fp-algebras`);
   - (F) every finitely presented algebra with solvable word problem embeds in a
     finitely presented simple algebra.

**Reading.** The completion premise is a normal form for the root, not a
weakening. Any proof of it must already produce simple envelopes. Attempt 1 of
the premise ("trivial recursions die") is the special case where the base is not
simple. The root splits exactly as group Boone--Higman does through Clapham's
theorem (`clapham-fp-embedding-preserves-word-problem`). The algebra form of that
theorem is not source-checked in this graph.

No novelty is claimed. Both parts are elementary.

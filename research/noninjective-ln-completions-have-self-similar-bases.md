---
rg: 2
id: noninjective-ln-completions-have-self-similar-bases
kind: claim
title: For any matrix recursion psi on a finitely presented algebra B, injective or not, O_psi(B) is finitely presented and equals the completion of the self-similar quotient B/J, J the union of the kernels of the iterates of psi
distinct_from:
  leavitt-nekrashevych-completion-embeds-and-is-fp: that proves finite presentation and that B -> O_psi is injective iff psi is; this identifies the kernel when psi is not injective, as the self-similar quotient, and shows O_psi(B) is the completion of that quotient.
  ln-completion-word-problem-reduces-to-base-algebra: that bounds the word problem of O_psi by that of B for INJECTIVE psi, which fences completions over free bases with injective recursions; this shows that for non-injective psi the base of the completion is B/J, which need not be finitely presented, so that fence does not apply.
  decidable-algebras-embed-in-simple-ln-completions: that premise asks for B finitely presented and psi injective; the weaker premise decidable-algebras-embed-in-simple-self-similar-completions allows a free B and any psi, and still implies algebra Boone--Higman.
---

**ESTABLISHED** through `ln-completions-of-noninjective-recursions-proof` (lane proof, bh-algebra,
elementary, not reviewed).

**Setting.** `K` a field, `B = K<g_1..g_m | R>` finitely presented (for example free), `d >= 2`, and
`ψ : B -> M_d(B)` any unital homomorphism. Let `ψ_1 = ψ`, and let `ψ_(N+1)` be `ψ` applied entrywise to
`ψ_N`, so `ψ_N : B -> M_(d^N)(B)`. Put `J = ∪_N ker ψ_N`, the *self-similar kernel*.

**Claim.**
1. `J` is a two-sided ideal and is ψ-saturated. So `ψ` induces an *injective* recursion
   `ψ̄ : B/J -> M_d(B/J)`.
2. The kernel of `B -> O_ψ(B)` is exactly `J`, and `O_ψ(B) ≅ O_(ψ̄)(B/J)`.
3. `O_ψ(B)` is finitely presented, by the generators of `B`, the Leavitt letters, the relators `R`, the
   Leavitt relators, and one covariance relator per generator.
4. If `B/J` is ψ̄-minimal and `(B/J, ψ̄)` is aperiodic, then `O_ψ(B)` is a finitely presented simple
   algebra containing `B/J`.

**Why it matters.** `ln-completion-word-problem-reduces-to-base-algebra`, applied to `(B/J, ψ̄)`,
reduces the word problem of `O_ψ(B)` to deciding membership in `J`. For non-injective recursions on
a free algebra, `J` is the relation ideal of a *self-similar algebra* in the sense of automaton
algebras. Nothing in the repository bounds its complexity uniformly: the fence of that node (its
parts 3 and 4, and Attempt 3 of `decidable-algebras-embed-in-simple-ln-completions`) assumes `ψ`
injective. So completions of self-similar quotients of free algebras are not yet excluded as envelopes
for the monomial benchmark `K<x,y>/(x y^n x : n ∈ X)`. The open premise is
`decidable-algebras-embed-in-simple-self-similar-completions`.

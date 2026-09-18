---
rg: 2
id: algebraic-closure-makes-rational-k1-classes-divisible
kind: claim
title: If the algebraic closure of Q embeds unitally in R, the image of Q^x in K_1(R) lies in a divisible subgroup, so the stable scalar clause of the widened ring gate needs a divisible subgroup of infinite rank in K_1(R); a reduced K_1 forces every widened-gate host into loophole (i)
distinct_from:
  algebraic-closure-kills-rational-steinberg-symbols: that shows Q̄ ⊆ R kills K_2(Q) in every St_N(R); this shows the same hypothesis makes the rational K_1 classes infinitely divisible, which constrains the K_1 clause.
  ring-gate-k1-clause-is-unstable: that separates the stable and unstable scalar clauses; this shows that, for widened-gate rings with reduced K_1, only the unstable clause can hold.
  leavitt-tuples-make-the-scalar-clauses-agree: that closes loophole (i) for Leavitt-tuple rings; this shows which remaining rings must use it.
---

**ESTABLISHED** through `algebraic-closure-makes-rational-k1-classes-divisible-proof`. Lane proof, elementary, not
independently reviewed. No priority is claimed.

**Setting.** `R` is a unital ring and `Q̄ -> R` a unital ring homomorphism. `ι : Q^x -> K_1(R)` is induced by `Q ⊆ Q̄`,
and `ῑ : Q̄^x -> K_1(R)`.

**Statement.**
1. **Divisibility.** `ῑ(Q̄^x)` is a divisible subgroup of `K_1(R)`, and it contains `ι(Q^x)`. In particular every
   `ι(λ)` is divisible by every integer in `K_1(R)`.
2. **Reduced `K_1` kills the stable clause.** If `K_1(R)` has no nonzero divisible subgroup, for example if it is
   finitely generated, then `ῑ = 0`. So `ker ι = Q^x`, which is not finitely generated.
3. **What the stable clause needs.** If `ker ι` is finitely generated, then `K_1(R)` contains the divisible group
   `ῑ(Q̄^x)`, whose rational part `ι(Q^x) ≅ Q^x / ker ι` is not finitely generated.
4. **Consequence for the widened gate.** A widened-gate ring whose `K_1` is reduced can meet the scalar condition
   only through loophole (i) of `frame-designs-for-the-ring-gate-are-bracketed`: `Λ_N(R)` finitely generated while
   every rational scalar dies stably. By `leavitt-tuples-make-the-scalar-clauses-agree`, it must then contain no
   Leavitt tuple.
   - Example: `R_L` has `K_1(R_L) = Z`, so `ker ι = Q^x`. It also contains a Leavitt pair, so `Λ_N(R_L) = Q^x`, and it
     fails both clauses.

## Reading for the construction target

A candidate host for loophole (i) needs:
- `Q̄ ⊆ R`;
- no Leavitt tuple, for example `[1]` of infinite order;
- one of two things:
  - a divisible part of infinite rank in `K_1(R)` containing the rational scalars (the stable route), or
  - reduced `K_1(R)` together with `K_1`-instability at some rank `N`: the scalars are stably trivial by item 2, yet
    `λ I_N ∉ E_N(R)` for all `λ` outside a finitely generated group.
The second option asks that `GL_N(R)/E_N(R) -> K_1(R)` be far from injective on scalars at a fixed rank. That is a
large unstable `K_1` defect.

---
rg: 2
id: wreath-candidate-embeds-in-finitary-permutation-extension
kind: claim
title: The wreath candidate embeds in a finitary permutation extension of its actor, whose factor is a crossed product of the hyperfinite factor
distinct_from:
  hyperlinear-wreath-model: that asks for microstates of `W` directly; this exhibits a larger nonsofic group `Sigma_2` whose hyperlinearity would suffice and whose von Neumann algebra is `R rtimes G`, so the base is a factor rather than a Cartan algebra.
  positive-core-bernoulli-ce: that supplies microstates for a proper subgroup of `W`; this goes the other way, embedding `W` into a larger group with a more rigid base algebra.
  invariant-cartan-completion: that asks to complete a Cartan-type structure in an abstract embedding; here the abelian lamp algebra is replaced by the hyperfinite factor before any embedding is sought.
  pair-flips-in-finitary-symmetric-group-add-no-envelope: that proves the visible pair-flip subalgebra is still exactly the old abelian lamp algebra and gains no Cartan envelope; this route asks for a genuinely non-Cartan embedding of the whole finitary symmetric factor, so it neither contradicts nor bypasses that fence for free.
artifacts:
  - notes/HYPERLINEAR_NONSOFIC_ATTEMPT_2026-08-26.md
---

**ESTABLISHED.**  Let `G` act on a countable set `X`, let `Y = X x {0,1}`
with `G` acting on the first coordinate, and let

```text
Sigma_2(X) = Sym_fin(Y) rtimes G,
```

the semidirect product for the conjugation action of `G` through
`G -> Sym(Y)`.  Then:

1. The generalized wreath product `C_2 wr_X G = (directSum_X C_2) rtimes G`
   embeds in `Sigma_2(X)`, the lamp at `x` going to the transposition
   `((x,0) (x,1))`.
2. `Sym_fin(Y)` is countable, locally finite and ICC, so
   `L(Sym_fin(Y)) ~= R` (the hyperfinite `II_1` factor) and
   `L(Sigma_2(X)) ~= R rtimes_alpha G` for the action `alpha` induced by
   `G curvearrowright Y`.
3. If `X = G/Gamma` is the Kun--Thom coset space, then `Sigma_2(X)` is not
   sofic (it contains the nonsofic wreath candidate `W`), and if it is
   hyperlinear then `W` is hyperlinear and Pestov's Question 3.4 is answered
   by separation.
4. If every nonidentity element of `G` moves infinitely many points of `Y`,
   then every `alpha_g`, `g != 1`, is an outer automorphism of `R`.

Consequently the separation question for the Kun--Thom candidate is implied
by the following Connes-embedding question with a **factor** base:

```text
Is R rtimes_alpha G Connes embeddable, for the explicit action alpha of the
residually finite Kazhdan group G = EL_r(R) rtimes SL_d(Z) on
R = L(Sym_fin(G/Gamma x {0,1})) ?
```

By `finitary-extension-ce-iff-action-lifts-to-normalizer` this is exactly a
lifting problem for `alpha` through `N_(R^omega)(R) -> Aut(R)`, with no
trace bookkeeping when item 4 applies.  The reformulation removes the
abelian lamp algebra -- the object on which every collapse theorem of this
subtree (`diagonal-normalizer-rigidity`, `block-monomial-coordinate-collapse`,
`finite-quotient-blindness`) operates -- and replaces it by a factor whose
embeddings into `R^omega` are all conjugate.  It is a reduction only in one
direction: hyperlinearity of `Sigma_2` implies that of `W`, and the converse
is not claimed.

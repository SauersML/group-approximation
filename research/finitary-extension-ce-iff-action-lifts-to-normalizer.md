---
rg: 2
id: finitary-extension-ce-iff-action-lifts-to-normalizer
kind: claim
title: A crossed product of the hyperfinite factor is Connes embeddable iff the action lifts to the normalizer of R in its ultrapower
distinct_from:
  hyperlinear-near-representation-criterion: that is an operator-norm, finitely-additive-charge criterion for hyperlinearity of a group; this is an intrinsic `II_1` lifting criterion for crossed products of the hyperfinite factor, with the trace condition made explicit and shown to be automatic for outer actions.
  invariant-cartan-completion: that concerns recovering a Cartan subalgebra normalized by the actor inside an abstract embedding; here the base is a factor, all of whose embeddings into `R^omega` are conjugate, so no completion step exists.
  wreath-candidate-embeds-in-finitary-permutation-extension: that produces the specific action `alpha` of the Kun--Thom actor on `R`; this is the general criterion it is fed into.
artifacts:
  - notes/HYPERLINEAR_NONSOFIC_ATTEMPT_2026-08-26.md
---

**ESTABLISHED.**  Let `R` be the hyperfinite `II_1` factor, `omega` a free
ultrafilter on `N`, `R <= R^omega` the diagonal embedding, and
`N = N_(R^omega)(R) = {u in U(R^omega) : u R u^* = R}`.  Restriction gives a
surjective homomorphism

```text
Ad: N -> Aut(R),     kernel U(R' cap R^omega),
```

surjective because every automorphism of `R` is approximately inner
(Connes).  Let `alpha: G -> Aut(R)` be an action of a countable group.  The
following are equivalent.

1. `R rtimes_alpha G` embeds trace-preservingly into `R^omega` (is Connes
   embeddable);
2. there is a homomorphism `u: G -> N` with `Ad(u_g)|_R = alpha_g` and
   `tau(x u_g) = 0` for all `x in R`, `g != 1`.

If every `alpha_g`, `g != 1`, is outer, the trace condition in (2) is
automatic, so (1) is equivalent to the bare lifting statement: the pullback
of the extension `1 -> U(R' cap R^omega) -> N -> Aut(R) -> 1` along `alpha`
splits.

Two calibrations show the criterion is sharp.  For the trivial action of an
arbitrary countable `G`, the bare lift `u = 1` always exists, while the trace
condition asks for `G <= U(R' cap R^omega)` with vanishing traces, which is
hyperlinearity of `G` (the relative commutant contains a copy of `R^omega`);
so the trace condition cannot be dropped for non-outer actions.  For an
action of a free group the lift always exists (choose the generators freely
in `N`), recovering the known Connes embeddability of `R rtimes F_n`.

Applied through `wreath-candidate-embeds-in-finitary-permutation-extension`,
the Kun--Thom separation is implied by a lifting statement for one explicit
action of the residually finite Kazhdan actor on `R`, with the lamps
entirely absorbed into `R`.

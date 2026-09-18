---
rg: 2
id: full-mf-radical-abelianized-cover-is-not-mf
kind: claim
title: The free abelianized cover of a nontrivial full-MF-radical group is not MF
distinct_from:
  free-abelianized-cover-reflects-mf: that is descent (D) for every presentation of every group; this is only its contrapositive for bases with FULL MF radical, where every corona homomorphism of the base is trivial and not merely non-injective.
  free-abelianized-cover-fd-radical-is-commutator: that computes the exact finite-dimensional radical of the same cover, a larger radical whose total collapse is compatible with MF; this asks for the operator-norm corona radical.
  abelianized-cover-commutator-is-finitely-generated-perfect: that is group theory of the commutator core; this is the analytic non-MF statement.
artifacts:
  - research/abelianized-cover-injective-corona-model-carries-nonzero-twist.md
  - research/implemented-corona-actions-of-countable-groups-are-unconstrained.md
---

**OPEN.**  Let `F` be free of finite rank, `R` normal in `F`, and suppose
`G = F/R != 1` has `Rad_MF(G) = G`.  Set `E = F/[R,R]` and `M = R/[R,R]`.
The claim is that `E` is not MF:

```text
every homomorphism rho : E -> U(prod M_(k_n) / (+) M_(k_n)) has nontrivial kernel.   (DF)
```

The route `property-t-free-seed-via-leavitt-abelianized-cover` uses only one
instance: the finite presentation that
`full-mf-radical-has-fp-cover-same-generators` gives over
`St_20(L_(F_2)(1,2))`.

`free-abelianized-cover-reflects-mf` implies `(DF)`.  The converse is not
claimed.

**Known structure.**

- A nontrivial full-MF-radical group is infinite, because finite groups are MF.
- For infinite `G`, the relation module `M` is a nontrivial `G`-module with no
  fixed vectors.  It embeds in `ZG^n` by the Lyndon sequence, and
  `(ZG^n)^G = 0`.  Moreover `M != 0`, since otherwise `R` is perfect, hence
  trivial, and then `G` is free, hence MF.
- So `[E,M]`, which is the image of `I_G M`, is a nontrivial normal subgroup
  of `E`.

## Attempts

- **Untwisting dichotomy (2026-09-18).**
  `abelianized-cover-injective-corona-model-carries-nonzero-twist` proves:
  - if a model `rho` has zero pushed class
    `rho_* xi in H^2(G; U(C*(rho(M))))`, then `rho` kills `[E,M] != 1`;
  - so an injective model of `E` must act nontrivially on the spectrum of
    `C*(rho(M))`, and it must carry a nonzero abelian twist class there.

  This does not close `(DF)`.  Nothing shows that a nonzero class cannot occur,
  and the nonabelian-coefficient form of the dichotomy is a tautological
  restatement of `rho([E,M]) = 1`.
- **Rigidity of the induced action is false as a principle (2026-09-18).**
  `implemented-corona-actions-of-countable-groups-are-unconstrained` realizes
  every nontrivial countable group, full MF radical or not, by a nontrivial
  action on a commutative subalgebra `C(X)` of a matrix corona.  The action is
  implemented by unitaries whose cocycle lies in the relative commutant.
  - Any proof of `(DF)` must therefore use the finer data of an actual model:
    the cocycle takes values in `U(C*(rho(M)))` itself, and it is the image of
    the relation module.
  - A counterexample must realize such a cocycle exactly with commuting
    conjugates.  The Bernoulli construction does not: its permutation
    holonomy lies only in the commutant.

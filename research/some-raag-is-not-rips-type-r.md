---
rg: 2
id: some-raag-is-not-rips-type-r
kind: claim
title: Some right-angled Artin group with its standard generating set is not of Rips type R
---

There is a finite simplicial graph `Γ` such that for arbitrarily large `r`
the Rips complex `R_r(A_Γ, V(Γ))` of the standard word metric is not
contractible.

This is the negative answer to Zaremsky Problem 4.5
(`zaremsky-4-05-raag-rips-complexes-contractible`). It is the negation of
`every-raag-is-rips-type-r`.

## Attempts

- 2026-09-13 (z4-05-raag-rips): no candidate yet. Any counterexample must have
  a connected, non-complete `Γ` containing a triangle, by the covered classes
  recorded in `every-raag-is-rips-type-r`. A non-contractible `R_r` needs a
  persistent sphere. Since `A_Γ` is coarsely contractible, the inclusions
  `R_r → R_{r'}` are eventually null-homotopic on compact pieces, so such a
  sphere must be born again at every scale rather than survive from a fixed
  scale. No mechanism for that is known in dimension ≥ 3.

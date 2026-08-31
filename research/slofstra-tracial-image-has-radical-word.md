---
rg: 2
id: slofstra-tracial-image-has-radical-word
kind: claim
title: A word survives in the sofic radical of the Slofstra tracial image
distinct_from:
  slofstra-involution-not-sofic-radical: that gives a sofic homomorphism from the full solution group detecting `J`; this asks about the quotient by the kernel of the selected nonclosed-game trace, through which that homomorphism is not known to factor.
  sofic-radical-hyperlinear-survivor: that asks for any group, radical word, and hyperlinear detector; this fixes the group to one explicit tracial image supplied by Slofstra's nonclosed LCS game.
  finite-table-quantum-classical-hamming-gap: that asks only for a finite local table; this asks for the global radical word whose image quotient would supply such a table coherently.
  slofstra-natural-negative-corner-image-is-sofic: that proves the particular character obtained by taking the negative corner of the permutation-valued construction has a sofic image; this asks whether a different perfect C_qa character has a nonsofic image.
---

**OPEN ALTERNATIVE-CHARACTER CRITERION.** Let `S` be the solution group of the
nonclosed LCS game in Slofstra, arXiv:1703.08618. Find a Connes-embeddable
perfect-`C_qa` solution-group character `chi`, other than the signed-permutation
negative-corner character ruled out by
`slofstra-natural-negative-corner-image-is-sofic`, and put

```text
N=ker(pi_chi),                  H=S/N.                    (STI1)
```

Find one explicit `w in S` such that

```text
w notin N,                     wN in Rad_sof(H).          (STI2)
```

Equivalently, decide that `H` is nonsofic and exhibit one nontrivial element
of its sofic radical. The quotient `H` is already hyperlinear: mix `chi` with
the trivial character before taking conjugate tensor powers, which converges
to the regular character of its ordinary GNS image. Thus `(STI2)` would give
a concrete hyperlinear nonsofic group and a coherent finite-table gap.

The central sign `J` is the first candidate because `chi(J)=-1`, hence
`J notin N`. But `slofstra-involution-not-sofic-radical` does **not** decide
whether `JN` lies in `Rad_sof(H)`: its permutation-ultraproduct detector is a
homomorphism from `S`, and no inclusion

```text
N subset ker(Theta)                                           (STI3)
```

is known. Without `(STI3)` the detector need not descend to `H`. The same
factorization issue governs every other candidate word.

Precisely, if `q:S->H` is the quotient map, then

```text
q^(-1)(Rad_sof(H))
 = intersection ker(Theta),                               (STI4)
```

where the intersection runs over homomorphisms from `S` to sofic groups
whose kernels contain `N`. Thus a sofic detector on the full solution group
is relevant to `(STI2)` only after the additional kernel-containment check.
Conversely, proving that every such detector kills one surviving word is
already the desired radical theorem; it is not supplied by LCS game
soundness.

For the natural negative-corner character, the quotient is sofic, so no word
can satisfy `(STI2)`. For an alternative character this remains the only
noncircular whole-group extraction from the known nonclosed-game table:
direct-sum/tensor amplification supplies the regular-character unitary
microstates of `H`; the remaining permutation floor is exactly the soficity
of this named quotient, not a consequence of the original classical game
gap.

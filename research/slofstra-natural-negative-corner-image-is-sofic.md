---
rg: 2
id: slofstra-natural-negative-corner-image-is-sofic
kind: claim
title: Slofstra's permutation-corner perfect character has a sofic GNS image
invalidates:
  - slofstra-natural-negative-corner-radical-route
distinct_from:
  slofstra-involution-not-sofic-radical: that only proves `J` survives in one sofic image of the full solution group; this proves the whole image of the associated negative-corner character is sofic.
  known-game-gaps-miss-finite-group-table-quantifiers: that audits every known game source; this closes the only natural character left by its Slofstra subcase.
---

**ESTABLISHED NATURAL-CHARACTER NO-GO.** In the permutation-valued
finite-coordinate construction proving
`slofstra-involution-not-sofic-radical`, the solution-group sign `J` is the
fixed-point-free sheet flip and every generator commutes with it exactly
(or may be made to do so at vanishing Hamming cost). Restrict the coordinate
models to the `J=-1` eigenspaces and let `chi_-` be an ultralimit of their
normalized characters. Then

```text
chi_-(J)=-1,                                             (SNC1)
```

and the vanishing solution-group relators give a perfect `C_qa` model supplied
by the nonclosed LCS construction. But

```text
H_-=S/ker(pi_(chi_-))                                    (SNC2)
```

is sofic: the coordinate restrictions are signed permutations, and
`fixed-flip-negative-corner-is-sofic` converts them uniformly to permutation
microstates.

Consequently

```text
Rad_sof(H_-)=1.                                         (SNC3)
```

There is no word—not `J` and not any other word—surviving `chi_-` while being
killed by every sofic image of `H_-`. Thus Slofstra nonclosure by itself does
not supply the finite unitary-versus-permutation table gap. Any continuation
must first choose a different perfect `C_qa` character and then prove that its
GNS image is nonsofic, which is already the hyperlinear-nonsofic problem for a
named quotient.

DERIVATION
slofstra-natural-negative-corner-proof

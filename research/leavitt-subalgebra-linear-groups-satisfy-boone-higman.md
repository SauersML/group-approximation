---
rg: 2
id: leavitt-subalgebra-linear-groups-satisfy-boone-higman
kind: claim
title: Linear groups over subalgebras of the binary Leavitt algebra embed in its finitely presented simple unit group
distinct_from:
  weyl-algebra-blocks-a-universal-leavitt-host: that shows some coefficient rings do not embed in L_K(1,2), which kills the Leavitt algebra as a universal host; this is the positive statement for the coefficient rings that do embed, now that the unit group is known to be finitely presented.
  binary-leavitt-unit-group-is-simple: that proves simplicity of the unit group; this uses it, together with finite presentation and the prefix-code matrix identifications, to embed every linear group over a Leavitt subalgebra.
  fp-self-similar-groups-embed-in-fp-simple-groups: that embeds finitely presented self-similar groups in Rover--Nekrashevych commutators; this embeds linear groups over Leavitt subalgebras in one fixed finitely presented simple group.
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

**ESTABLISHED (conditional on the imported finite presentation).** Let
`R = L_(F_2)(1,2)`. For every unital subalgebra `A <= R` and every `n >= 1`,
`GL_n(A)` embeds in `R^x`. Since `R^x` is finitely presented
(`leavitt-unit-group-finitely-presented`) and simple
(`binary-leavitt-unit-group-is-simple`), every subgroup of `GL_n(A)` embeds in
a finitely presented simple group. In particular every finitely generated such
subgroup satisfies Boone--Higman.

## Scope

This is one fixed finitely presented simple container. A single finitely
presented group has one word-problem algorithm, so by
`complexity-bounded-host-classes-are-not-universal` it contains copies of only
some decidable inputs. The payoff is a class of inputs: see
`char-two-laurent-linear-groups-satisfy-boone-higman`.

DERIVATION
leavitt-subalgebra-linear-groups-proof

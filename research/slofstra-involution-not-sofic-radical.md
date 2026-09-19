---
rg: 2
id: slofstra-involution-not-sofic-radical
kind: claim
title: The Slofstra involution survives a sofic image
invalidates: [slofstra-solution-group-collision]
distinct_from:
  literal-clifford-ce-model: Same shape of elimination for a different candidate — that one shows the literal non-MF mark has a Connes-embeddable detector and is visible in a sofic group; this one shows Slofstra's involution J is visible in a permutation ultraproduct. Both remove a candidate from the sofic-radical half of a collision, by different constructions in different groups.
  sofic-radical-hyperlinear-survivor: That asks for a word IN the sofic radical with a hyperlinear detector; this proves one specific candidate word is NOT in the sofic radical, so it is an elimination rather than an instance.
  sofic-radical-soficization: That is a general structure theorem about Rad_sof of an arbitrary countable group — functoriality, soficity of the quotient, and Rad_sof trivial iff sofic — naming no group and asserting nothing about any particular element. This is a single explicit non-membership in one named group, proved by constructing one permutation-ultraproduct model. Note it does NOT follow from that theorem's third clause: Theta is not claimed faithful, so J is shown outside Rad_sof(S) without deciding whether S itself is sofic.
artifacts:
  - notes/NOTEPAD.md
---

Let `S` be the solution group produced in the proof of Slofstra,
arXiv:1703.08618v2, Proposition 5.1, and let `J` be its distinguished central
involution.  There is a homomorphism

```text
Theta : S -> product_omega (Sym(Omega_n), d_H)
```

with `Theta(J) != 1`.  Its image is a subgroup of a metric ultraproduct of
finite symmetric groups, hence sofic.  Therefore

```text
J notin Rad_sof(S).
```

## What this refutes

It refutes the assertion isolated in the corpus as `(HSC7)`,

> `every homomorphism S -> a sofic group kills J`,

which was the missing input of a proposed dichotomy. The corpus is explicit
that `(HSC7)` had been the precise gap and that this theorem closes it in the
negative:

> The missing assertion `(HSC7)` is in fact false for the particular solution
> group constructed in Slofstra, arXiv:1703.08618v2, Proposition 5.1.  The
> finite-coordinate constructions in that proof can be made with permutation
> matrices throughout.  Consequently its distinguished involution `J` survives
> in a metric ultraproduct of finite symmetric groups.

## The trap it closes

The tempting inference was that `J`, being invisible in every *exact*
finite-dimensional representation, must lie in the sofic radical. It does not.
Exact finite-dimensional invisibility does not imply sofic invisibility — the
corpus flags this directly (*"exact finite-dimensional invisibility alone does
not imply this"*), and the same trap is already recorded for a different
candidate in `literal-clifford-ce-model`.

That makes two independent eliminations of the same shape. Both times a word
that is invisible to exact finite-dimensional representations turned out to be
visible in a sofic or Connes-embeddable model. Any future candidate for the
sofic-radical half of a radical collision should be tested against a
permutation-ultraproduct construction before effort is spent on the detector
side.

## Scope

This says nothing about whether `S` is sofic, and nothing about
`hyperlinear-nonsofic-group`. `Theta` is not asserted to be faithful — only
`Theta(J) != 1` is needed and only that is proved. It removes one candidate.

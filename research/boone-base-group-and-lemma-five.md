---
rg: 2
id: boone-base-group-and-lemma-five
kind: claim
title: The base group of the Aanderaa-Cohen construction, its scaled embeddings, and Simpson's Lemma 5
artifacts:
  - GroupApproximation/Computability/BooneGroupBase.lean
  - GroupApproximation/Computability/BooneGroupFreeBasis.lean
---

ESTABLISHED.  The base group of the Aanderaa--Cohen construction, as written
out in Simpson's 2005 note, is `G = <t, x, y | xy = yx>`.  Modelled here as the
split extension

    BaseGroup = FreeGroup (Z x Z) semidirect Multiplicative (Z x Z),

with the acting `Z^2` translating the free basis, `t(a,b) = inl (of (a,b))` and
`x^u y^v = inr (ofAdd (u,v))`.  The defining relations come out as Simpson has
them: `sh_comm` is `xy = yx`, `sh_conj_tw` is
`x^{-1} t(a,b) x = t(a+1,b)` and `y^{-1} t(a,b) y = t(a,b+1)`, and `t = t(0,0)`
holds definitionally.

What is established, all of it unconditional:

* `T = Tsub` is the set of elements with trivial `Z^2` component, free on the
  family `t(a,b)`, and `T_S = twSub S` its sub-basis subgroups;
* `emb a b M N` is the canonical embedding of the base group with image
  `G_{ab}^{MN}`, and `emb_injective` holds whenever `M, N` are nonzero;
* `Gsub_eq_closure` -- `G_{ab}^{MN}` is `<t(a,b), x^M, y^N>`, i.e. the range of
  `emb` is Simpson's *definition* of it, not merely contained in it;
* **Simpson's Lemma 5**, `T_{ab}^{MN} = T cap G_{ab}^{MN}`.

## Why the split extension is the definition

`G` is `<t> * Z^2`; the normal closure of `<t>` in it is free on the conjugates
`t(a,b)` indexed by the coset representatives `x^a y^b`, and `Z^2` splits the
quotient.  Taking the split extension as the definition makes the two facts
that carry the whole argument -- freeness of `T` on `{t(a,b)}`, and Lemma 5 --
*structural*, reached through [[free-subbasis-subgroup-calculus]] rather than
through the Kurosh subgroup theorem, which Mathlib does not have.

The cost of that choice is deferred, not avoided: the final group cannot be
called finitely presented until the split extension is identified with the
two-generator one-relator presentation.  That is
[[boone-base-group-two-generator-one-relator]], and it is done.

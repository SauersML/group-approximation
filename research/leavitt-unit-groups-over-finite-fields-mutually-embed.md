---
rg: 2
id: leavitt-unit-groups-over-finite-fields-mutually-embed
kind: claim
title: In each characteristic p all Leavitt unit groups L_(F_q)(1,n)^x embed in one another, so their approximation problems are one problem
distinct_from:
  d-ary-leavitt-groups-nonsofic-over-finite-fields: that proves nonsoficity of every d-ary Leavitt unit group over a finite field through a corner route; this proves the groups embed in each other, so every subgroup-closed property is decided at once for the whole family of a given characteristic.
  leavitt-algebras-l-k-1-n-are-simple: that is simplicity of the algebras; this is the resulting mutual embedding of their unit groups.
---

**ESTABLISHED** by `leavitt-unit-groups-over-finite-fields-mutually-embed-proof`.

Fix a prime `p`. For all powers `q, q'` of `p` and all `n, n' >= 2` there are
injective group homomorphisms

```text
L_(F_q)(1,n)^x  ->  L_(F_p)(1,2)^x  ->  L_(F_q')(1,n')^x .
```

**Consequence.** Let `P` be any isomorphism-invariant property of countable groups
that passes to subgroups, such as being hyperlinear, sofic, linear sofic over a
given field, weakly sofic, LEF, a-T-menable, or free of `H_3(Z)`. Then `P` holds for
one member of the family exactly when it holds for all. In particular:
- `binary-leavitt-unit-group-hyperlinear` is the hyperlinearity question for every
  `L_(F_(2^k))(1,n)^x`;
- `leavitt-unit-group-has-no-integer-heisenberg-subgroup` is the Heisenberg question
  for all of them;
- every one of these groups contains Thompson's `V`, so a positive hyperlinearity
  answer for any of them requires `thompson-v-hyperlinear`.

The "relatives `L_K(1,n)^x`" of the binary witness therefore add no new
hyperlinearity problem over finite fields. A genuinely different instance needs a
different characteristic, or an infinite coefficient field.

## Credit and what is new

No novelty is claimed for any of the algebra embeddings. The node records their
consequence for unit groups and approximation properties. Credit check prompted by
`ex-novelty`; sources read on 2026-09-13 from arXiv PDFs, text extracted on MSI.

- **Step (a), `L_K(1,n) -> L_K(1,2)` unital, is a special case of known theorems.**
  - N. Brownlowe and A. P. W. Sorensen, *Leavitt R-algebras over countable graphs embed
    into L_(2,R)*, arXiv:1503.08705v3, J. Algebra 454 (2016) 334--356, **Theorem 4.1**:
    "Let R be a commutative ring with unit and let E be a directed graph. If E is
    countable, then there is a *-algebraic embedding of the Leavitt path algebra L_R(E)
    into L_(2,R), and if E^0 is finite, then this embedding can be chosen to be unital."
    The rose `R_n` has one vertex, so the embedding is unital.
  - B. Bilich, R. Hazrat and T. G. Nam, *Embedding k-algebras into Leavitt algebra
    L_k(1,2)*, arXiv:2512.09241, **Theorem 2.5**: for a field `k`, a unital `k`-algebra
    `R` and a finite graph `E` with condition (L), `L_R(E)` embeds into `L_R(1,2)`.
  - The prefix-code construction used here is the classical one for Cuntz and Leavitt
    algebras.
- **Step (c) must use a corner.** Bilich--Hazrat--Nam, **Corollary 2.4**: for
  `1 < m, 1 < n` there is a unital injective homomorphism
  `M_s(L_k(1,m)) -> M_t(L_k(1,n))` exactly when positive integers `k, k'` exist with
  `(m-1)k = (n-1)k'` and `ks ≡ t (mod n-1)`. With `m = 2` and `s = t = 1` it reads
  `k = (n-1)k'` and `k ≡ 1 (mod n-1)`, which forces `n = 2`, so for `n >= 3` there is no unital embedding `L(1,2) -> L(1,n)`. Step (c)
  instead embeds `L_(F_p)(1,2)` unitally in a corner `e L_(F_q)(1,n) e`, and pads units
  by `1 - e`. This is an elementary split-clopen construction; no source was found
  stating it for unit groups, and none was searched for beyond these two papers.
- **Step (b), lowering the field through the regular representation of `F_q` and
  `M_k(L) ~= L`, is elementary.** No priority is claimed.
- **What the node adds.** It assembles (a)--(c) into mutual embeddings of all
  `L_(F_q)(1,n)^x` of one characteristic, and states the consequence that every
  subgroup-closed approximation property is a single question per characteristic. The
  literature check was bounded to the two papers above and the Abrams survey.

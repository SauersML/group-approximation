---
rg: 2
id: leavitt-unit-group-steinberg-weyl-presentation
kind: claim
title: The binary Leavitt unit group has a presentation with seven generators and sixty relators of total length 1007
distinct_from:
  leavitt-unit-group-finitely-presented: that is finite presentability of the same group, imported from Khanh, whose explicit presentation has 20(4^195-1)/3 generators; this is one explicit seven-generator, sixty-relator presentation, written out and checked.
  atlas-steinberg-rank-five-translation: that is a 4,648-entry relator list in the twelve atlas generators of A8 * A8 presenting a central extension relative to the atlas; this presents the unit group itself with sixty relators on seven generators.
  atlas-steinberg-spare-index-independence: that is the theorem that the 100-generator Steinberg family presents St_5(L); this consumes it and collapses the family through the symmetric-group symmetry of the roots.
artifacts:
  - research/artifacts/leavitt-unit-group-steinberg-weyl-presentation-2026-09-12.md
  - experiments/nonsofic-certificates/presentations/verify_st5_weyl_presentation.py
  - experiments/nonsofic-certificates/presentations/st5-weyl-presentation.json
---

**ESTABLISHED (2026-09-12, unreviewed)** through
`leavitt-unit-group-steinberg-weyl-presentation-proof`.

Let `L = L_(F_2)(1,2)`, letters `A = {1,e,f,E,F} = {1,s0,s1,t0,t1}`, `[x,y] = xyx^-1y^-1`.
Let `P` be the group with generators `c, t, y_1, y_e, y_f, y_E, y_F`, abbreviations

```text
X12(a) = y_a     X23(a) = c y_a c^-1     X34(a) = c^2 y_a c^-2     X13(a) = tc y_a c^-1t^-1
X32(a) = ct y_a t^-1c^-1     X43(a) = c^2t y_a t^-1c^-2     X14(a) = c^-1tc^-1t y_a t^-1ct^-1c
```

and sixty relators:

```text
t^2, c^5, (tc)^4, (tc^-1tc)^3, (tc^-2tc^2)^2                               5
[y_a, c^2tc^-2], [y_a, c^-2tc^2]                    (a in A)              10
(t y_1)^3,  y_1^2                                                           2
[X12(a), X34(b)] ({a,b} in A), [X12(1),X13(1)], [X12(1),X32(1)]            17
[X12(a), X23(b)] = X13(ab)       (ab a letter or 0)                        13
[X12(a), X23(b)] = [X14(a), X43(b)]   (ab irreducible)                     12
[X12(e), X23(E)] [X12(f), X23(F)] = X13(1)                                  1
```

Total literal length 1,007, longest relator 38. With the chart `D = (00,01,10,110,111)`:
`c` is the Thompson unit `d_k w -> d_(k+1) w`, `t` swaps the prefixes `00` and `01`, and
`y_1 = 1+S[00]T[01]`, `y_e = 1+S[000]T[01]`, `y_f = 1+S[001]T[01]`, `y_E = 1+S[00]T[010]`,
`y_F = 1+S[00]T[011]`.

**Theorem.** These images define an isomorphism `P -> L^x`.

So the first nonsofic group can be written on half a page:
`explicit-sixty-relator-nonsofic-group`. Every relator was checked in `L^x` by exact dual-path
arithmetic. The completeness of the list is a proof, not a computation: an `S_5` symmetry
lemma, seven one-line commutation derivations, the spare-index theorem, and Khanh's Theorem 5.4.
The literal words, checksums and controls are in the JSON artifact.

The graph's previous smallest explicit list was `atlas-steinberg-rank-five-translation`:
4,648 entries in twelve generators, X-lengths up to 595, and it presented a central extension
relative to the atlas.

---
rg: 2
id: zaremsky-2-19-embeddings-into-brin-thompson-groups
kind: claim
title: "Zaremsky Problem 2.19 resolved: which groups embed in Thompson's group V and the Brin-Thompson groups nV?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 19,
verbatim: "(Added 10/2/24) Various questions about which groups embed in
Thompson's group V and/or the Brin–Thompson groups 2V, 3V, etc. Does every
hyperbolic group embed in one of these? Is there a hyperbolic group that does
not embed in V? Does every GL_n(Z) embed in some mV? Maybe even in 2V? Does Q
embed in 2V? [Xiaolei Wu points out that the answer to, "Is there a hyperbolic
group that does not embed in V?" is yes, because an infinite hyperbolic group
with property (T) cannot embed in V, on account of V having the Haagerup
property. For 2V and up, things remain mysterious.]"

This claim is the question. The opening sentence is a heading, not a question
with an answer, so this graph reads the problem as its five explicit questions.
The claim is established only through `zaremsky-2-19-by-all-parts`, which
requires the five part-claims, each itself a question established only by an
answer route:

- **(a)** `zaremsky-2-19a-every-hyperbolic-group-in-some-nv-resolved`: does
  every hyperbolic group embed in some nV?
- **(b)** `zaremsky-2-19b-hyperbolic-group-outside-v-resolved`: is there a
  hyperbolic group that does not embed in V? (answered yes in the list's note)
- **(c)** `zaremsky-2-19c-every-gl-n-z-in-some-mv-resolved`: does every
  GL_n(Z) embed in some mV?
- **(d)** `zaremsky-2-19d-every-gl-n-z-in-2v-resolved`: does every GL_n(Z)
  embed in 2V?
- **(e)** `zaremsky-2-19e-rationals-embed-in-2v-resolved`: does Q embed in 2V?

Never write a `requires: []` route into this claim or into a part-claim.

## Reading

- nV is the group of rearrangements of the Cantor cube `({0,1}^ω)^n`: the
  homeomorphisms that map the pieces of a finite partition into subcubes onto
  the pieces of another such partition by prefix replacement in each
  coordinate (Belk–Bleak–Matucci, arXiv:1602.08635, §3). 1V = V.
- For j < k, jV embeds in kV (Brin; recalled in arXiv:1602.08635, §1). So
  "embeds in some nV" is the same as "embeds in nV for every large n".
- "Embed" means an injective homomorphism, with no condition on the action.
- A group that virtually embeds in nV embeds in nV, for the same n
  (arXiv:1602.08635, p. 2, after Corollary 1.3: finite groups embed
  demonstratively in nV, and the Bleak–Salazar-Díaz wreath product theorem
  applies). So every part-question is insensitive to finite-index passage.

## Couplings with Problem 2.7

- If nV has the Haagerup property for infinitely many n, equivalently for
  every n, then no infinite group with property (T) embeds in any nV. Then (a)
  has answer no, because infinite hyperbolic groups with property (T) exist,
  and (c) has answer no, because SL_3(Z) has property (T).
- Conversely, a yes to (a) or to (c) puts an infinite property (T) group inside
  some mV, so kV fails the Haagerup property for every k ≥ m. That answers the
  Haagerup part of `zaremsky-2-07-brin-thompson-nv-haagerup-or-t`
  negatively for large n.

## Attempts

- 2026-09-13 (lane z2-19-hyperbolic-nv, unreviewed):
  - Part (b) is imported from Farley's Haagerup theorem for V.
  - Partial progress on (a): every group that virtually embeds in a finitely
    generated RAAG embeds in some nV (Belk–Bleak–Matucci), which covers every
    hyperbolic group acting properly and cocompactly on a CAT(0) cube complex
    (Agol). The open core of (a) is the hyperbolic groups that virtually embed
    in no RAAG, including every infinite hyperbolic group with property (T).
  - Parts (c)–(e) are worked by lane z2-19-glnz-q-2v. For (e), Kojima and
    Sheng, arXiv:2603.18410 (v3, May 23, 2026, unrefereed), claim that nV
    contains continuum many copies of Q for n ≥ 2.

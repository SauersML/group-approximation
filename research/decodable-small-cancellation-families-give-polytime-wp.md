---
rg: 2
id: decodable-small-cancellation-families-give-polytime-wp
kind: claim
title: A Gr'(1/6)-labelled large-girth family with polynomial-time path decoding and short-complement search gives a non-exact group with polynomial-time word problem
distinct_from:
  decidable-graphical-non-exact-groups-exist: that proves solvability of the word problem for Osajda's recursive labellings with no time bound; this isolates the two algorithmic properties of the labelled components that make Dehn's algorithm run in polynomial time.
---

**ESTABLISHED (lane proof, not reviewed).** Route:
`polytime-non-exact-group-via-decodable-labellings` (the proof is given there).

Let `Γ = ⊔_n Γ_n` be a reduced labelling, over a finite alphabet `S`, of finite connected
graphs of degree between 3 and `D`, with girths `g_n ≥ n`. Assume:

- **(SC)** Graphical small cancellation `Gr'(1/6)`: every essential piece contained in a
  simple cycle `c` of `Γ` has length `< |c|/6`. Here pieces are taken modulo
  label-preserving automorphisms, as in Gruber, arXiv:1210.0178.
- **(Dec)** Given `n` and a word `u` with `|u| ≥ g_n/2`, one can decide in time
  `poly(|u|)` whether `u` labels a path in `Γ_n`. If it does, one can output
  descriptions of size `poly(|u|)` of the start and end of one such path.
- **(Short)** Given `n`, two vertex descriptions `x, y` of `Γ_n`, and a bound `ℓ`, one can
  decide in time `poly(ℓ + |x| + |y|)` whether `d_(Γ_n)(x,y) < ℓ`. If it is, one can
  output the label of a path from `x` to `y` of length `< ℓ`.

Then `G(Γ) = <S | Γ>` has word problem decidable in polynomial time, and `G(Γ)` has no
property A.

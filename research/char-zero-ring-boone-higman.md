---
rg: 2
id: char-zero-ring-boone-higman
kind: claim
title: Every finitely generated Q-algebra with solvable word problem embeds in a finitely presented simple ring
distinct_from:
  algebra-boone-higman-conjecture: that is the conjecture over every computable field K with finite presentation over K; this is the case K = Q with finite presentation over Z, which is equivalent to that case by fp-simple-q-algebras-embed-in-fp-simple-rings.
  char-zero-representable-rings-embed-in-fp-simple-rings: that is the established class of inputs linear over finitely generated commutative Q-algebras; this is every decidable input.
  countable-char-zero-fields-embed-in-fp-simple-rings: that is the countable-field case, whose inputs are not finitely generated; this is the finitely generated case.
---

**OPEN.** Every finitely generated `Q`-algebra `A` with solvable word problem embeds in a
finitely presented simple ring.

**Equivalence with the algebra conjecture over `Q`.** By
`fp-simple-q-algebras-embed-in-fp-simple-rings`, part 3, `A` embeds in a finitely
presented simple ring if and only if it embeds in a finitely presented simple
`Q`-algebra. So this claim is exactly the case `K = Q` of
`algebra-boone-higman-conjecture`. It follows from that root by
`char-zero-ring-bh-via-algebra-bh-over-q`, and conversely implies its `K = Q` case.

## Known cases
- **Representable inputs** (`char-zero-representable-rings-embed-in-fp-simple-rings`):
  subrings of `M_D(C ⊗_Q Q<x_1..x_m>)` for a finitely generated commutative `Q`-algebra
  or finitely generated field `C`.
- **Inputs over fields of finite transcendence degree**
  (`field-envelopes-pass-to-algebraic-closures`).
- All these share one recursive word-problem bound. So they do not reach the complexity
  benchmark `no-fp-simple-algebra-hosts-every-decidable-algebra`, which a proof of the
  full claim must clear with hosts that vary with the input.

## Attempts
1. **Why the lane's constructions stop here (2026-09-17, lane `gq-ring-fp-simple`).** In
   the register method (`rational-function-fields-embed-in-fp-simple-rings`), one
   resolvent together with a finite substitution dynamics inverts every value of a
   computable family of never-zero polynomials. A decidable noncommutative input would
   need the dynamics to encode its word problem, so that every nonzero element acquires a
   finite certificate of generating the unit ideal. That is exactly the ψ-minimality wall
   recorded in `decidable-algebras-embed-in-simple-ln-completions`. The register method
   meets it only for inputs whose nonzero elements are detected by evaluation at a
   computable set of points, that is, by commutative representations.

---
rg: 2
id: fp-simple-dehn-functions-realize-every-recursive-lower-bound
kind: claim
title: For every recursive function some finitely presented simple group has Dehn function at least that function
distinct_from:
  fp-simple-dehn-functions-have-no-recursive-upper-bound: that is the weak reading, a Dehn function escaping f on infinitely many lengths; this demands f ≼ delta_S at every scale, and it implies that one.
  fp-simple-groups-with-arbitrarily-complex-word-problem: that is about word-problem time complexity; this is about the Dehn function, which a hard word problem forces to be large only infinitely often.
---

**OPEN.** For every recursive `f: N -> N` there is a finitely presented simple
group `S` with `f ≼ delta_S`, that is, some `K > 0` has
`f(n) <= K delta_S(Kn) + Kn` for all `n`.

This is the affirmative answer to
`zaremsky-1-16-fp-simple-groups-with-large-dehn-functions` under its adopted
reading. The case `f(n) = 2^n` is established
(`fp-simple-group-with-at-least-exponential-dehn-function`); no superexponential
case is known.

## Attempts

1. **Quasi-retract hosts.** Quasi-retracts have smaller Dehn functions
   (arXiv:2305.15176v2, Citation 1.2), and both known exponential examples are
   quasi-retract constructions. The needed input is, for each recursive `f`, a
   finitely presented group `H` with `f ≼ delta_H` that is a quasi-retract of a
   finitely presented simple group.
   - *Linear inputs* (Llosa Isenrich–Schesler–Wu, arXiv:2510.01952v1, Theorem 1.4).
     This needs finitely presented linear groups with Dehn functions at least `f`.
     LISW p. 4: "the fastest known Dehn function of a linear group is exponential",
     and Gersten–Riley conjecture a recursive upper bound. A heuristic reason, not
     recorded as a claim: in a finitely generated subgroup of `GL_n(Q)` every
     infinite cyclic subgroup is at most exponentially distorted (a virtually
     unipotent element has polynomially growing powers, and otherwise some
     eigenvalue has absolute value `> 1` at some place). So the iterated distortion
     behind superexponential Dehn functions (Baumslag–Gersten, hydra groups) has no
     linear model. *Blocked* unless the Gersten–Riley conjecture fails.
   - *Self-similar inputs* with calibrated representations (persistent, rational,
     weakly diagonal, as in arXiv:2305.15176). The candidates with large Dehn
     functions are the Kharlampovich–Myasnikov–Sapir groups, arXiv:1204.6506
     (finitely presented, residually finite, "arbitrarily large (recursive) Dehn
     function"). Whether they admit faithful self-similar representations is
     unknown (Zaremsky, p. 2), let alone calibrated ones. *Open, untried here.*
2. **Word-problem complexity.** Gives only `fp-simple-dehn-functions-have-no-recursive-upper-bound`.
   An almost-everywhere hard word problem does not help either: the
   diagram-enumeration algorithm needs a Dehn bound at the length being decided,
   and a Dehn function that is small on a sparse infinite set of lengths yields no
   algorithm that is fast on all long inputs. *Dead as a route to this claim.*

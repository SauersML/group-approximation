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
3. **2026-09-17 (swarm-0917-w5-pull-z-6, inverter): the verdict of Attempt 2 is
   wrong.** Word-problem complexity does give this claim, conditionally on
   Boone–Higman.
   - *Where Attempt 2 fails.* Embed a *dual certificate*: a finitely generated
     group with solvable word problem containing words `u_i`, `v_i` of length
     `4i + 4`, where `u_i = 1` iff `i ∈ A` and `v_i = 1` iff `i ∉ A`, for an
     almost-everywhere hard recursive `A`. In any finitely presented host, search
     both certificates by increasing area. The search always halts, needs no Dehn
     bound in advance, and is fast at every length where the host's Dehn function
     is small. Almost-everywhere hardness forbids infinitely many fast inputs.
   - Established: `almost-everywhere-hard-recursive-sets-exist` (Rabin 1960,
     self-contained cancellation proof).
   - Established: `dual-certificate-groups-force-large-host-dehn-functions`,
     with `H_f = G_A * G_(N \ A)` and `G_B = <a, b, t | [t, b^i a b^(-i)], i ∈ B>`.
     Every finitely presented overgroup `P` of `H_f` has `f ≼ delta_P` for `n >= 1`.
   - New route `fp-simple-large-dehn-via-boone-higman`. This claim follows from
     `boone-higman-conjecture`, and even from embedding the groups `H_f` alone.
     Contrapositive: `a-recursive-function-is-no-fp-simple-dehn-lower-bound`
     implies that Boone–Higman fails.
   - *Convention.* At `n = 0` the defining inequality reads `f(0) <= 0` for every
     group. So "for all `n`" in the statement should be read as `n >= 1`.
   - The distinct_from note on `fp-simple-groups-with-arbitrarily-complex-word-problem`
     says a hard word problem forces the Dehn function to be large only infinitely
     often. The argument above shows that this does not hold for a dual certificate. For a single certificate no such lower bound is proved.
   - *Still OPEN:* an unconditional proof needs a finitely presented simple host
     for `H_f`, or for any dual-certificate group of an almost-everywhere hard set.

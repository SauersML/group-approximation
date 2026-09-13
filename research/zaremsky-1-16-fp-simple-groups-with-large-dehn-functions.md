---
rg: 2
id: zaremsky-1-16-fp-simple-groups-with-large-dehn-functions
kind: claim
title: "Zaremsky Problem 1.16 resolved: are there finitely presented simple groups with arbitrarily large recursive Dehn functions?"
root: true
distinct_from:
  fp-simple-groups-with-arbitrarily-complex-word-problem: that is the Boone--Higman region's root about the word-problem time complexity of finitely presented simple groups; this is Zaremsky's question about their Dehn functions, a geometric invariant that word-problem complexity bounds from below only in the weak, infinitely-often sense.
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 16, verbatim:
"Find finitely presented simple groups with arbitrarily large (recursive) Dehn
function."

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-1-16-by-yes` requires
  `fp-simple-dehn-functions-realize-every-recursive-lower-bound`.
- **No**: `zaremsky-1-16-by-no` requires
  `a-recursive-function-is-no-fp-simple-dehn-lower-bound`.

Never write a `requires: []` route into this claim.

**Reading.** For a finite presentation `<X | R>` of `G` with `pi: F(X) -> G`,
`delta_G(n) = max { Area(w) : w in ker(pi), |w| <= n }`, where `Area(w)` is the
word length of `w` over the conjugates of `R^{+-1}`. Write `f ≼ g` when some
`K > 0` has `f(n) <= K g(Kn) + Kn` for all `n`. The Dehn function is well defined
up to `≃` (Zaremsky, arXiv:2305.15176v2, §1.1). A finitely presented simple group
has solvable word problem (Kuznetsov; `simple-envelope-forces-solvable-word-problem`),
so its Dehn function is recursive; the parenthetical "(recursive)" records that
only recursive functions can occur.

- **Strong reading (adopted).** For every recursive `f: N -> N` there is a
  finitely presented simple group `S` with `f ≼ delta_S`. This matches Zaremsky's
  own remark (arXiv:2305.15176v2, p. 3) that embedding a group with arbitrarily
  difficult solvable word problem in a finitely presented simple group "would
  provide an arbitrarily large, recursive lower bound on the Dehn function of the
  simple group".
- **Weak reading.** For every recursive `f` some finitely presented simple `S`
  has `delta_S ⋠ f` (`fp-simple-dehn-functions-have-no-recursive-upper-bound`).
  The strong reading implies it (`fp-simple-unbounded-dehn-from-realized-lower-bounds`).
  A proof of the weak reading alone is partial progress and does not close this
  root: a Dehn function that beats `f` only on a sparse set of lengths is not at
  least `f`.

**What is known** (sources read 2026-09-13).

- To the best of Zaremsky's knowledge in 2023 (arXiv:2305.15176v2, pp. 1–2), the
  finitely presented simple groups with any known Dehn function bound were the
  Burger–Mozes groups (quadratic) and Thompson's `T` and `V`
  (`delta_T ≼ n^5`, `delta_V ≼ n^11`). `T` is quadratic by Migliorini,
  arXiv:2410.23088 (Problem 2.5).
- **At least exponential.** arXiv:2305.15176v2, Theorem 3.2: "There exist finitely
  presented simple groups with at least exponential Dehn function." Imported as
  `fp-simple-group-with-at-least-exponential-dehn-function`.
- **Higher dimensions.** Llosa Isenrich–Schesler–Wu, arXiv:2510.01952v1,
  Corollary 1.8: "For every finite subset I ⊆ N, there is a simple group of type
  F∞ whose n-dimensional Dehn function is at least exponential for every n ∈ I."
  Their p. 4 names the barrier of their method: "despite of the fact that no
  recursive upper bound on Dehn functions of finitely presented linear groups is
  known so far, though conjectured to exist by Gersten and Riley [GR05, Conjecture
  8.7], the fastest known Dehn function of a linear group is exponential."
- No superexponential lower bound for a finitely presented simple group was found
  (bounded check: web search, these two papers, the repository at 2026-09-13).

**Graph wiring.**

- Weak reading ⇐ `fp-simple-groups-with-arbitrarily-complex-word-problem` (open
  root of the Boone–Higman region, implied by `boone-higman-conjecture`) with
  `dehn-function-bound-gives-word-problem-time-bound`, through the route
  `fp-simple-unbounded-dehn-via-complex-word-problem`.
- Strong reading: quasi-retract hosts, see Attempts 2.

## Attempts

1. **Hard word problems (weak reading only).** A Dehn bound `f` puts the word
   problem in time `2^(C(f(Cl)+l)^2)`, so a family beating every recursive time
   bound has unbounded Dehn functions. Wired as above. Open because the
   complexity root is open, a live Boone–Higman crux this lane does not duplicate.
   It cannot give the strong reading: complexity lower bounds hold infinitely
   often, while `f ≼ delta_S` must hold at every scale.
2. **Quasi-retract hosts (strong reading).** If `H` is a quasi-retract of a
   finitely presented `G` then `delta_H ≼ delta_G` (arXiv:2305.15176v2, Citation
   1.2, attributed to Alonso). Both known examples work this way. `BS(1,n)` is a
   quasi-retract of `V_{n+2}(BS(1,n))`, whose commutator subgroup has finite index
   and is simple (Zaremsky). Every finitely generated `H <= GL_n(Q)` is a
   quasi-retract of a simple group with the same finiteness properties (LISW,
   Theorem 1.4). The strong reading needs, for each recursive `f`, a finitely
   presented quasi-retract `H` of a finitely presented simple group with
   `f ≼ delta_H`.
   - Linear inputs are blocked unless finitely presented linear groups have
     arbitrarily large Dehn functions, which the Gersten–Riley conjecture denies.
   - Self-similar inputs: Zaremsky (p. 2) does "not know whether [the
     Kharlampovich–Myasnikov–Sapir groups] admit faithful self-similar
     representations", and the Dison–Riley hydra groups "are not residually finite
     [Pue16]" (p. 3), so they admit none.
3. **Twisted Brin–Thompson hosts.** `SV_G` accepts any input, but "finite
   presentability of the twisted Brin–Thompson group does not follow for free"
   (arXiv:2305.15176v2, p. 3), and no quasi-retraction of `SV_G` onto `G` is
   known. Not attempted.

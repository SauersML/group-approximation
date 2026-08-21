---
rg: 2
id: nonhyperlinear-conditional-routes-landscape
kind: claim
title: Every known route to a non-hyperlinear group hinges on flexible HS-stability or weak ucp-stability of some property (T) or (T;FD) group, and where the relative-commutant route sits
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  relative-commutant-collapse-for-sl2-pair: that is one specific operator-algebra target; this is the map of all published conditional routes and the shared open hypothesis, recorded so the program does not mistake any single route for a solved problem.
  non-hyperlinear-group: that is the goal; this is a survey claim about the reduction landscape, established by citation.
---

**Established by citation (survey).**  As of 2026-08, no non-hyperlinear
group is known (IAS lecture, "why are there still no known non-hyperlinear
groups").  Every published route reduces existence to an open stability
question of the same shape:

- **Dogon, arXiv:2211.10492.**  For a countable property (T) group `Gamma`
  with a suitable central extension by a countable abelian `A`, if `Gamma`
  is flexibly HS-stable -- or merely *weakly ucp-stable* (Thm 1.6, weaker,
  after Ioana--Spaas--Wiersma) -- then a non-hyperlinear group exists.
  Applied to `Sp_(2g)(Z)` (which has (T) and `pi_1(Sp_(2g)(R)) = Z`), to
  generic Gromov-density-`(1/3,1/2)` random groups, and to all infinitely
  presented (T) groups.  HS analogue of Bowen--Burton (P-stability of
  `PSL_n(Z)` and non-sofic groups).
- **Dogon--Vigdorovich, arXiv:2506.20843.**  If `SL_2(Z[1/p])` (property
  (T;FD), not (T)) is flexibly HS-stable, then it has a non-hyperlinear
  finite central extension; reduced to the Iwahori local-global question.
- **This graph's relative-commutant route.**
  `relative-commutant-collapse-for-sl2-pair` /
  `sl3-pair-relative-commutant-route`: the co-dense Kazhdan HNN extension
  is non-hyperlinear once `pi(C)' cap M = pi(A)' cap M` in the matrix
  ultraproduct -- a statement that needs neither central extensions nor the
  `pi_1` condition, unifying with Alekseev--Thom OP 6.2 and the Kun--Thom
  lane, for the explicit commensurated pairs `SL_2(Z) <= SL_2(Z[1/2])` and
  `SL_3(Z) <= SL_3(Z[1/2])`.

**The shared open core.**  Flexible HS-stability (or weak ucp-stability) of
an infinite (T)/(T;FD) group is not known for ANY such group; an infinite
hyperlinear (T) group is not even locally HS-stable, so these questions ask
for stability against the (T) obstruction, which is exactly why they are
hard.  The character/trace side is settled everywhere by rigidity (limits
of finite-dimensional traces), and for `SL_2(Z[1/2])` even the abelian
solenoid dynamics is settled (single automorphism, dense periodic
measures); the irreducibly open part is the correction of NON-hyperfinite
asymptotic representations, equivalently the relative-commutant collapse
`(RCC)`.

**Progress recorded in this graph (2026-08-21).**  The NEAR sector of the
Dogon--Vigdorovich question is now a theorem
(`iwahori-uniform-infinitesimal-rigidity` + `iwahori-newton-closes-near-sector`):
representations within a fixed tube of the compatible locus obey
`D(pi) <= C def(pi)`.  Only the far sector (`iwahori-outlier-repair`, an
operator/relative-commutant statement) remains, and it is the same `(RCC)`.

## Attempts

- **Weak ucp-stability weakening.**  Dogon's Thm 1.6 shows weak
  ucp-stability suffices for the central-extension route; whether the
  relative-commutant route
  (`hnn-over-codense-kazhdan-subgroup-not-hyperlinear`) also weakens from
  flexible HS-stability to weak ucp-stability is worth checking -- the
  proof only needs to correct the restricted microstates enough to place
  `k` in the commutant, which a ucp correction might provide.
- **Where to spend effort.**  Since all routes share the stability/ucp
  core, effort concentrates on `(RCC)` for a commensurated arithmetic pair
  (Popa deformation/rigidity, proper proximality) or on a direct
  construction of a flexibly stable (T;FD) group, not on multiplying
  conditional routes.

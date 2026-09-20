---
rg: 2
id: binary-lcs-perfect-qc-strict-qa-gap-exists
kind: claim
title: A finite binary linear-system game has a perfect commuting strategy and quantum value strictly below one
distinct_from:
  mipstar-bcs-tracial-nonru-exists: That is an arbitrary Boolean constraint system supplied by MIPstar equals RE; this requires binary linear equations.
  perfect-lcs-gap-implies-nonhyperlinear: That is the conditional implication from a game to its nonhyperlinear solution group; this is existence of such a game.
  explicit-exact-support-lcs-witness: That demands an actual frozen equation list and checkable numerical constants from an exact-support construction; this only establishes existence and a positive, not displayed, gap.
  perfect-completeness-constant-soundness-lcs-compiler: That is a machine-indexed interface with asymmetric promises; this names a single separating linear system.
artifacts:
  - research/artifacts/liu-to-linear-games-and-marked-gap-2026-09-20.md
---

There is a finite system of linear equations over F_2 whose associated
constraint-system game has a perfect commuting-operator strategy but no
perfect quantum-approximable strategy. For any fixed full-support question
distribution, there is epsilon > 0 such that every finite-dimensional
quantum strategy wins with probability at most 1-epsilon.

Equivalently its BCS algebra has a tracial state but no unital
*-homomorphism to R^U. This is a binary LINEAR system, not merely a general
Boolean constraint system, and the conclusion excludes success approaching
one, not just success exactly equal to one in a fixed dimension.

The route imports Paddock--Slofstra Proposition 5.8 and Theorem 3.11 and
uses the finite-presented Leavitt witness. Its nonhyperlinearity ultimately
uses Jihao Liu's internality theorem; its finite presentation is a separate
input due to Huynh Viet Khanh. This does not claim a new proof of the
published group-to-game reduction or literature priority for its application.

## Constructive boundary

The group-to-game construction is effective given a finite presentation and
a word already known to be nontrivial and invisible in all tracial matrix
ultraproduct homomorphisms. It does not itself find that word, supply a
numerical collapse modulus, or make the output small. The explicit numerical
Leavitt target is `leavitt-lcs-game-with-certified-numerical-gap`.

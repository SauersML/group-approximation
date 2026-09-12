---
rg: 2
id: word-level-seed-wirings-preserve-matricial-approximability
kind: claim
title: Word-level perfect-seed wirings preserve marked matricial approximability
artifacts:
  - research/word-seed-wiring-ultraproduct-transfer-proof.md
distinct_from:
  fixed-perfect-seeds-do-not-black-box-exactify-tv: that treats game-level AND, OR, mixtures, and a common operator gate; this treats every universal group-word substitution at once.
  opposite-sign-compressions-are-spectral-routing: that converts the minimal complete two-gate compression into one reflection equality; this explains why such equalities cannot amplify a merely approximate seed.
  tv-central-flags-and-private-slacks-cannot-exactify: that treats elementary flags and private equation slacks; this is a functorial obstruction for arbitrary finite marked presentations.
---

Let \((\Gamma_C,J_C)\) and \((\Gamma_S,J_S)\) be finitely presented groups
with distinguished central involutions.  Suppose a universal word-level
wiring of the seed presentation into the compiled presentation induces a
homomorphism

$$
\Phi:\Gamma_C\longrightarrow\Gamma_S,
\qquad
\Phi(J_C)=J_S.                                         \tag{1}
$$

If \(\Gamma_S\) has a homomorphism to a tracial metric ultraproduct of
matrix unitary groups which sends \(J_S\) to \(-I\), then
\(\Gamma_C\) has one sending \(J_C\) to \(-I\): simply compose it with
\(\Phi\).

There is also a finite quantitative form.  Fix a word representative for
\(\Phi\) on generators.  For every compiled relator, choose a finite
van Kampen expression of its image in conjugates of seed relators.  If
\(N\) is the largest number of cells in these finitely many expressions,
then a matrix tuple satisfying every seed relator within normalized
Hilbert--Schmidt error \(\eta\) yields a compiled word tuple satisfying
every compiled relator within \(N\eta\).

Therefore no universal group-word or LCS-word substitution can turn a
fixed seed which is matricially approximable at \(J=-I\) into a marked
constant-gap presentation.  In particular, a perfect seed whose
finite-dimensional game value is one only by nonattainment remains
gapless under such a wiring.

The theorem does not cover a construction which selects one special
non-matricially-approximable state of the seed algebra by non-group
projection constraints, nor a relation-dependent corner operation which
is not valid in every seed representation.  Such a construction would no
longer be a word-level black-box use of the seed.

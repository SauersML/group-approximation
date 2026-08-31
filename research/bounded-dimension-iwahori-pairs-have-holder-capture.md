---
rg: 2
id: bounded-dimension-iwahori-pairs-have-holder-capture
kind: claim
title: Bounded-dimensional Iwahori pairs have global Hölder congruence capture
artifacts:
  - research/semialgebraic-lojasiewicz-captures-fixed-matrix-size.md
distinct_from:
  bounded-dyadic-conductor-iwahori-pairs-have-uniform-repair: that is dimension-free but assumes a bounded dyadic conductor; this allows arbitrary infinite-image and noncongruence vertex representations but fixes the ambient matrix size.
  odd-congruence-iwahori-pairs-have-uniform-linear-repair: that starts inside the congruence locus and is uniform in dimension and level; this globally captures every exact vertex pair at a fixed dimension, with constants allowed to depend on that dimension.
  iwahori-uniform-infinitesimal-rigidity: that is a uniform linear derivative estimate at congruence endpoints; this is a nonlinear global estimate over the whole fixed-dimensional modular representation variety.
---

**ESTABLISHED BOUNDED-DIMENSION SECTOR; NO DIMENSION-FREE CLAIM.**

For every integer \(d_0\geq 1\) there are constants
\(C_{d_0}<\infty\) and \(\alpha_{d_0}>0\) such that every exact pair
\(\pi=(\pi_+,\pi_-)\) of unitary representations of the two modular
vertices, of common dimension \(d\leq d_0\), satisfies
\[
 D(\pi)\leq C_{d_0}\operatorname{def}(\pi)^{\alpha_{d_0}}.       \tag{BDH1}
\]
The correcting compatible pair can be chosen in the **same dimension**.
It is the restriction of a finite-dimensional representation of
\(\operatorname{SL}_2(\mathbb Z[1/2])\), hence has finite image and factors
through an odd congruence quotient.

No congruence, finite-image, conductor, character, or closeness assumption is
placed on either input vertex representation. In particular (BDH1) includes
the continuous infinite-image part of the finite-dimensional dual of
\(\operatorname{SL}_2(\mathbb Z)\).

Consequently every countersequence to Dogon--Vigdorovich Question 1.4 must
have dimensions tending to infinity. More strongly, no subsequence of
bounded dimension can carry a positive global noncongruence-capture gap while
its Iwahori defect tends to zero.

The constants and exponent arise from a global semialgebraic Łojasiewicz
inequality on the fixed-\(d\) representation variety. This argument provides
no control as \(d\to\infty\); taking a maximum over finitely many dimensions
is the only uniformization used here. Thus the unrestricted question and the
nonhyperlinear-group root remain open.

DERIVATION
semialgebraic-lojasiewicz-captures-fixed-matrix-size

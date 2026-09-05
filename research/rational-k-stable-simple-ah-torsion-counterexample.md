---
rg: 2
id: rational-k-stable-simple-ah-torsion-counterexample
kind: claim
title: A simple unital monotracial AH algebra is rationally K-stable with integral stabilization kernel Z/2
distinct_from:
  stw59-independent-component-and-degree-one-obstructions: uses rationally acyclic real-projective bases and a torsion-safe fourth-power Euler identity; the earlier complex-projective towers have a free cokernel and fail rational K-stability.
artifacts:
  - research/artifacts/stw59-rational-k-stability-torsion-euler-tower-2026-09-05.md
  - research/artifacts/rational-ah-and-selfless-k-stability-proof-review-2026-09-05.md
---

There is a simple unital separable nuclear stably finite infinite-dimensional
AH algebra A with a unique tracial state such that A is rationally
K-stable and
\[
 \ker\bigl(U(A)/U_0(A)\longrightarrow K_1(A)\bigr)
 \cong\mathbb Z/2.
\]
Moreover M_2(A) is integrally K-stable. No identification of the whole
component group, or vanishing of K_1(A), is asserted.

The construction uses r_i=4*2^i,
X_i=(RP^2)^4 times product_(j<i) RP^(2r_j), and
E_i=1^4 direct sum direct sum_(j<i) L_(j+1)^(direct sum r_j).
Dense point-evaluation tails in the twisted unital maps
a -> pull(a) direct sum a(x_i) tensor 1_L make the limit simple.

Every E_i is four copies of a bundle. The integral Euler relation
reduces modulo two to a fourth power, which vanishes in top degree
because every positive-degree monomial in the initial (RP^2)^4
factor has zero fourth power. This handles every K^0 class, including
torsion classes. The top Z/2 obstruction persists under the actual maps.
Rational acyclicity and increasing ranks give rational stability of
all adjacent matrix maps in every positive degree.

This provides a negative answer to Vaidyanathan's AH extension
question, even in the simple unital compact-building-block class.
The accompanying proof is internally reviewed; this is not a claim
of external peer acceptance, formal verification, or publication priority.

ROUTES:

- rational-ah-fourth-power-euler-tower-proof

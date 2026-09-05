---
rg: 2
id: stw99-problem-lxi-properly-infinite-k1-injective
kind: claim
title: Properly infinite unital C*-algebras are K1-injective (STW Problem LXI, Blanchard-Rohde-Rordam)
root: true
artifacts:
  - research/artifacts/stw99-k1-kk-cluster-2026-08-30.md
  - research/artifacts/stw61-blanchard-preprint-firewall-2026-08-30.md
  - research/artifacts/stw61-free-envelope-compression-attack-2026-09-05.md
  - research/artifacts/stw61-mixed-corner-rotation-obstruction-2026-09-05.md
  - research/artifacts/stw61-alternating-conjugate-shift-obstruction-2026-09-05.md
  - research/artifacts/stw61-functional-letter-flip-obstruction-2026-09-05.md
  - research/artifacts/stw61-projective-finite-representation-obstruction-2026-09-05.md
  - research/artifacts/stw61-projective-mf-coefficient-obstruction-2026-09-05.md
  - research/artifacts/stw61-toeplitz-defect-bell-shift-test-2026-09-05.md
---

**Problem LXI of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Blanchard--Rohde--Rordam; implicitly Rordam's Crelle hypotheses;
Kirchberg's squeezing property was invented for it).  Are all properly
infinite unital C\*-algebras `K_1`-injective?  BRR reduce it to the
single algebra `O_∞ * O_∞` (full unital free product); properly
infinite algebras are always `K_1`-surjective (Cuntz).

## Literature false-positive firewall

Blanchard's arXiv:1606.04773v1 advertises
`T_2 *_[C] T_2` as a properly infinite non-`K_1`-injective algebra.  It does
not close this root. Proposition 2(5), Step 2 invokes a retraction
from a crossed product to its coefficient algebra by sending the
implementing unitary to 1. Covariance would force its nontrivial
dilation automorphism to be the identity. The attached firewall
records this exact obstruction and also corrects its earlier
overly broad criticism of the finite-stage passage in Step 1:
non-nullness of the same compatible witness at every stage would
suffice for non-nullness in the limit. STW v2 continues to state
LXI as open.

## Attempts

The free-envelope candidate `A_LIX * T2` has a stably null witness,
but its non-nullness remains unproved. The attached compression notes
exclude ordinary properly infinite tensor factors and several explicit
families of candidate contraction projections. The shift obstruction
proves `||[v,w p w*]||=1` for every finite alternating product of integer
powers of v and arbitrary Toeplitz-factor unitaries, and every nontrivial
Toeplitz projection p. General mixed unitaries remain outside this result.
The two-site flip argument further permits arbitrary repeated powers
of one continuous unitary function f(v), and any family sharing a
compatible antipodal pair. Independent functions without such a pair
are not covered by that proof.
The stronger theorem `stw61-finite-representation-maximal-commutator`
handles every mixed unitary over any coefficient subalgebra admitting
a finite-dimensional representation that detects both sides of the
projection. This includes every two-projection coefficient algebra.
It does not provide such a representation for the full Toeplitz algebra.
The extension `stw61-mf-coefficient-maximal-commutator` proves the
same exact norm-one obstruction for every mixed unitary over MF
coefficients, including UHF coefficients with no finite-dimensional
representations. More generally, a matrix-quotient homomorphism
detecting both complementary projections suffices. Genuine coordinate
unitary lifts and projective-space tests establish the quotient norm.
The full Toeplitz algebra admits no such unital homomorphism, so
the unrestricted properly infinite coefficient case remains open.
An explicit mixed Bell conjugate now tests that remaining setting:
its commutator norm is one in the universal free product and the
Toeplitz shift representation, but is `sqrt(3)/2` in the Cuntz
shift quotient. The conjugating unitary is constructed in the
original free product, including every Toeplitz defect term.
This shows exactly why a strict estimate in that properly infinite
quotient cannot establish the universal strict-commutator criterion.

* Szabo's January 2026 solution of KK-uniqueness
  (`stw99-problem-lxii-kk-uniqueness`) went AROUND this problem
  (Cuntz--Higson multiplier-algebra features), and STW note it does
  not touch LXI — so LXI is now decoupled from its main classical
  application and stands as pure non-stable K-theory.
* The `O_∞ * O_∞` reduction makes it a free-probability/K-theory
  hybrid: a unitary `u` in the free product, trivial in `K_1`
  (= trivial in each factor since `K_1(O_∞ * O_∞) = 0`), must be
  connected to `1`.  The free-product unitary group deformation
  technology (Brown--Dykema-type standard form arguments, and the
  homotopy analysis of `U(A*B)` by Thomsen) handles REDUCED free
  products with faithful states; `O_∞` has no trace, which is exactly
  why nothing transfers — the recorded gap is a homotopy analogue of
  Avitzour freeness for state-free full products.  Kirchberg's
  squeezing property is the only structural attack on record and its
  status for `O_∞ * O_∞` is open.

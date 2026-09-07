---
rg: 2
id: property-t-free-manuscript-results
kind: claim
title: Reprove the non-MF manuscript endpoints without Property T
root: true
goal: true
artifacts:
  - non_mf_groups_exist.tex
  - research/proposed-property-t-free-whitehead-proof-safe-prefix-audit.md
  - research/proposed-property-t-free-whitehead-proof-safe-prefix-route.md
  - research/finite-order-central-compression-defect-survives-mf-proof.md
  - research/polar-corner-descent-retains-relator-error-proof.md
---

**OPEN.**  Produce a replacement proof of the results advertised by
`non_mf_groups_exist.tex` in which Property `(T)` is absent from the proof,
not merely hidden behind a premise-free theorem.

The replacement must include the mathematical endpoints that remain after
removing the Kazhdan-specific intermediate language:

1. an explicit countable non-MF group, with a nontrivial element killed by
   every homomorphism to every norm matrix corona;
2. the full-MF-radical version for the binary-Leavitt group;
3. the basic MF-radical and MF-kernel-closure calculus;
4. functoriality, normal-generation saturation, full-kernel pullback, and
   universal factorization;
5. the explicit simplicity, defect, and prescribed-visible-quotient
   consequences used by the manuscript;
6. a two-generated finitely presented torsion-free acylindrically hyperbolic
   full-MF-radical group, all of whose nontrivial quotients again have full
   MF radical, with the printed Property-`(T)` clause deleted.

The final kernel-checked surface is

```text
GroupApproximation/Manuscript/OneSidedMFRadical/Unconditional.lean
```

and must have no declaration input standing for an unformalized literature
result.  Its proof dependency cone must not use a Property-`(T)` or Kazhdan
theorem.  In particular, a closed declaration obtained by instantiating
`HasKazhdanPropertyT` does **not** satisfy this claim.

The Kazhdan projection/order/transport statements in the current manuscript
are proof machinery, not endpoints to rename.  They must be removed from the
replacement argument and replaced by the finite-coordinate Property-`(T)`-free
mechanism that proves MF invisibility.

The torsion-free theorem is a second mathematical obligation.  It does not
follow from the binary-Leavitt collapse because the latter seed has torsion;
its current proof uses a normal Kazhdan subgroup at the load-bearing radical
inclusion.  The exact replacement target is
`property-t-free-torsion-free-full-mf-radical`.

## Attempts

The downstream radical calculus is already algebraic and independent of
Property `(T)`.  The load-bearing missing input is the concrete
binary-Leavitt MF collapse recorded at
`property-t-free-leavitt-full-mf-radical`, together with the independent
torsion-free input above.  Writing a theorem package whose new premises are
these open collapses would be conditional and would not settle this goal.

Two further Property-`(T)`-removal attempts are now fenced by explicit
finite-matrix calculations.

* `finite-order-central-compression-defect-survives-mf` constructs a
  three-generated MF norm-corona subgroup with a properly compressed infinite
  cyclic subgroup, an involution centralizing that subgroup, and a nontrivial
  central involutive compression defect represented by `-I`. Hence proper
  compression plus torsion, centrality, or macroscopic visibility does not
  replace the rigidity input.
* `polar-corner-descent-retains-relator-error` proves that polar correction on
  an `eta`-invariant corner changes a length-`ell` relator by at most
  `delta+ell(ell+1)eta^2/2`. A two-dimensional exact model realizes a
  quadratic leakage term. Thus a minimal-dimension descent needs a
  group-specific reconstruction which cancels inherited errors; generic
  compression and polar correction do not close the target.

Neither fence establishes that Property `(T)` is necessary for non-MF
existence. They locate two mechanisms which cannot by themselves provide the
requested proof.

The vector-energy alternative has also been tested with arbitrary fixed
polynomial right contexts. `finite-context-energy-certificate-iff-word-trivial`
proves that this entire class of universal positive-operator certificates
detects precisely words already equal to the identity in the presented
group. Its countermodel direction allows any finite collection of translated
relator tests and additive slack below two. Increasing the finite context
depth therefore cannot detect a nontrivial MF-radical element. The remaining
operator-norm estimate must supply global control; it does not follow from
these vector tests. This observation leaves the present goal open.

---
rg: 2
id: pcp-subroutes-to-both-hs-dehn-orientations-share-lin-barrier
kind: claim
title: The PCP sub-routes to the coRE HS-Dehn crux and the RE LCS compiler share one affine-LIN barrier
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  perfect-completeness-constant-soundness-lcs-compiler: that is the RE-orientation existence target (a computable LCS family with perfect commuting completeness on halting inputs and a constant matrix soundness gap); this is the structural statement that the coRE-orientation crux's PCP sub-route needs the same target, so the two orientations are not independent within the LCS approach.
  unsolvable-word-problem-group-with-computable-hs-dehn-modulus: that is the coRE-orientation existence crux for one fixed group; this does not construct any group and does not close it, but locates its only recorded area-beating mechanism inside the same obstruction as the RE compiler.
  selector-gated-equality-is-not-affine-pp-definable: that is the pp-definability fence itself, a statement about one relation; this is the claim that both HS-Dehn orientations' PCP sub-routes run into that fence.
---

**ESTABLISHED (structural).**  Consider the two orientations of the
computability route to `non-hyperlinear-group`:

* RE orientation, consumed by `re-oriented-lcs-compiler-gives-nonhyperlinear-group`,
  whose sole open input is `perfect-completeness-constant-soundness-lcs-compiler`:
  a computable machine-indexed family of **binary linear** constraint systems
  (`LIN` language) with perfect commuting completeness on halting inputs and a
  constant finite-dimensional soundness gap on nonhalting inputs.
* coRE orientation, `unsolvable-word-problem-group-with-computable-hs-dehn-modulus`
  (its consuming route `non-hyperlinear-from-computable-hs-dehn-modulus`).

Claim: the only area-beating mechanism recorded for the coRE crux is a PCP
sub-route that requires the RE compiler's target.  Concretely, along the
Taller--Vidick sub-route the coRE crux is reduced to
`perfect-completeness-constant-soundness-lcs-compiler`, so a solution of the
coRE crux by that sub-route solves the RE target too.

Consequently the coRE orientation is **not an independent second attempt**
within the LCS/PCP approach: both sub-routes are blocked at the same point,
the affine-`LIN` pp-definability barrier of
`selector-gated-equality-is-not-affine-pp-definable`.

## Argument

1. **The coRE crux beats area only through PCP soundness.**  Its own recorded
   attempts (area modulus, structural permanence, relator-preserving
   endomorphisms, abelian/cyclic distortion, Rips--(T) kernels) all either
   track the Dehn function or fail to create an unsolvable word problem.  The
   one recorded mechanism that supplies a length-control modulus strictly
   below area is Taller--Vidick soundness (`taller-vidick-lcs-re-hardness`)
   restricted to the `J = -1` spectral part of an approximate representation
   of a solution group: it gives `||J(U) - I||_2 <= 17 Def(U)`, linear length
   control for a length-one word whose area is unbounded in the machine.

2. **That mechanism needs perfect completeness in `LIN`.**  The linear
   length-control estimate of step 1 controls the marked word only where
   `J = 1` on the completeness side (else `perfect-lcs-gap-implies-nonhyperlinear`
   already closes the goal directly).  A computable binary-LCS family with
   `J = 1` on halting inputs and a constant nonhalting gap is exactly
   `perfect-completeness-constant-soundness-lcs-compiler` (`(PC1)`, `(PC2)`).

3. **Both are blocked at the same barrier.**  The published perfect-gap
   families (`culf-mastel-oracular-2csp-perfect-gap-family`) are nonaffine
   2-CSPs, and the Paddock--Slofstra Lemma 5.4 reductions compile a source
   relation into target language `LIN` only when it is pp-definable from
   `LIN`, i.e. affine; `selector-gated-equality-is-not-affine-pp-definable`
   shows the required conditional relation is not affine pp-definable.  So the
   perfect gap does not currently cross into `LIN` for either orientation.

## Scope, and what this does not say

* This does **not** close either crux, and does **not** claim the two cruxes
  are logically equivalent.  The coRE crux might still be solved by a
  mechanism outside the LCS/PCP approach (a direct group-theoretic
  construction of computable trivial-word length control beating area with no
  PCP inside).  No such mechanism is known, and the recorded non-PCP attempts
  are dead, but their deadness is not a proof of impossibility.
* The claim is exactly: *the PCP sub-route to the coRE crux requires the RE
  compiler's target, so the affine-`LIN` barrier is a single obstruction
  shared by the currently-live PCP attacks on both orientations.*  Effort
  spent crossing the affine barrier serves both; effort duplicating one
  orientation as a hedge against the other does not.

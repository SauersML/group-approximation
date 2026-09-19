---
rg: 2
id: unsolvable-word-problem-group-with-computable-hs-dehn-modulus
kind: claim
title: A finitely presented group with unsolvable word problem whose trivial words have length-controlled HS defect
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  hs-pcp-boone-compiler: that asks for a machine-indexed family of presentations each with one marked word and one-sided halting soundness, consumed through the recursion theorem; this asks for one fixed group, a bound for every trivial word, and no self-reference, and it is consumed through undecidability of the word problem.
  hyperlinear-hs-stable-is-residually-finite: that is a theorem about stable groups; this is an open existence claim whose hypothesis is strictly weaker than stability (no statement about nontrivial words or exact representations).
---

Exhibit a finitely presented group `G=<S|R>` such that

1. the word problem of `G` is unsolvable, and
2. `G` has computable HS length control: a computable `Phi(l,t)` with
   `Phi(l,t)->0` as `t->0^+` and `||w(U)-I||_2<=Phi(|w|,t)` for every
   trivial word `w` and every finite-dimensional unitary tuple `U` with
   `Def_R(U)<=t`.

By `hyperlinear-computable-hs-dehn-modulus-solvable-word-problem`
such a group is not hyperlinear.

The two conditions pull against each other only through area: by
`hs-dehn-modulus-bounded-by-dehn-function` the Dehn function always
supplies a modulus, and it is non-computable exactly under condition 1.
So the claim asks for a group in which the HS defect of trivial words is
controlled by something much smaller than their area.  Known sources of
such control are HS-stability with a computable modulus (which would make
the group a stable non-residually-finite group, itself unknown) and
structural permanence: free products and amalgams over finite subgroups
preserve computable length control, but do not create unsolvable word
problems.

**Relative form, which is the single-group version of the compiler.**
It suffices that condition 2 hold for the trivial words of a recursive set
`W` whose nontrivial part is not recursively enumerable.  For the Boone
group of a universal machine and `W` the halting commutators over all
inputs, this is `(HPB2)` made uniform over inputs of one machine instead
of over machines.

## Attempts

- **Area modulus.**  `Phi(l,t)=Dehn_G(l) t` always works and is
  non-computable exactly when the word problem is unsolvable; this is the
  attack that dies by definition and fixes the target as "beat area".
- **Stability.**  A computable HS-stability modulus gives length control,
  but every HS-stable group whose status is known is residually finite
  (`hyperlinear-hs-stable-is-residually-finite` forbids anything else among
  hyperlinear groups), so this attack needs a stable group outside the
  known classes, which is the Dogon--Vigdorovich and Steinberg lanes.
- **Permanence.**  Free products and amalgams over finite subgroups
  preserve computable length control (pinch subwords one at a time, each
  paying its own modulus; total length is conserved), and direct products
  pay at most a quadratic reordering term.  None of these operations
  creates an unsolvable word problem; Britton-style HNN extensions over
  distorted finitely generated subgroups do, and there the pinch rewrites
  a subgroup element across the amalgamation with unbounded length, which
  is exactly where the control is lost.  So the group must get its
  unsolvability from somewhere other than distorted amalgamation, or the
  rewriting across the amalgam must itself be length-controlled.
- **Relator-preserving endomorphisms.**  An endomorphism sending each
  relator to a conjugate of a relator transports trivial words with no
  loss, so a machine whose steps are such endomorphisms has free
  configuration transport.  But a halting word is a semantic coincidence
  (`Phi(c_0)=c_0`, or `[k,Phi(c_0)]=1`), not the image of a short trivial
  word, so free transport of trivial words does not control it.  This is
  the `(CC2)` semantic-transport gap of `hs-pcp-boone-compiler` restated.

- **Abelian distortion is dead.**
  `centralized-cyclic-distortion-hs-dehn-tracks-area` shows that when the
  distorted subgroup is cyclic the HS-Dehn modulus equals the Dehn function
  along tuples of defect tending to zero; the same drift model transplants
  to any halting subgroup distorted through a near-degenerate spectral
  direction.
- **Rips--(T) kernels transfer the problem to the quotient.**  For an
  Ollivier--Wise triple `N -> G -> Q` with `N` Kazhdan and
  `Gamma_Q = <G, k | [k, N]>`, property (T) pins `k` to the commutant of
  `U(N)` and the generators of `G` act on the multiplicity bundle over
  `Irr(N)` as an approximate representation of `Q`; the mark `[k, u]` is the
  defect of the trivial `Q`-word `u` there.  So the target for `Gamma_Q` is
  the target for `Q` (modulo robustness of the conjugation gap for
  approximate representations of `N`, itself open); the kernel's
  non-computable distortion is paid for by (T), the quotient's is not.
- **Where length control beating area is already a theorem.**  Taller--
  Vidick soundness (`taller-vidick-lcs-re-hardness`) says that on a
  nonhalting input every finite-dimensional strategy violates at least a
  `1/72` fraction of constraints; restricted to the `J = -1` spectral part
  of an approximate representation of the solution group this gives
  `||J(U) - I||_2 <= 17 Def(U)` with a constant independent of the
  machine.  Whenever `J = 1` in that solution group (if ever it is not,
  `perfect-lcs-gap-implies-nonhyperlinear` closes the goal), this is
  linear length control for a word of length one whose area is unbounded
  in the machine: PCP soundness is exactly the mechanism that beats area,
  by averaging over an expanding family of constraints instead of
  following one derivation.  The missing piece on that side is perfect
  completeness, not soundness.

**Falsification test.**  Any proposed modulus must be checked against the
one-dimensional and block-diagonal tuples first: for `U` the identity
tuple every word is at distance zero, so the test cases are tuples with
small but nonzero defect, e.g. the scalar near-models of
`cyclic-character-orbit-pressure-has-vanishing-hs-gap`.  A bound of the
form `C Area(w) Def(U)` is the area modulus and establishes nothing.

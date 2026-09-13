---
rg: 2
id: sp4-mod3-twisted-fibres-have-llp
kind: claim
title: The nontrivial mod-three twisted group C-star fibre of the symplectic lattice has the local lifting property
distinct_from:
  sp2g-z-full-c-star-algebra-has-llp: that is the untwisted fibre (the full group C*-algebra of Sp_4(Z)); this concerns the alpha- and alpha^2-twisted fibres of the Deligne triple cover, which have no finite-dimensional representations at all, so the RFD and Ioana--Spaas--Wiersma tool kits have no purchase on them in either direction.
  sp4-metaplectic-class-pointwise-coboundary-limit: that settled a cocycle-rigidity question about the mod-two metaplectic class; this is a lifting question about the mod-three twisted algebras, with no cocycle approximation involved.
---

OPEN CLAIM.  Let `alpha` be the `mu_3`-valued multiplier of a section of
Deligne's triple cover `1 -> Z/3 -> E_3 -> Sp_4(Z) -> 1`.  Then the twisted
group C-star algebra

```text
C^*(Sp_4(Z); alpha)                                             (TF3)
```

has Kirchberg's local lifting property.  By
`twisted-c-star-opposite-inverts-cocycle`, the `alpha^2` fibre is its opposite
and has LLP exactly when `(TF3)` does.  Thus only one twisted lifting question
remains, not two independent ones.

**Why it matters.**  `C^*(E_3)` decomposes as the finite direct sum of
its three central-character fibres `C^*(Sp_4(Z); alpha^j)`, `j = 0,1,2`
(central idempotents of the finite central `Z/3`), and LLP holds for a
finite direct sum iff it holds for every summand.  So this claim plus the
untwisted fibre `sp2g-z-full-c-star-algebra-has-llp` is exactly LLP of
`C^*(E_3)`, which by `llp-non-rf-kazhdan-group-is-non-hyperlinear` makes
the non-residually-finite Kazhdan group `E_3` non-hyperlinear — the
route `non-hyperlinear-from-e3-fibre-llp` — and by the equivalence
`deligne-sector-gap-is-exactly-nonhyperlinearity` simultaneously yields
the mod-three Maslov defect gap and the one-word central collapse of the
Deligne lane.  This is Fournier-Facio--Willett Question 1.12
(arXiv:2603.18456v2, p. 7, verbatim from the PDF): *let `Gamma` be a group
**with the (L)LP** and let `sigma in Z^2(Gamma; S^1)` be a normalized
`S^1`-valued 2-cocycle; does the twisted group C-star algebra
`C^*(Gamma; sigma)` have the (L)LP?*  For `Gamma = Sp_4(Z)` the hypothesis
of Q1.12 is itself the open untwisted fibre
`sp2g-z-full-c-star-algebra-has-llp`, so this is the sharpest live instance
in which that hypothesis is not gratuitous: a positive answer to Q1.12
**together with** the untwisted fibre gives this claim.  LLP of
`C^*(Sp_4(Z))` is not known in either direction (it is that node, open at
`g = 2`).

There is also a sharper trace-localized consequence which does not require
the untwisted fibre.  By `llp-makes-hyperlinear-traces-amenable`, LLP of
`A_alpha` would make every hyperlinear trace on it amenable.  But
`odd-maslov-twisted-fibres-have-no-amenable-trace` excludes amenable traces,
while Thom's central-corner criterion makes the canonical twisted trace
hyperlinear whenever `E_3` is hyperlinear.  Thus this claim **alone** forces
`E_3` non-hyperlinear through
`nonhyperlinear-from-odd-maslov-fibre-llp`; the untwisted
`sp2g-z-full-c-star-algebra-has-llp` gate is not part of that mouth.

## Attempts

- **No tool reaches this algebra in either direction.**  The twisted
  fibre has NO nonzero finite-dimensional representations
  (`deligne-triple-cover-fd-central-invisibility`), so they are as far
  from RFD as possible, the Ioana--Spaas--Wiersma finite-dimensional
  realizability mechanism is vacuous, and the
  Fournier-Facio--Willett positive machinery (LLP + RFD, property FD)
  does not apply.  Nothing in the recorded literature computes any
  lifting property of a twisted algebra of a higher-rank lattice.
- **The exact metaplectic finite model does not bridge the odd orbit.**
  `finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres` proves
  that every generator-equivariant finite tensor/Morita shift carries an
  exact projective coefficient whose class is the difference of the two
  twists.  Metaplectic finite quotients supply only classes `0` and `1/2`;
  an odd-fibre bridge would require a forbidden exact `1/3` or `1/6`
  coefficient.  Hence the half-shift retract cannot be iterated or Morita-
  amplified into a proof of `(TF3)`.
- **A non-equivariant retract must be genuinely nonfaithful.**
  `odd-maslov-ucp-retract-must-hide-generator-defect` applies Schwarz to any
  split ucp pair from the odd fibre into a matrix amplification of the
  untwisted or metaplectic fibre.  Every canonical generator's two
  multiplicative defects are positive and killed by the retraction.  At
  least one is nonzero, or multiplicative-domain plus an even-fibre finite
  representation would contradict Deligne invisibility.  Thus faithful
  retractions, conditional expectations, order-zero embeddings, and
  generator-unitary complete-order models are all ruled out.  An arbitrary
  nonfaithful ucp retract remains possible in principle, but must hide its
  nonmultiplicativity in a positive kernel.
- **That positive-kernel escape is formally real.**
  `split-ucp-matrix-retracts-can-hide-defect-in-a-boundary-ideal` constructs
  an explicit finite-dimensional complete-order embedding `M_2 -> M_4` with
  a split ucp retraction.  A unitary generator acquires a nonzero positive
  multiplicative defect, and the retraction kills it; even on the C-star
  algebra generated by the range the retraction is the quotient by that
  boundary ideal.  Therefore matrix amplification, complete-order embedding,
  and exact ucp splitting do not force the faithfulness needed by the prior
  no-go.  Closing the non-equivariant retract lane requires a Maslov-specific
  obstruction to such a boundary ideal, not a generic operator-system lemma.
- **Simplicity and central-fibre origin do not supply that obstruction.**
  In `v4-twisted-fibre-has-a-nonfaithful-untwisted-matrix-retract`, the
  nondegenerate twisted fibre of `V_4` is the simple algebra `M_2`, the
  untwisted fibre is the finite/RFD algebra `C^4`, and nevertheless the first
  is a split ucp complete-order retract of `M_2(C^4)` with its generator
  defect hidden in a scalar boundary ideal.  Hence the analogous formal
  features of the Maslov central-fibre decomposition cannot close the lane.
  The exact point absent from the countermodel is canonical covariance of
  generator images; some Maslov-specific weakened covariance condition is
  the surviving target.
- **The covariance threshold is now sharp.**  Exact covariance modulo a
  scalar cochain is impossible for an odd-to-even split ucp retract:
  `scalar-covariant-odd-even-ucp-retract-is-impossible` uses the split norm
  equality to make every scalar unimodular and hence every generator image
  multiplicative.  But arbitrary matrix-valued homogeneous covariance is
  still too weak.  `matrix-homogeneous-ucp-retracts-can-hide-defect` puts a
  positive-definite Fourier multiplier in a hidden diagonal block, producing
  exactly coaction-equivariant split ucp retracts with positive generator
  defect.  Approximate scalar covariance likewise has no formal finite-stage
  rigidity.  The remaining possible input is therefore a quantitative
  Maslov-specific modulus upgrading matrix homogeneous coefficients toward a
  scalar/projective coefficient; that is not supplied by ucp theory alone.
- **Bounded homogeneous coefficient size has a Maslov gap.**
  `odd-maslov-homogeneous-coefficients-have-a-fixed-size-defect-gap` uses the
  odd difference multiplier, projective GNS compression, and Deligne
  invisibility to prove that every fixed coefficient size `n` pays a
  positive total generator defect `kappa_n`.  Thus fixed-size compactness
  alone says that the same-twist countermodel could escape only by taking
  coefficient size to infinity.  The next item closes that apparent escape.
- **The unbounded coefficient escape is also closed for scalarization.**
  `odd-maslov-homogeneous-coefficients-have-a-uniform-folner-gap` identifies
  the coefficient defect with normalized finite-rank boundary in the
  projective GNS representation.  A hypothetical sequence with defect
  tending to zero, even with matrix size tending to infinity, direct-sums to
  one forbidden odd-Maslov Folner representation.  Hence one constant
  `kappa_hom>0` works in all coefficient sizes.  The surviving homogeneous
  retract lane cannot perturb its hidden boundary toward a scalar/projective
  Morita bridge: any retract must kill a macroscopic positive coefficient
  boundary.  Such a genuinely nonfaithful macroscopic-boundary retract is
  not ruled out for arbitrary nonhomogeneous embeddings, but the proposed
  quantitative scalarization gate is now closed negatively.
- **Exact matrix homogeneity is itself impossible for a split retract.**
  `odd-maslov-homogeneous-split-ucp-retract-is-impossible` strengthens the
  preceding defect gap.  If the embedding has exact homogeneous form
  `i(u_g)=C_g tensor u_g`, then Schwarz equality puts every generator image
  in the multiplicative domain of the arbitrary ucp left inverse.  The
  support of its canonical coefficient state reduces all `C_g` and carries
  a nonzero finite-dimensional projective representation with the odd
  difference multiplier, contradicting Deligne invisibility.  No
  homogeneity of the retraction is used, and a macroscopic killed boundary
  does not escape.  A surviving split-retract proof must therefore break
  exact homogeneity of the embedding itself.
- **The Connes-embeddability of the fibres is also live.**  Thom's
  criterion (Lemma 3.4, `thom-central-corner-criterion`) makes
  hyperlinearity of `E_3` equivalent to Connes-embeddability of all
  three twisted von Neumann fibres; if the alpha-fibre were shown non-CE
  the goal would close by a different mouth (the trace route), so BOTH
  the C*-lifting and the von Neumann embedding questions for `(TF3)` are
  goal-relevant and unrecorded.  The embedding side carries a second
  major stake: the twisted von Neumann fibre inherits property (T) from
  the Kazhdan group (Connes--Jones through the alpha-regular
  representation).  Non-Connes-embeddable property-(T) `II_1` factors
  are already known abstractly: Chifan--Drimbe--Ioana's embedding-
  universality theorem (Adv. Math. 417 (2023), arXiv:2205.07442,
  Theorem A), combined with the negative solution of CEP, supplies such
  factors.  What remains open here is the much more structured endpoint:
  a non-CE twisted group factor of this concrete arithmetic Kazhdan group.
  Such a fibre would make the finite central extension `E_3`
  nonhyperlinear and hence give a non-CE property-(T) **group** factor;
  CE fibres for all three characters are exactly hyperlinearity of `E_3`
  (`deligne-sector-gap-is-exactly-nonhyperlinearity`).  The peers'
  `maslov-bounded-block-sector-gap` already fences the would-be
  hyperlinear models of the twisted sectors to decompositions in which
  asymptotically all block dimensions are unbounded.
- **Having no finite-dimensional representation is not evidence against
  LLP.**  FFW's own discussion immediately after Q1.12 (same page, verified
  from the PDF) gives the residual-finite-dimensionality analogue of this
  question a NEGATIVE answer through `Gamma = Z^2`: for a suitable cocycle
  `sigma`, `C^*(Z^2; sigma)` is the irrational rotation algebra
  `A_theta`, which is simple and infinite-dimensional and so has no nonzero
  finite-dimensional representation.  Yet `A_theta` is nuclear and
  therefore has the LLP.  Hence `deligne-triple-cover-fd-central-invisibility`
  (the twisted fibre has no fd representation) makes the RFD and
  Ioana--Spaas--Wiersma finite-dimensional machinery inapplicable but is by
  itself no obstruction to `(TF3)`; fd-invisibility cuts only against
  fd-representation tools, in either direction.  The gap between `A_theta`
  and `A_alpha` is exactly non-nuclearity: `A_alpha` has C-star property
  (T) and no amenable trace, so the nuclear route by which `A_theta` gets
  LLP is closed and gives `(TF3)` no help.
- **Twisted subgroup permanence fences `(TF3)`, but has no ammunition.**
  For `H <= Gamma` the canonical conditional expectation
  `C^*(Gamma; alpha) -> C^*(H; alpha|_H)` that projects onto the
  `H`-supported projective generators is ucp, so by Kirchberg's tensor
  characterization `LLP <=> (x)_max B(l^2) = (x)_min B(l^2)` the LLP
  descends: `(TF3)` implies LLP of `C^*(H; alpha|_H)` for every subgroup
  `H`.  This is the twisted counterpart of the subgroup audit that refutes
  `sp2g-z-full-c-star-algebra-has-llp` for `g >= 3`.  Here it is inert: a
  refutation this way would need a subgroup `H <= Sp_4(Z)` with
  `C^*(H; alpha|_H)` KNOWN to fail LLP, and the untwisted affine/parabolic
  audit (`sp4-contains-no-isw-affine-subgroup`,
  `isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals`) shows
  `Sp_4(Z)` contains no recorded LLP-failing subgroup, and no
  twisted-algebra LLP failure is published for any group.  So the fence is
  real but symmetric, and `(TF3)` stays OPEN in both directions.

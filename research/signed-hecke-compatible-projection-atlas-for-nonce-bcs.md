---
rg: 2
id: signed-hecke-compatible-projection-atlas-for-nonce-bcs
kind: claim
title: A no-CE-trace BCS has a compatible algebraic projection atlas in one signed group corner
artifacts:
  - research/artifacts/signed-hecke-direct-trace-promotion-2026-08-20.md
distinct_from:
  character-rigid-signed-bcs-quotient: that asks for a quotient from a unique-trace corner onto the BCS algebra and must preserve character rigidity; this asks for a homomorphism in the opposite direction, from the BCS algebra into the canonical positive corner, so no source-trace classification is needed.
  bcs-projective-kernel-phase-compilation: that tries to compress each predicate to one projective scalar phase; this retains complete context projection partitions and asks for their shared marginals to agree.
---

Fix the finite BCS `B` supplied by `mipstar-bcs-tracial-nonru-exists`. Find a
finitely presented group `Gamma`, a finite subgroup `K<=Gamma`, and an
irreducible type `rho in Irr(K)` with `dim(rho)>1`, such that for
`q=z_rho` the corner `qC[Gamma]q` contains algebraic projections

```text
p_(c,a),       c a context, a in R_c,                         (SHA1)
```

satisfying the compatible projection-atlas equations `(BPA1)--(BPA3)`.
Equivalently, construct one unital star homomorphism

```text
A(B) -> qC[Gamma]q.                                          (SHA2)
```

The construction should give each projection and transport arrow by a finite
group-ring expression. Piecewise transport as in `(PGT1)--(PGT4)` is allowed;
no uniqueness of trace, quotient map, asymptotic decoder, or prescribed BCS
trace is required.

There is now a strictly weaker alternative endpoint.
`rowwise-hecke-crt-certificate-for-nonce-bcs` does not require `(BPA3)` in one
common corner or a homomorphism of the whole BCS algebra.  It asks only that
each predicate and consistency equality hold on its own high-mass right-ideal
mask.  The context PVMs and the shared-variable involutions themselves remain
global, so the rowwise freedom cannot be used to change the BCS semantics.

## Attempts

- **Independent masks weaken the endpoint without weakening the game gap.**
  `independent-row-masks-transfer-bcs-gap-to-ambient-identity` bounds the
  unconditional `G=I` BCS energy from separately masked rows.  Therefore the
  exact weighted deficit condition `D_row<Delta` already forces a canonical
  matrix obstruction.  The resulting Hecke-CRT route is not a solution of
  this stronger common-corner claim; it is a separate path around it.

- The trivial finite-subgroup average is impossible by
  `augmentation-one-corner-retains-a-character`.
- `every-boolean-predicate-has-a-character-free-finite-type-block` constructs
  an exact seed partition for every context separately. The missing equation
  is precisely the cross-context marginal identity `(BPA3)` in one common
  corner.
- **Common local type is solved.**
  `all-bcs-contexts-share-one-hyperoctahedral-signed-type` puts every context
  in a copy of one hyperoctahedral group and one irreducible type, with equal
  corner trace and an explicit common number of coordinate atoms.  No
  dimension- or trace-balancing bridge remains at the local level.
- **Shared-variable rank balancing is solved.**
  `tracial-bcs-has-rational-balanced-hyperoctahedral-atlas` rationalizes the
  local marginals of any source trace and clears denominators.  Every overlap
  then admits an explicit sign-preserving coordinate permutation in the same
  `K_D` type.  These edge matchings cannot be made globally coherent:
  `coherent-balanced-context-permutations-would-give-a-ce-trace` would turn
  such a gauge into a finite-dimensional BCS representation.
- **Unique-spin Heisenberg packets do not make arbitrary marginals literal.**
  `heisenberg-subgroup-cuts-are-affine-stabilizer-flats` classifies every
  projection exposed by one Pauli spectral cut or one subgroup-character
  condition in the `J=-1` spin block.  Such a projection is an affine
  stabilizer flat of trace `2^(-r)`; Fourier uniqueness says that identifying
  two such cuts identifies the same affine subgroup and character.  Thus a
  common `J` and literal shared Pauli subgroup data cannot identify a general
  coarse marginal (already a three-of-eight atom union is impossible).  A
  successful Heisenberg refinement still needs the non-scalar group-algebra
  projection transport requested by `(SHA1)--(SHA2)`.
- **One literal word cannot selectively transport the first Boolean-sum
  witness.**  `three-of-eight-transport-forces-chart-conjugacy` uses the fact
  that every Fourier coefficient of a three-atom sum is a nonzero sum of
  three signs.  In any ambient group, even infinite and non-residually-finite,
  a group element conjugating one such projection to another must conjugate
  the complete rank-three context subgroups and hence affinely permute all
  eight atoms.  This does identify the coarse projections, but only by the
  already-matricial full sheet transport.  The live escape is therefore a
  genuinely additive finite-support corner unitary whose cancellations move
  the coarse marginal without normalizing the context algebra.
- Single compressed group elements stay in the corner-unit stabilizer.
  `piecewise-group-transport-gives-corner-unitaries` proves that two or more
  group translates can repair domains and ranges exactly, but it does not
  choose a globally compatible finite transport quiver.
- Ordinary free products or Bass--Serre amalgams preserve independent context
  choices and therefore do not force `(BPA3)`. A successful construction
  needs nontrivial finite holonomy among the context partitions.
- Allowing an arbitrary finite linear combination instead of one Hecke
  literal does not create a new individual packet capacity.
  `bass-serre-algebraic-projections-are-stably-vertex-induced` proves that
  every matrix projection over the group algebra of a finite graph of finite
  groups is stably Murray--von Neumann equivalent to a finite direct sum of
  vertex-group projections.  This does not rule out the atlas: individual
  stable equivalences need not be simultaneously compatible.  It localizes
  the only possible escape to relative placement/holonomy of the induced
  packets rather than the projective class of any one context atom.
- The first simultaneous exception has only a finite-packet relative index.
  `nand-triangle-relative-k1-is-a-finite-packet-index` computes the minimal
  S4 NAND cell after stable packet straightening.  For atom algebra `C^3`
  inside separator commutant `M_2(C) directSum C`, the determinant `K_1` map
  `(a,b,c) |-> (ab,c)` is surjective, while the six-term relative group is
  the single atom-difference lattice `Z(1,-1,0)`.  The sheet swap represents
  that oriented difference; the returned central minus has zero relative
  boundary.  Both occur in an exact three-dimensional signed-permutation
  model.  Any successful atlas must therefore couple several such indices
  through a genuinely global relative-position relation; one odd NAND phase
  cell cannot be the nonmatricial obstruction.
- The smallest coupling of two cycle indices is still finite-packet data.
  `two-nand-triangles-have-only-free-finite-packet-indices` treats both ways
  two minimal NAND triangles can overlap.  Sharing a full edge identifies
  the two private variables and the two `Z` indices, leaving one free `Z`;
  sharing one variable leaves independent row and column differences `Z^2`.
  The two phase words equal the same `J`, so their ratio and product are
  trivial.  Explicit signed-permutation models exist in dimensions three
  and six respectively.  Thus neither torsion nor a new central class begins
  at the two-cycle level.
- In fact the entire pure sheet-transport program is matricial.
  `finite-sheet-transport-networks-are-exactly-matricial` puts every finite
  rank-balanced coordinate set on one `D`-point basis and realizes every
  edge bijection and every cycle return in `(C_2)^D semidirect S_D`.  The
  monodromy coinvariant lattice is free on its finite orbits, so adding more
  cycles creates neither torsion nor a nonmatricial phase.  Retaining this
  monodromy gives only covariance between context copies, not the literal
  marginal equality `(BPA3)`; coherifying it would give the forbidden finite-
  dimensional BCS model.  The live block-escaping target must therefore use
  a genuinely nontransport relation, not a larger finite permutation atlas.
- **Literal local contexts are completely solved, but finite Bass--Serre
  compatibility is impossible.**
  `common-corner-literal-contexts-stop-at-bass-serre` tensors all selected
  predicate types behind one projection and makes every marginal a compressed
  literal involution.  It also proves that any compatible completion inside a
  finite graph of finite groups would pull a CE canonical corner trace back to
  the no-CE BCS.  Thus no more elaborate finite amalgamation can close the
  overlap equations.
- **Returning to the finite root block is impossible.**
  `root-block-piecewise-transport-cannot-host-nonce-bcs` shows that if all
  transported context projections lie in `q_D C[K_D]q_D`, the atlas is a
  finite-dimensional BCS model and creates a CE trace.  Thus the live target
  is more specific: place isomorphic local `M_D` blocks as distinct algebraic
  subalgebras of the infinite corner and identify only their shared signed
  marginals.
- **Finite groupoids do not enlarge the overlap syntax.**
  `finite-groupoid-diagonals-have-only-classical-gluing` computes the strict
  limit of the context coarse diagonals: its sheets are exactly compatible
  families of allowed context answers, hence exactly classical solutions.
  A connected object corner kills all non-root object identities; retaining
  finitely many objects leaves one common coordinate diagonal.  Groupoid
  transports avoid the classical limit only by retaining cycle holonomy, in
  which case they give covariance rather than `(BPA3)`.  Non-diagonal
  isotropy-corner elements return to the signed-Hecke chord, while a graph of
  finite isotropy groups is virtually free and is already excluded.
- **Lin's static synchronous gap has the same atlas boundary.**
  `lin-gap-wrappers-retain-oracular-atlas-holonomy` audits the properties
  actually provided by arXiv:2510.07162, Theorem 6.15.  For a preserved
  perfect oracular strategy, every sampled pair has the joint allowed-answer
  PVM `P_x^a P_y^b`, whose marginals are the question PVMs.  This is exactly
  the multi-answer version of `(BPA1)--(BPA3)`.  Conditional linearity and
  balance concern sampling, while anchoring adds deterministic leaves and
  repetition contains an anchored slice isomorphic to the old diagram.
  Uniform answers and the external coordinate symmetry therefore solve no
  cross-context equality.  A source-specific escape must use the full
  Pauli-PCP incidence through a genuinely nontransport chord.
- **Narrow live cell.**  The route
  `signed-hecke-balanced-holonomy-route` leaves only
  `signed-hecke-block-escaping-cycle-holonomy`: realize the residual chord
  transports by finite-support corner unitaries which preserve the one shared
  sign but move the remaining matrix block outside the finite root algebra.
- **Finite-support localization makes the remaining cell load-bearing.**
  `finite-support-corner-localizes-obstruction`
  shows that any completed atlas already lives in the group generated by the
  finite supports of its corner and generator images, and that this finitely
  generated support group is itself nonhyperlinear.  Thus an ambient Higman
  wrapper, unrelated property-`(T)` block, or free phase decoration cannot
  repair the chord after the fact.  Some chord-support extension must be the
  first point at which the cumulative support subgroup becomes
  nonhyperlinear.  The cycle holonomy is therefore genuinely load-bearing,
  not an artifact of insisting on one particular finite root model.
- **An embedding theorem is strictly harder than this target.**
  `injective-group-corner-map-requires-faithful-trace` shows that an
  injective map into any algebraic group corner forces a faithful trace on
  the source algebra.  The fixed MIP-star BCS input does not supply
  faithfulness of its universal algebra, whereas the trace-promotion theorem
  needs no injectivity at all.  Passing to a tracial null quotient preserves
  the all-traces-non-CE property but can lose finite presentation.  Thus replacing
  `(SHA2)` by a general algebra-embedding theorem adds a new tracial-radical
  problem and gives no stronger conclusion.
- **Finite presentation of the host can be postponed.**
  `effective-corner-host-higman-promotion` combines finite-support
  localization with the effective Higman theorem.  It is enough to build the
  atlas by effective finite group-ring expressions in a recursively
  presented group.  Their support subgroup is finitely generated,
  recursively presented, and already nonhyperlinear, so it embeds in an
  explicit finitely presented nonhyperlinear group.  This removes finite
  presentation from the chord-construction burden, but does not remove the
  chord: its finite support must still carry the obstruction.

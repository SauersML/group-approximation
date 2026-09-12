---
rg: 2
id: finite-relator-reservoir-repairs-every-fd-packet
kind: claim
title: One finite relator reservoir repairs every finite-dimensional representation packet of the triangle extension
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
distinct_from:
  triangle-relator-extension-admits-local-ucp-sections: that asserts existence of exact ucp lifts into `C^*(G_0)`; this asserts a bounded word depth for corrections tested only against finite packets of finite-dimensional representations, is strictly stronger (a ucp section's correction lies in the closed ideal, not in any finite relator span), and can fail while that target holds.
  finite-reservoir-compactness-lifts-ucp-repairs: that is the general established compactness lemma with the reservoir as a hypothesis; this is the open assertion that a specific reservoir, spanned by the native relator words at bounded depth, satisfies that hypothesis at the Kac--Moody triangles.
  triangle-kernel-relators-charge-authenticated-corner-leakage: that is the established analytic estimate showing the native relators charge the leakage of an authenticated corner once a common carrier exists; this is the missing coefficient statement -- which relator words, at what depth -- and supplies no inequality.
  km-triangle-local-bimodules-have-finite-nonflat-models: that exhibits finite-dimensional models in which the local bimodule data is nonflat; this asserts that corrections at bounded relator depth repair every such model, so the two are compatible and their conjunction is the interesting case.
---

**OPEN CLAIM.**  There is an infinite finitely presented simple Kazhdan
Kac--Moody lattice `Lambda` with a triangle-of-finite-groups presentation as in
`triangle-relator-extension-admits-local-ucp-sections`, with

```text
A := C^*(G_0),   G_0 = P_12 *_(P_2) P_23,   q : A ->> C^*(Lambda),
N = ker(P_1 *_(P_0) P_3 ->> P_13) free of rank r with basis
n_1,...,n_r,   I_N = ker q,
```

such that the following holds.  For a finite symmetric `W = W^(-1) subset G_0`
put the **relator reservoir**

```text
L_W := span_C { u_a (u_n - 1) u_b :
                a,b in W,  n in {n_1^(+-1),...,n_r^(+-1)} }
       subset I_N,                                           (RR1)
```

a finite-dimensional self-adjoint subspace of `I_N`.  Then for every
finite-dimensional operator system `E subset C^*(Lambda)` there exist a unital
self-adjoint linear section `t:E->A` of `q` and a finite symmetric
`W=W(E) subset G_0` such that for **every** finite collection `R` of
finite-dimensional representations of `A` there is a linear

```text
d_R : E -> L_(W)   with   rho o (t+d_R) ucp for all rho in R. (RR2)
```

(`q(t+d_R)=id_E` is automatic, since `L_W subset I_N`.)

By `finite-reservoir-compactness-lifts-ucp-repairs` this gives exact local ucp
sections, hence -- via
`local-ucp-sections-from-finite-relator-reservoir` and
`triangle-colimit-llp-reduces-to-relator-local-splitting` -- LLP of
`C^*(Lambda)`, closing `non-rf-kazhdan-group-with-llp-full-c-star-algebra` and
the goal.

**Stakes both ways.**  If it is refuted for every candidate `Lambda` and every
reservoir, the local-splitting hole is not thereby closed negatively -- the
target survives, because a ucp section's correction need only lie in the
*closed* ideal.  What a refutation would buy is a first quantitative
obstruction of the right type: the correcting directions demanded by growing
packets escape every fixed finite relator span, which by
`fd-representation-packets-never-obstruct-ucp-sections` is exactly the shape any
genuine failure of local splitting must take.

## Attempts

- **No proof by a uniform relator-Laplacian inverse is possible.**
  `km-triangle-relator-kernel-has-no-relative-gap` proves that the normal
  kernel pair `(G_0,K)` lacks relative property `(T)`.  Otherwise quotient
  property `(T)` would force the infinite virtually free group `G_0` itself
  to be Kazhdan.  Hence every fixed finite relator reservoir admits unitary
  representations with almost invariant unit vectors, no `K`-fixed vector,
  and arbitrarily small reservoir energy.  In particular `(RR2)` cannot be
  proved by applying a dimension-uniform Moore--Penrose/Poincare inverse to a
  finite relator sum of squares.  This does not refute `(RR2)`: its finite
  packets and correction coefficients vary, and it asks for cp repair rather
  than a coercive estimate.  A proof must exploit that noncoercive
  packet-dependent geometry.
- **The low-spectrum obstruction already occurs in finite-dimensional full-support packets.**
  `km-triangle-relative-gap-failure-has-fd-full-support-witnesses` uses RFD of
  the virtually free ambient algebra to approximate the relative-gap witnesses
  by genuine finite-dimensional representations, then removes their
  `K`-fixed summand.  The resulting packets have ideal support `z_rho=1` and
  arbitrarily small Rayleigh energy for every prescribed finite relator
  reservoir.  Thus the spectral no-go cannot be evaded by restricting `(RR2)`
  to finite-dimensional packets.  Conversely, these packets exist
  independently of whether `(RR2)` or local splitting holds, so their mere
  existence is not a counterexample to the Choi-slice intersection.
- **Central-support dilution is not the source of the soft spectrum.**
  `native-relator-soft-modes-persist-in-simple-ideal-blocks` selects one
  irreducible summand from the full-support packet while retaining arbitrarily
  small combined relator Rayleigh energy.  On that summand

  ```text
  rho(I_N)=M_d,
  ```

  so the ideal support is the identity in a simple matrix algebra.  Hence no
  support-projection estimate, even restricted to irreducible packets, can
  give the uniform angle needed for `(RR2)`.  A successful argument must use
  the particular Choi discrepancy and positivity, rather than only maximal
  native-ideal support.
- **The reservoir cannot act only by independent inner gauges on the tree
  faces.**  In the explicit `(3,3,4)` Kac--Moody triangle,
  `kernel-inner-tree-face-balancing-collapses` proves that conjugating the two
  canonical tree-face embeddings by arbitrary relator-kernel elements
  collapses, through Bass--Serre edge rigidity, to one common conjugation; the
  kernel-cycle Gram obstruction then survives unchanged.  Thus a successful
  `d_R` cannot merely encode two facewise inner gauges.  It must make at least
  one corrected tree-face restriction genuinely nonmultiplicative while
  preserving compatibility on the shared `P_2` algebra.  This is the
  sharpest live positive subproblem inside `(RR2)`.
- **Nor can it hide a more general group-word-valued multiplicative gauge.**
  `group-word-tree-face-balancing-collapses` proves, under the checkable
  maximal-finite/self-normalizer/edge-centralizer conditions `(GW1)--(GW3)`,
  that every star-homomorphic tree-face lift taking canonical finite-group
  unitaries to group unitaries is already an inner kernel gauge.  Hence the
  preceding no-go is not evaded by choosing unrelated word-valued copies of
  the two finite vertex groups.  A successful `d_R` must create genuinely
  non-group-unitary operator values or destroy multiplicativity on at least
  one tree face.  This does not refute `(RR2)`, which allows exactly that
  operator-algebraic behavior.
- **That operator-algebraic behavior cannot shrink away with the packet.**
  `tree-face-balance-pays-word-or-multiplicative-defect` gives the explicit
  dichotomy
  `max_V(mu_V+3 gamma_V)>=min{sqrt(2),6/L^2}` for every ucp right inverse on
  the three-face system of the `(3,3,4)` candidate, where `L` is one fixed
  nontrivial closing-face kernel-relator length.  Here `mu_V` is the tree-face
  multiplication defect and `gamma_V` is distance to all group-unitary lifts
  with the correct quotient image.  Thus a proposed sequence of packet repairs
  cannot converge through increasingly accurate group-word gauges; one face
  retains a macroscopic nonmultiplicative or non-word component.  `(RR2)`
  remains open because its finite reservoir may still support exactly such a
  component.
- **The nonmultiplicative branch is genuine Stinespring leakage.**
  `tree-face-balance-pays-stinespring-loss-or-word-distance` replaces `mu_V`
  by the diagonal Kadison--Schwarz slack `sigma_V`.  With
  `delta_L=min{sqrt(2),6/L^2}`, some tree face obeys
  `sigma_V>=delta_L^2/4` or `gamma_V>=delta_L/6`.  In a Stinespring dilation,
  `sigma_V` is the squared operator norm with which a face unitary exits the
  Stinespring corner.  Hence a positive reservoir proof cannot be a Newton
  correction converging to a word-valued multiplicative face: it must retain
  a fixed off-corner or a fixed non-word component.  This still does not
  refute `(RR2)`, which may deliberately store its correction in that
  off-corner.
- **The packetwise statement is already a theorem; only uniformity in the
  packet is open.**  Fix a finite packet `R` and put `rho=(+)_(rho in R) rho`,
  a finite-dimensional representation.  Then `rho(I_N)` is a
  finite-dimensional subspace of `rho(A)`, and the algebraic two-sided ideal
  generated by the `u_(n_j)-1` is dense in `I_N`, so
  `rho(L_W) = rho(I_N)` for every sufficiently large finite symmetric `W`.
  Feeding that into
  `fd-representation-packets-never-obstruct-ucp-sections` (whose Step 3 only
  needs preimages of prescribed elements of `rho(I_N)`) yields `d_R` valued in
  `L_(W_R)`.  So `(RR2)` holds with `W` depending on `R`, and the entire open
  content is that `W` may be chosen once and for all.  This also shows the
  conjecture is not vacuous and not obviously false: it fails only if the
  minimal admissible depth `W_R` diverges as the packet grows.
- **Closed-ideal density does not upgrade a local lift to one finite
  reservoir.**  For a fixed `t` and `L_W`, `(RR2)` is equivalent to the
  existence of one ucp section `s=t+d` with `d:E->L_W`: the forward
  implication is exactly
  `finite-reservoir-compactness-lifts-ucp-repairs`, and the reverse
  implication uses the same `d` for every packet.  Thus starting from an
  arbitrary local ucp section only gives a correction `s-t:E->I_N` in the
  **closed** ideal.  Approximating its finite-dimensional range by the
  algebraic relator ideal produces maps at vanishing distance from the ucp
  cone, as in `exhausting-ideal-reservoirs-have-lift-or-quotient-separator`,
  but does not make any approximant ucp.  The tempting strictification by an
  additive cp kernel map is impossible: if `k:E->I_N` is positive and
  `(s+k)(1)=1`, then `k(1)=0`, hence `||k||=||k(1)||=0` and `k=0`.  This is a
  no-go only for the density-plus-positive-slack shortcut, not for `(RR2)`;
  a successful finite-reservoir correction is necessarily a signed
  unit-zero direction whose sum with `t` satisfies the coupled Choi
  inequalities.
- **What a proof has to bound, and what it does not.**  The argument above
  needs `rho(L_W) = rho(I_N)`, which certainly fails uniformly in `R` (a large
  representation has a large image of the ideal).  But that is far more than
  is required: only the *specific* discrepancy `psi - rho o t` of that route
  has to be hit, not all of `rho(I_N)`.  So the real target is a word-depth
  bound for one prescribed finite-dimensional discrepancy, uniform over
  packets -- a statement about how far into the relator ideal the *correction*
  must reach, not about how much of the ideal a representation sees.  No
  attempt here yet produces such a bound; this is where the work is.
- **The non-inner Kraus problem is now one exact ideal-block Choi slice.**
  `finite-packet-triangle-repair-is-ideal-block-choi-feasibility` uses minimal
  almost periodicity of the simple Kac--Moody quotient.  For a packet sum
  `rho`, put `B=rho(A)`, `J=rho(I_N)`, and let `z` be the unit of `J`.  The
  quotient block `B/J` is forced to be the augmentation character, so a repair
  in `L_W` exists exactly when

  ```text
  [z rho o t + rho_* L_sa(E,L_W)] intersect UCP_z(E,J) != empty.
  ```

  This is a finite-dimensional necessary-and-sufficient feasibility problem,
  not an inner-gauge ansatz.  It removes every quotient-side variable and
  locates all genuinely non-inner Kraus freedom in the ideal block.  The open
  uniform-depth task is precisely to make these affine Choi slices nonempty
  for every packet using one `W`; no argument here proves that.
- **An exhausting sequence has a sharp lift-versus-separator endpoint.**
  `exhausting-ideal-reservoirs-have-lift-or-quotient-separator` defines the
  distance from `t+L(E,L_W)` to the global ucp cone.  If those distances tend
  to zero as the reservoirs exhaust `I_N`, point-norm lifting closure already
  gives the desired exact local section, even if no one finite depth works.
  If the distances stay bounded below, Hahn--Banach functionals annihilating
  deeper and deeper reservoirs have a tail cluster point which annihilates
  all of `I_N` and strictly separates `id_E` from every liftable ucp map in the
  quotient.  For packet Choi certificates the analogous ultralimit is valid
  only after pullback by `s |-> z_rho rho o s` and only with a uniform
  normalized gap; moving packet dimensions and support projections otherwise
  destroy compactness.  Hence failure of one uniform depth is not itself a
  negative result: vanishing depth-dependent gaps are exactly compatible with
  a positive local lift.
- **Why the two recorded no-gos do not apply.**  The window/Folner no-go
  `position-window-ucp-sections-collapse-to-folner-vectors` kills corrections
  indexed by group positions with a right-translation reindexing; `(RR1)` is
  not of that shape -- its directions are relator words, and the collapse
  under the trivial character sends every `u_a(u_n-1)u_b` to `0`, so the
  argument degenerates and produces no Folner vector.  The counterpacket
  fence `km-triangle-local-bimodules-have-finite-nonflat-models` refutes
  inferring flatness from local regular bimodule tables; `(RR2)` never infers
  flatness, it injects the missing face relators explicitly.
- **Where it connects to the established analytic half.**
  `triangle-kernel-relators-charge-authenticated-corner-leakage` proves the
  native relators `u_(n_j)-1` charge the complete leakage of an authenticated
  positive-density corner, and states in its own last paragraph that what
  remains is "the finite coefficient identity".  `(RR1)`-`(RR2)` is a candidate
  formulation of exactly that identity, with compactness doing the
  infinite-representation bookkeeping.  Making the two meet -- exhibiting the
  reservoir coefficients as the ones that pay the charge -- is the concrete
  first task, and it is not done.
- **Deferred sub-question: group-word systems versus all finite-dimensional
  systems.**  The natural attack is on group-word systems
  `E_F = span{u_g : g in F}`, `F subset Lambda` finite, where `W(E_F)` should
  be read off the word ball carrying `F`.  Local liftability quantifies over
  *all* finite-dimensional operator systems of the quotient, and reducing the
  general case to a dense directed family of group-word systems is not a
  recorded step here (perturbing an arbitrary finite-dimensional `E` into a
  group-word system changes the complete order structure, and no cb-distance
  transfer principle for ucp liftability is recorded).  The claim is therefore
  stated for arbitrary `E`; a solver who proves only the group-word case will
  have to supply that reduction or restate the target.

---
rg: 2
id: projective-commutant-transfer-for-arithmetic-pair
kind: claim
title: Projective commutant transfer with a dimension-free trace-square modulus for the arithmetic pair
distinct_from:
  relative-commutant-collapse-for-sl2-pair: that demands the commutator converge to 1; this demands only that it become SCALAR, which already contradicts the regular trace, and its witness is the full-rank inner superoperator rather than a possibly sparse commutant vector.
  no-exact-quasi-regular-leak: that is the minimal single-configuration core (one exact profile refuted); this is the uniform local inequality that would refute it with room to spare, shaped for spectral-gap and sum-of-squares methods.
  hnn-over-codense-kazhdan-subgroup-not-hyperlinear: that consumes flexible HS-stability of the base group and corrects the representation; this transfers only a scalar-commutator property, so the scalar 2-cocycle obstructions that block ordinary stability are quotiented away before the problem starts.
  finite-regular-adjoint-retains-full-conductor: that is the exact finite-group calculation showing projectivization preserves dyadic depth; this asks for the remaining approximate arithmetic transfer inequality.
---

Let `(Lambda, Gamma) = (SL_n(Z), SL_n(Z[1/p]))` with finite generating
set `S` of `Lambda`, fix `h in Gamma \ Lambda`, and fix a finite
presentation of `Gamma`.  For `U, V in U(d)` write the **trace-square
energy** `e(U,V) = 1 - |tr_d([U,V])|^2`, where `tr_d` is the normalized
trace.  The claim (PRCC): there are `K` and a modulus `eta(delta) -> 0`
such that for every `delta`-approximate finite-dimensional unitary
representation `rho` of the presentation and every `U in U(d)`,

```text
e(U, rho(h))  <=  K sum_(c in S) e(U, rho(c)) + eta(delta).   (PRT1)
```

Equivalently, in inner superoperators: since

```text
|| Ad(W) - I ||_(2, d^2)^2 = 2 - 2 |tr_d(W)|^2,              (PRT2)
```

`(PRT1)` says `Ad`-centrality for `Lambda` transfers to `Ad`-centrality
for `Gamma`, with dimension-free constants.  The conclusion is strictly
weaker than commutant collapse: it only forces `[U, rho(h)]` to be
asymptotically scalar.  That is already fatal to a regular microstate,
because a scalar unitary commutator has trace modulus `1` while the
regular trace of the nontrivial commutator word is `0`.

**Exact case: now a QUANTITATIVE theorem on both pairs.**  For exact
finite-dimensional `rho` the inequality `(PRT1)` holds with zero
defect term and explicit dimension-free constants:
`sl2-exact-projective-transfer-via-doubled-squeeze` proves
`e(U, rho(h)) <= (4/kappa^2) E_C(U)` for the SL_2 pair at
`(tau)`-only strength (the Ad-doubling squeeze — phases cancel inside
`Ad`, no perfectness needed), and
`exact-projective-codensity-has-a-uniform-trace-square-gap` covers the
perfect/(T) pairs for `n >= 3`.  What remains open in this claim is
exactly the APPROXIMATE-representation form: the passage from the
exact variety to `delta`-representations, i.e. the outlier sector.

## Attempts

- **Adjoint-lift exactification is sufficient and strictly narrower than
  full group stability.**  Put `beta_rho(x)=Ad(rho(x))` on the Hilbert space
  `M_d`.  If `rho` has presentation defect `delta`, then every defining
  relator satisfies

  ```text
  ||beta_rho(r)-1||_2^2
    =2-2|tr(rho(r))|^2
    <=2||rho(r)-1||_2^2,                              (PRT3)
  ```

  so `beta_rho` has defect at most `sqrt(2) delta`.

  Suppose one could prove the following special exactification statement:
  there is `theta(delta)->0` such that every such **adjoint lift** is within
  `theta(delta)` on the fixed generator packet of an exact unitary
  representation

  ```text
  pi:Gamma -> U(M_d).
  ```

  No assertion about exactifying `rho` itself is needed.  Apply the established
  exact projective transfer theorem to `pi` and the unitary `T=Ad(U)` on
  `M_d`.  For unitaries `V,W`, the group commutators with fixed `T` obey

  ```text
  ||[T,V]-[T,W]||_2 <=2||V-W||_2,
  ```

  and hence their trace-square energies differ by at most
  `4||V-W||_2`.  Moreover, for `beta_rho(g)=Ad(rho(g))`,

  ```text
  tr_(d^2)([T,beta_rho(g)])=|tr_d([U,rho(g)])|^2.
  ```

  Therefore, writing `e_g=1-|tr_d([U,rho(g)])|^2`, the exact transfer for
  `pi`, finite word telescoping from the generator packet to `S union {h}`,
  and

  ```text
  e_g <= 1-(1-e_g)^2 <=2e_g
  ```

  give

  ```text
  e_h <= 2K sum_(c in S)e_c + C theta(sqrt(2)delta),    (PRT4)
  ```

  for a fixed `C`.  Thus exactification of the special adjoint lifts alone
  proves `(PRT1)`; full Hilbert--Schmidt stability of `Gamma` is stronger
  than necessary.

- **The adjoint functor removes scalar phase but does not remove the
  two-primary conductor (exact special-adjoint leak).**  Let `Q` be any
  finite group and let `lambda_Q` be its left regular representation on
  `ell^2(Q)`.  On the Hilbert--Schmidt space, with matrix units indexed by
  `Q x Q`,

  ```text
  Ad(lambda_Q(g)) E_(x,y) = E_(gx,gy).                       (PRT5)
  ```

  The diagonal left-action on `Q x Q` has `|Q|` free orbits, indexed by
  `x^(-1)y`.  Consequently there is an exact representation isomorphism

  ```text
  Ad(lambda_Q)  ~=  |Q| lambda_Q.                            (PRT6)
  ```

  In particular `Ad(lambda_Q)` is faithful, and for every `g != 1`,

  ```text
  tr_(|Q|^2)(Ad(lambda_Q(g)))=0,
  ||Ad(lambda_Q(g))-1||_2=sqrt(2).                           (PRT7)
  ```

  Apply this to `Q_a=SL_3(Z/2^a Z)`.  For every `a>b>=1`, the reduction
  kernel `ker(Q_a -> Q_b)` contains a nonidentity elementary matrix (for
  example `e_12(2^b)`), and `(PRT7)` shows that its image under
  `Ad(lambda_(Q_a))` remains at the maximal regular distance from the
  identity.  Thus the adjoint lift does not factor through `Q_b`; its exact
  dyadic conductor is still `2^a`.  In particular the sharp depth-two
  leakage isolated by
  `two-adic-tower-format-of-surviving-lambda-exact-enemy` survives passage
  to adjoints unchanged on regular congruence blocks.

  This rules out the hoped-for shortcut "projectivize, then the even tower
  disappears."  Adjoint lifting kills only scalar cocycles.  A proof of the
  special exactification used in `(PRT4)` must still use the approximate
  denominator-generator relations to synchronize or contract the dyadic
  conductor; it cannot follow from an algebraic conductor drop under `Ad`.
  Scope: `(PRT6)` is an exact no-go for conductor factorization.  By itself
  it is not a fixed-generator quantitative obstruction to being close to a
  shallower representation, because a word exhibiting a deep kernel element
  may have length growing with `a`.

- **PTS4 identifies why property (T) does not supply that exactification.**
  For `n>=3`, `(PTS4)` in
  `projective-trace-square-transfer-for-sl3-pair` turns small projective
  subgroup energy into ordinary almost-invariance of `U` under
  `rho(SL_n(Z))`, with error `O(sqrt(q)+delta)`.  But the operators
  `beta_rho(c)` are only an almost representation.  The Kazhdan projection
  estimate applies to a genuine unitary representation and therefore cannot
  be invoked before the special exactification above.  Defect quarantine also
  does not fix this: its large corner need not be invariant, so compressed
  adjoint maps acquire uncontrolled leakage products.  Current exact
  co-density then becomes usable only *after* the missing adjoint
  exactification.

  This is not a formal consequence of perfectness, subgroup property (T),
  and equality of exact finite-dimensional images.  The established
  `exact-codensity-does-not-imply-matricial-rcc` gives a non-arithmetic
  hyperlinear product pair with all three properties and a maximal
  ultraproduct leak.  It does not refute arithmetic adjoint exactification,
  but proves that any such theorem must use the denominator-generator
  relations of `SL_n(Z[1/p])`, rather than only the exact subgroup data.

- **Exact co-density alone cannot cross the approximation wall.**
  `exact-codensity-does-not-imply-matricial-rcc` gives the unconditional
  pair `SL_3(Z) < SL_3(Z) x A_fin`: every exact finite-dimensional
  representation has equal subgroup and ambient images, yet the canonical
  hyperlinear regular model has a maximal relative-commutant/projective
  energy leak from the `A_fin` factor. Thus the exact theorem above cannot
  be promoted by compactness, perfectness, or subgroup property (T) alone;
  any proof here must use the arithmetic coupling to the denominator
  generator.

- **The involution-only qualitative form is NOT a smaller wall.**
  `trace-zero-involution-projective-transfer-equals-rcc` proves by the
  explicit dilation `v=[[0,U],[U*,0]]` that every positive-energy
  relative-commutant leak yields a trace-zero self-adjoint involution leak,
  retaining the dimension-free gap
  `Phi(epsilon)=1-((1+sqrt(1-epsilon))/2)^2`.  Combined with perfectness,
  qualitative PRCC restricted to trace-zero involutions is already full
  relative-commutant collapse.  Therefore the fact that the arithmetic lamp
  generator `c` is an involution does not itself simplify this claim.  The
  only honest narrower target must also consume a JOINT native lamp relation,
  such as `[c,h c h^-1]=1`, or the full commuting-orbit moment packet.

- **How much of the projective slack is real (2026-08-21 analysis).**
  If `[U, rho(c)]` is asymptotically scalar for every `c`, the scalars
  form a character `lambda : Lambda -> T` in the ultraproduct limit.
  For `n >= 3`, `SL_n(Z)` is perfect, so `lambda = 1` and projective
  centrality collapses to EXACT centrality in the limit: the
  ultraproduct form of full `(PRT1)` is not weaker than the collapse
  for `Lambda`-central elements.  For `n = 2`,
  `Lambda^(ab) = Z/12`, so `lambda` has order dividing `12` and `U` is
  exactly central for the finite-index kernel `Lambda_0 = ker lambda`,
  which is still commensurated with the same Schlichting completion —
  the whole Hecke formalism relativizes, and the twisted enemies are
  characters of the finitely many `mu_12`-twisted carriers (finite
  central extensions of the HNN, exactly the
  asymptotically-projective format of the DV central-extension route).
  CONSEQUENCE: the genuine content of this claim is its QUANTITATIVE
  finite-dimensional threshold form — for the goal it suffices that no
  `Lambda`-central `U` keeps `e(U, rho(h)) >= epsilon_0` while the
  right side of `(PRT1)` vanishes, since the exact-leak enemy sits at
  the maximal value `e = 1`.  The one-shell threshold version is
  exactly what `exact-leak-refuted-by-projective-transfer` consumes,
  and its enemy-side number is pinned by
  `single-hecke-average-isometry-for-lambda-central-unitaries`
  (`||S(k)||_2^2 = 1/4 + 1/(4L)` on the exact profile).
- **Why projectivization changes the difficulty class.**  The known
  obstructions to HS-stability of higher-rank groups are generated by
  scalar 2-cocycles (Deligne-type central extensions, isolated
  characters): they live exactly in the kernel of `Ad`.  And the
  sparse-outlier failure mode of linear spectral-gap arguments cannot
  occur here: the transported object `Ad(U)` has full normalized rank,
  so the target contradiction is `0` versus `sqrt(2)` in superoperator
  HS norm, not a vanishing rank fraction.
- **Nonlinear fixed-point formulation.**  The witness ranges over the
  compact algebraic manifold `PU(d) subset U(d^2)`, not over arbitrary
  vectors.  The needed estimate is a uniform Lojasiewicz/Kazhdan
  modulus for the conjugation action of `Lambda` on `PU(d)` relative
  to its projective fixed variety, split as usual into a near sector
  (Hessian/Newton, matching `iwahori-newton-closes-near-sector`
  architecture) and a far sector (packet energy floor).
- **Numerical probe on odd quotients (2026-08-21,
  `experiments/prt1_threshold_probe.py`,
  `experiments/prt1-threshold-probe.json`).**  Riemannian ascent on the
  regularized ratio `E_h/(E_C + delta)` over `U(d)` for the regular
  representations of `SL_2(Z/3)`, `SL_2(Z/5)` with multiplicities
  `N = 1, 2, 4` (`d` up to `240`, restarts per config): the best ratio
  found anywhere is `2.64` (at `m=3, N=1`, an interior point
  `E_h = 0.45`, `E_C = 0.16`), and every attempt to push `E_h` to its
  cap `1` dragged `E_C` to its MAXIMUM `2` — the exact-leak signature
  (`E_h = 1`, `E_C ~ 0`) was never approached, and the ratio does not
  grow with multiplicity or level.  Evidence for a linear `(PRT1)`
  with small `K` on the odd-congruence sector, in agreement with
  `odd-congruence-vertex-sector-admits-no-exact-leak`.  Scope honesty:
  exact quotient probes can NEVER see the even sector — `h` has no
  image mod `2^k` and exact representations of `Gamma` exist only at
  odd levels — so the probe confirms the theorem's regime and
  reconfirms that the enemy is a strictly non-exact phenomenon.
- **Constrained modulus probe (2026-08-21,
  `experiments/prt1_modulus_probe.py`,
  `experiments/prt1-modulus-probe.json`).**  Maximizing `E_h` subject
  to `E_C <= eps` from perturbed on-variety starts gives, at level
  `m = 3`: `sup E_h = 0.073` at `E_C = 0.024` (`eps = 0.016`) and
  `sup E_h = 0.213` at `E_C = 0.071` (`eps = 0.064`) — the SAME ratio
  `E_h / E_C ~ 3.0` at both scales, i.e. a LINEAR modulus, and the
  values for multiplicities `N = 1` and `N = 2` agree to four digits:
  the measured escape mode is dimension-free.  Numerology worth a
  conjecture: `K ~ 3 = [Lambda : Lambda cap h Lambda h^(-1)]`, the
  Hecke shell size — the extremal escape appears to spread its energy
  uniformly over the edge cosets, suggesting the sharp `(PRT1)`
  constant is exactly the shell index.  (The `m = 5` run was
  under-converged at its restart budget and is not evidence either
  way.)  This gives the SOS search below a concrete target: certify
  `E_h <= 3 E_C` plus defect terms.
- **SOS certificate formulation.**  `e(U,V)` is a degree-four trace
  polynomial; `(PRT1)` is a trace-positivity statement over the
  presentation ideal.  A rational dimension-free sum-of-squares
  certificate would prove it for every `d` at once and is falsifiable
  cheaply on congruence quotients — a concrete search target that does
  not ask any solver to discover the whole proof.
- **WARNING: the standard tracial hierarchy is provably unsound for
  this target (2026-08-21, transferring
  `tracial-npa-cannot-separate-canonical-trace`).**  The enemy
  configuration exists in the genuine tracial von Neumann model
  `L(H)` with ZERO presentation defect and `e(U, rho(c)) = 0`,
  `e(U, rho(h)) = 1` (recorded in `no-exact-quasi-regular-leak`), so
  its truncated tracial moments are feasible at every level of a
  standard tracial NPA/Lasserre hierarchy; every sound dual from
  that hierarchy is therefore nonnegative on it and cannot certify
  `(PRT1)`, whose content is matrix-only.  Any SOS campaign here
  must use a genuinely matricial (dimension-sensitive) proof system
  from the start — same lesson as the radius-nine lane; a standard
  tracial solver run would produce either infeasibility noise or an
  unsound dual, and its cost is wasted.
- **Falsification gates.**  Connes embeddability of the coset
  Bernoulli action
  (`coset-bernoulli-ce-refutes-relative-commutant-collapse`) refutes
  `(PRT1)` too: its witness has commutator of trace `0`, hence
  genuinely non-scalar energy `1` against `e(U, rho(c)) = 0`.  So PRCC
  sits strictly between the minimal exact-leak core and full collapse,
  and shares their producer gate.  The odd-congruence exclusion
  (`odd-congruence-vertex-sector-admits-no-exact-leak`) applies
  verbatim: any failure of `(PRT1)` along microstates is pinned to the
  even-level/non-congruence vertex sector, i.e. the two-adic solenoid
  wall of `far-sector-is-solenoid-measure-rigidity`.
- **Uniform odd-correctable projective modulus.**
  `sl3-odd-correctable-sector-has-uniform-projective-modulus` upgrades the
  established odd-congruence commutant collapse to arbitrary projective
  witnesses.  If the ambient defect, subgroup projective energy, and
  distance of the `SL_3(Z)` restriction to an exact congruence
  representation of level prime to `p` all tend to zero, then projective
  energy at `h` tends to zero with a uniform (not presently linear) modulus.
  The proof uses perfectness in the ultraproduct and requires no canonical
  trace.  Hence every fixed-gap failure of `(PRT1)` is now rigorously confined
  to exactifications whose levels are divisible by the denominator prime
  (including mixed levels), or to lattice tuples uniformly far from every
  exact representation.  For `p=2`, no purely odd correctable far sector
  remains; this does not yet bound the two-primary mass in a mixed level.
- **A fixed far gap forces positive denominator-primary mass.**
  `fixed-projective-gap-forces-primary-congruence-mass` closes the mass
  loophole left by the preceding item.  For any exact correction `sigma` of
  the lattice tuple, split its irreducibles by minimal congruence conductor
  and let `m` be the normalized dimension of the positive `p`-conductor
  part.  Replacing that part by trivial blocks gives a wholly coprime exact
  representation at generator cost at most `2 sqrt(m)`.  Hence

  ```text
  e_h <= eta_odd(delta+xi+E_Lambda+2 sqrt(m)).
  ```

  Every fixed-gap projective enemy with the other errors vanishing therefore
  has `liminf m>0`.  What remains is not a vanishing primary spectator but a
  positive primary mass that may spread over unbounded conductor depth; the
  Folner-atlas fence shows why a separate arithmetic coherence/contraction
  input is still necessary.
- **The genuine congruence branching still has Folner depth marginals.**
  `regular-congruence-depth-mixtures-remain-folner` tests the most immediate
  weighted-shift rescue on actual arithmetic blocks.  In
  `Reg(SL_3(Z/p^a))`, minimal-conductor bands form a geometric tail with
  ratio `p^(-8)`.  Arbitrary rational top-level weights are realizable by
  integer regular-block multiplicities, so resolving a wide triangular
  top-level profile into genuine conductor bands merely convolves it with
  this geometric kernel.  Fixed one- and two-depth translation variation
  still tends to zero, the largest band atom tends to zero, and shifting the
  window to infinity gives the canonical lattice character locally.  Thus
  neither the `p^8` branching dimensions nor canonical normalization yields
  a one-dimensional depth boundary.  The remaining payment must see the
  joint parahoric branch labels, mixed-root coherence, or the global
  building PVM; this construction does not supply those denominator
  intertwiners and is not a full countermodel.
- **Even all six forty-two-branch charts remain amenable if histories can
  fold through a finite fiber.**
  `six-parahoric-finite-fiber-folds-remain-amenable` keeps every local label
  from `native-sl3-edge-parahoric-has-index-forty-two`, not only the depth
  marginal.  If the chart transitions act on `Z^2 times F` by the six
  coweight translations and arbitrary permutations of a finite
  multiplicity fiber, coweight boxes times the whole fiber have boundary
  `O(1/N)` simultaneously for all `252` labelled moves.  Local inverse,
  link, triangle, and Weyl-holonomy constraints on the fiber permutations
  do not change the estimate.  Hence the fixed building gap becomes
  available only after proving that branch histories cannot recycle in this
  way and instead form distinct atoms of one global PVM.  This pins the next
  non-marginal arithmetic gate to cross-chart Gram collision/deck-cocycle
  faithfulness, not to another weighted conductor inequality.
- **Five cross-chart saturation scalars are necessary and sufficient for
  one native shell PVM.**
  `five-parahoric-overlap-saturations-give-global-shell-pvm` observes that
  the six Weyl charts `C/D_w` canonically parameterize the same Hecke sphere
  `C h C/C`.  Choose one root chart and compare each other chart to it under
  this canonical bijection.  The aggregate deficit on one star edge is half
  the sum of the `42` squared projection distances, hence is determined by
  `42` cross traces.  The exact identity

  ```text
  total chart-to-root movement^2=2 sum_(five edges) Delta_w
  ```

  shows that vanishing of the five scalars gives literal global labeling,
  with a dimension-free approximate version.  Five links are minimal since
  fewer cannot connect six charts and a disconnected component retains an
  independent multiplicity conjugation.  The open arithmetic statement is
  now sharply finite: bound these five deficits by mixed-root energy and
  first-exit mass.  No further PVM authentication theorem is required.
- **The fixed shell Laplacian cannot prove even the first saturation.**
  `two-equivariant-shell-pvms-have-independent-coordinate-escape` uses the
  diagonal action of `C` on `Omega times Omega`.  The two coordinate PVMs
  are complete, exactly covariant under the same actor, and have zero
  lattice mixed-root and first-exit energy, yet their corresponding-atom
  deficit is exactly `41/42`.  Tensoring with deep regular congruence blocks
  makes the lattice character canonical locally without changing the
  deficit.  Hence finite shell spectral gap only reaches the full orbital
  commutant; a denominator-generator incidence must select the diagonal
  orbit from its off-diagonal orbitals.  This countermodel does not extend
  to the ambient arithmetic group and therefore identifies, rather than
  refutes, the remaining simple-neighbor inequality.
- **Scope boundary: the uniform vertex-outlier sector remains separate.**
  The conductor, parahoric-chart, and five-saturation reductions all begin
  after the `SL_3(Z)` restriction is close to an exact congruence
  representation.  They do not address approximate lattice tuples uniformly
  far from every exact finite-dimensional representation.  Full PRCC still
  needs either a canonical-character correction theorem for at least one
  vertex or an independent argument excluding that outlier sector; no shell
  inequality should be advertised as closing it.
- **Raw denominator incidence selects the diagonal orbital sector exactly.**
  `raw-denominator-incidence-kills-off-diagonal-shell-orbit` chooses the two
  fixed section words `a_i,b_i` representing each of the same `42` Hecke
  vertices.  They satisfy `a_i=b_i d_i` for fixed `d_i in C`; hence their
  conjugates of the native `C`-central base projection have total mismatch
  `O(delta^2)`.  On the independent-coordinate escape the resulting
  square-function is exactly `2(1-R_diag)`, so zero incidence confines the
  carrier to the trace-`1/42` diagonal and the off-diagonal mass pays in
  full.  The raw word estimate itself is complete and Weyl-uniform.
- **Pointwise decoded-to-raw proximity is impossible by trace capacity.**
  `balanced-raw-lamp-orbit-cannot-approximate-shell-pvm` corrects the first
  proposed interface after the raw incidence lemma.  Forty-two raw lamp
  conjugates each have trace `1/2` (or `1/4` for a positive two-lamp atom),
  while a partial shell PVM has total trace at most one.  Therefore the sum
  of squared decoded-to-raw distances is at least `20` (respectively
  `19/2`), even at exact defect zero.  The valid next target is nonlinear:
  decode mutually orthogonal cylinder/character atoms from the JOINT raw
  lamp algebra and tie their covariance to the denominator section words.
  First exits may control loss of those atoms; they cannot make individual
  balanced lamps into a PVM.
- **The uniformly noncorrectable lattice sector is now a separate node.**
  `sl3-noncorrectable-lambda-sector-has-no-projective-leak` records
  the exact complementary assertion required for full PRCC.  None of the
  conductor, parahoric, shell, or raw-incidence arguments proves it; they
  all operate after a lattice correction is available.
- **The native forty-two raw lamps are not one Boolean packet.**
  `fixed-commuting-lamps-have-robust-fourier-atoms` gives the exact proposed
  decoder under its true hypothesis: for `k` commuting involutions the
  `2^k` Fourier products are an orthogonal PVM, their traces are the finite
  Fourier transform of the lamp moments, and transported atoms obey the
  dimension-free bound

  ```text
  ||vE_epsilon v* - E'_(sigma epsilon)||_2^2
  <=(k/4) sum_i ||v u_i v* - u'_(sigma i)||_2^2.
  ```

  But `native-forty-two-shell-has-a-noncommuting-pair` shows that the native
  `42`-point Hecke shell fails the hypothesis at zero defect.  The labels
  `hC` and `h^(-1)C` lie in the same shell but are nonadjacent in the orbital
  graph; in the exact graph-wreath regular model their lamp commutator has
  squared 2-norm `2`.  Moreover `h` sends `hC` to `h^2C` outside the shell,
  so denominator covariance enlarges the coordinate window rather than
  normalizing a fixed finite algebra.  The remaining correctable-sector
  target must therefore force missing nonedge commutators on a positive
  carrier or solve global overlapping-clique/window coherence.  This does
  not touch the separate uniformly noncorrectable lattice sector.
- **No bounded overlapping-shell atlas propagates the missing
  commutators.**  `every-fixed-hecke-window-retains-graph-product-nonedges`
  extends the preceding exact model to every fixed finite union of Weyl and
  denominator shells.  Each genuine clique has its exact equidistributed
  Fourier PVM, and these PVMs satisfy all marginal identities on overlaps;
  all actor transports are also exact.  Yet the induced lamp subgroup is
  still the right-angled Coxeter special subgroup.  For the persistent
  nonedge `x=hC`, `y=h^(-1)C`, even cutting by a positive cylinder atom `e`
  from any clique in their common link leaves

  ```text
  ||e(c_xc_y-c_yc_x)||_2^2=2 tau(e),
  ||e[P_x,P_y]_add||_2^2=tau(e)/8.
  ```

  Thus expansion or chordality of the clique-cover nerve controls only
  agreement of already shared coordinates; it cannot create a missing
  commutation relation.  A fixed family also yields only bounded rank
  pressure.  This closes the bounded-shell version of the nonlinear target:
  the next mechanism must use diverging windows/global coset-action
  coherence or genuinely new finite-dimensional-only incidence.  The
  uniformly noncorrectable lattice sector remains separate.
- **Projective far-defect formula (now a theorem).**  Established as
  `projective-far-defect-formula`: doubling the adjoint representation
  cancels the phases (`U otimes conj(U)` is exactly `Lambda`-fixed),
  the Hecke/Howe--Moore splitting reruns verbatim, the far projective
  energy is the single scalar `1 - s_proj` with `s_proj =
  ||E_2(|U><U|)||_HS^2`, the extreme value `s_proj = 1` forces exact
  centrality for `n >= 3` by perfectness, and the doubled lazy Hecke
  average contracts onto `E_2` at the same rate `delta_0`.  Through
  `sl3-collapse-from-projective-transfer` the `SL_3` instance of this
  claim now also implies the full collapse `(RC3)`, so the projective
  lane and the exact lane converge at higher rank.

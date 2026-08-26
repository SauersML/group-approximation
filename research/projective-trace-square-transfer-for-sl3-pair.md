---
rg: 2
id: projective-trace-square-transfer-for-sl3-pair
kind: claim
title: Projective trace-square transfer for the co-dense SL3 arithmetic pair
distinct_from:
  relative-commutant-collapse-for-sl2-pair: that forces an actual subgroup-central unitary into the ambient commutant; this asks only that its commutator with the one ambient generator become scalar in normalized Hilbert--Schmidt norm.
  no-spherical-leak-in-matrix-ultraproducts: that excludes every nontrivial spherical component and is equivalent to full relative-commutant collapse; this permits a leak whenever its ambient commutator is scalar, because scalarity already suffices for the HNN trace contradiction.
  no-exact-quasi-regular-leak: that excludes only the exact HNN coefficient profile and contains no quantitative transfer inequality; this proposes a dimension-free projective energy inequality for all approximate representations of the fixed arithmetic presentation, with no trace-profile restriction.
---

Let

```text
C = SL_3(Z),
A = SL_3(Z[1/2]) = <C,h>,
h = diag(2,1,1/2).
```

Fix finite presentation relators for `A` and a finite generating set `S_C`
of `C`.  There are a constant `K<infinity` and a modulus `eta(delta)->0`
such that every finite-dimensional unitary assignment `rho` with presentation
defect at most `delta`, and every unitary `U` of the same matrix size, satisfy

```text
1-|tr([U,rho(h)])|^2
 <= K sum_(c in S_C) (1-|tr([U,rho(c)])|^2) + eta(delta).       (PTS1)
```

Equivalently, after passing to inner superoperators,

```text
||[Ad(U),Ad(rho(h))]||_2^2
 <= K sum_(c in S_C) ||[Ad(U),Ad(rho(c))]||_2^2 + 2 eta(delta), (PTS2)
```

because for every unitary `W in U(d)`, with normalized trace and normalized
Hilbert--Schmidt norm on `M_(d^2)`,

```text
||Ad(W)-I||_2^2 = 2-2|tr(W)|^2.                               (PTS3)
```

The claim is projective: `(PTS1)` concludes that `[U,rho(h)]` is close to
*some scalar*, not necessarily to `1`.  This phase quotient is exactly the
weakening consumed by the HNN marked word.

## Attempts

- **The full raw rank-one coboundary packet still has an exact leak.**
  `rank-one-self-commutator-coboundary-packet-has-s3-leak` strengthens the
  earlier derived-identity countermodel. In the regular representation of
  `S_3`, take `U=X=Y=(12)`, `H=(23)`, and `C=1`. Then `U` centralizes all
  three lattice-word variables, `Z=HYH^*=(13)`, the literal denominator
  decomposition `H=XZXC` holds, and the literal target coboundary
  `W=[U,H]` is a nonidentity three-cycle, hence has normalized trace zero.
  So retaining the original coboundary and decomposition data does not
  improve the rank-one attack. The first omitted arithmetic datum is the
  common-root additivity `X=x(1)^2`, `Y=y(1)^(-2)`,
  `C=x(1)^(-1)y(1)x(1)^(-1)` together with its cross-root gluing; the
  countermodel's transposition `X` has no square root in `S_3`. Any smallest
  viable arithmetic transfer inequality must see that shared root carrier,
  not just the five raw rank-one variables.

- **Literal root additivity kills the `S_3` enemy, but an exact `S_4` leak
  remains.** `root-additivity-eliminates-the-s3-rank-one-leak` performs the
  complete `S_3` case analysis after substituting
  `X=a^2`, `Y=b^(-2)`, `C=a^(-1)b a^(-1)` and requiring `U` to centralize
  `a,b`. If `U` is a transposition, its two-element centralizer makes the
  denominator identity force `H` into the same centralizer. If `U` is a
  three-cycle, its centralizer is `A_3`; a noncentral `H` would invert that
  cyclic group, making the right side of the denominator identity lie in
  `A_3`, impossible for a transposition. Thus `[U,H]=1` in every `S_3`
  realization. `literal-root-additivity-rank-one-packet-has-s4-leak` closes
  the larger-finite-group test negatively: with
  `a=U=(2 3 4)`, `b=a^(-1)`, and `H=(1 2)(3 4)`, the literal denominator
  identity holds while `[U,H]` is nonidentity and hence has regular trace
  zero. Therefore root additivity plus the rank-one packet still cannot imply
  a matrix inequality. Any viable repair must use genuinely rank-two
  Steinberg gluing or another arithmetic relation absent from that `S_4`
  carrier.

- **The bottom two-primary root face satisfies an explicit HS transfer
  inequality.** `involutory-opposite-root-face-obeys-projective-transfer`
  proves, for the literal root variables `a=x_13(1)`, `b=y_31(1)`, that
  the denominator identity has

  ```text
  ||[U,H]-I||_2
   <=2(eta+||a^2-I||_2+||b^2-I||_2)
      +2||Ua-aU||_2+||Ub-bU||_2.
  ```

  Indeed the two square terms reduce the recursive denominator word to
  `H approximately a b a^(-1)`, which already centralizes `U`. Thus an
  enemy cannot live on the exponent-two root stratum. It must carry deeper
  two-power root order or pay a displayed defect. This is the first robust
  positive inequality beyond the `S_3` no-go and explains the role of the
  next rank-two layer: synchronize the deeper conductor strata across the
  shared Steinberg root, rather than spend rank-two machinery on the already
  closed involutory face.

- **One genuine A2 relation supplies the involutory long-root input.**
  `involutory-steinberg-simple-root-forces-long-root-involution` proves the
  robust identity

  ```text
  ||a^2-I||_2
   <=4||a-[p,q]||_2+||p a p^*-a||_2+2||p^2-I||_2.
  ```

  It is just the quantitative fact that conjugation by an involution
  reverses its commutator. Using the upper A2 chamber
  `a=[x_12(1),x_23(1)]` and the opposite chamber for `b=y_31(1)`, then
  feeding both estimates into the preceding opposite-root inequality,
  gives the first explicit rank-two-to-target cascade. It closes every
  packet supported on the bottom exponent-two simple-root stratum. The
  remaining enemy must put positive mass at deeper two-power conductor in
  at least one opposite chamber, exactly where the full shared-root hexagon
  synchronization remains necessary.

- **The first deep shared-carrier stratum has a robust dimension-free
  floor.**  `robust-half-period-a2-flip-pays-simultaneous-doubling` treats a
  fixed depth `2^N` without assuming an exact finite Heisenberg packet.  Four
  explicit half-period commutator residuals force the two transverse root
  doubling errors to have squared sum at least
  `2(1-Delta/4)_+^2/(2^(N-1)+1)^2`.  This closes the analytic inequality once
  a common primitive A2 carrier is present.  It does not solve the remaining
  matrix-only step: authenticating positive common carrier mass around the
  closed hexagon rather than allowing separate rectangular root matchings.

- **The exact regular congruence stratum authenticates a fixed positive
  carrier.**  In `SL_3(Z/2^a)`, the six top-layer root involutions generate
  `(C_2)^6`.  `six-top-dyadic-root-signs-share-weyl-hexagon-carrier` proves
  that their all-negative character projection has regular trace `1/64`, is
  fixed by the signed Weyl hexagon, and supports both negative half-period
  commutators in every chamber.  Thus the common-carrier intersection is
  already depth independent after exact regular congruence decoding.  The
  unresolved boundary is outlier/approximate decoding plus the rectangular
  transition between adjacent dyadic depths, not a loss intrinsic to the
  closed A2 packet.

- **The large-prime one-twist depth argument does not close this dyadic
  decoder.**  `p-divisible-lambda-exact-mass-vanishes-at-large-primes`
  concerns `p>=11` and starts from a genuine lattice representation, so
  that exact `C_0`-isotypic depth measures exist.  It proves a positive
  diagonal/off-diagonal gap because `4c_p-3>0`.  Here the arithmetic pair is
  fixed at `p=2`, where that coefficient is negative, and `(PTS1)` quantifies
  over arbitrary approximate assignments rather than the already decoded
  `Lambda`-exact face.  Thus the single-twist proof really does kill all
  flat and ultra-deep towers in its stated large-prime face, but it supplies
  neither the missing sixfold-parity decoder nor a counterexample to this
  universal dyadic transfer claim.

- **Proper sign moments do not decode that carrier.**
  `six-weyl-sign-proper-moments-miss-top-parity` takes the odd-parity affine
  hyperplane of the six sign characters.  Its exact finite representation
  has the regular trace on every nonempty proper product of the six signs
  and exact signed-Weyl covariance, but its all-negative projection is zero.
  Fourier inversion shows that precisely the missing full six-root parity
  moment distinguishes it from the regular packet.  Thus an outlier decoder
  must control that genuinely six-way moving-depth word; one-root, pairwise,
  five-wise, and Weyl-symmetrized proper moments cannot close the packet.
  This no-go is upstream of the still-open rectangular denominator
  transition.

- **The denominator image of the missing parity word is explicit.**
  `six-root-top-parity-transports-to-staggered-negative-triple` computes that
  conjugation by `diag(2,1,1/2)` sends the product of all six top-layer root
  signs, modulo level `2^a`, to the commuting `21,32,31` triple at depths
  `a-2,a-2,a-3`.  Thus the remaining decoder/transport gate is now a single
  scalar coefficient transfer from the sixfold source parity word to this
  order-`4,4,8` target triple.  The identity is exact, but its fixed-generator
  word length grows with `a`; it does not by itself give the required
  depth-free normalized-HS modulus.

- **Approximate perfectness removes the projective phases quantitatively.**
  This part of the exact proof survives presentation defect and is not the
  remaining obstruction.  Put

  ```text
  q=sum_(c in S_C) (1-|tr([U,rho(c)])|^2).
  ```

  Fix, once and for all, for each `s in S_C` an equality in `C`

  ```text
  s=product_j [a_(s,j),b_(s,j)],
  ```

  with every `a_(s,j),b_(s,j)` written in the alphabet `S_C`.  Let `L` be
  the maximum total `S_C`-letter length of these products, and let `B` be the
  maximum area, over the fixed ambient presentation, of the finitely many
  resulting equality words.

  For each `c in S_C`, choose `z_c in T` minimizing the distance from
  `w_c=[U,rho(c)]` to the scalars, with the inverse choice conjugated.  Then

  ```text
  ||w_c-z_c I||_2^2
    =2-2|tr(w_c)|
    <=2(1-|tr(w_c)|^2).
  ```

  The relative-commutator cocycle identity telescopes along every word in
  `S_C`.  Scalar phases cancel on each commutator, so the fixed product of
  commutators representing `s` has relative commutator within

  ```text
  L sqrt(2q)
  ```

  of `1`.  Its evaluated matrix is within `B delta` of `rho(s)`, because a
  van Kampen expression with `B` conjugates of defining relators telescopes
  in normalized Hilbert--Schmidt norm.  The map
  `R |-> U R U^* R^*` is `2`-Lipschitz on unitaries.  Therefore every
  approximate assignment satisfies the dimension-free bound

  ```text
  max_(s in S_C) ||[U,rho(s)]-1||_2
    <= L sqrt(2q)+2B delta.                             (PTS4)
  ```

  Thus scalar drift is fully paid by the projective subgroup energy and the
  presentation defect.  After `(PTS4)`, the unresolved step is sharply
  isolated: turn ordinary almost-commutation with the matrices `rho(S_C)`
  into almost-commutation with `rho(h)` when `rho` is only an approximate
  representation.  The exact Kazhdan projection cannot simply be applied,
  because `Ad rho|_C` need not be a representation; proving the needed robust
  projection/co-density statement is already the universal matrix-
  ultraproduct relative-commutant wall.

- **The native joint relation has a strictly smaller defect-only certificate.**
  `native-transfer-has-defect-only-certificate` proves that after restricting
  to the balanced involution `c` and imposing `[c,h c h^-1]=1`, qualitative
  regular transfer is equivalent to one universal linear inequality with no
  actor trace conditions.  Tensor amplification and residual-finite
  camouflage preserve all native conditions.  This does not prove the present
  arbitrary-unitary claim, but it removes both the modulus and trace-profile
  gaps from the weaker lamp problem.
- **The quantitative wall collapses to the universal qualitative wall.**
  `projective-transfer-linear-bound-equals-no-ultraproduct-leak` proves a
  stronger compactness statement than the previously recorded tensor
  observation.  If no linear bound
  `e_h<=L(q_C+delta)` exists, choose a violation
  `e_n>n(q_n+delta_n)` and take `ceil(1/e_n)` diagonal tensor copies.
  Relator defect and total `C`-energy become `O(1/n)`, while target energy is
  at least `1-exp(-1)`.  Hence exclusion of a qualitative projective leak in
  every matrix ultraproduct automatically gives `(PTS1)` with the linear
  modulus `eta(delta)=L delta`; there is no separate Lojasiewicz-rate
  problem.  Combined with perfectness, this identifies the present claim
  with **universal** relative-commutant collapse.  It also exposes an
  overstrength in the current route: `(PTS1)` ranges over arbitrary
  approximate assignments, while the HNN contradiction consumes only the
  full regular-trace microstate class of the joint HNN tuple.  The precise
  trace-profile audit is recorded below.

- **Canonical restriction on `A` is equivalent to the universal claim; full
  HNN regularity is genuinely narrower.**  Enumerate the nonidentity elements
  `g_1,g_2,...` of the residually finite group `A`.  Given any failed sequence
  `(rho_n,U_n)`, choose a finite quotient `q_n:A->Q_n` separating
  `g_1,...,g_n`, let `lambda_n` be the regular representation of `Q_n`, and
  put

  ```text
  rho_tilde_n(x)=rho_n(x) tensor lambda_n(q_n(x)),
  U_tilde_n=U_n tensor I.                                (CAN1)
  ```

  Every presentation relator has exactly its old normalized-HS defect, and
  for every word `w in A`,

  ```text
  [U_tilde_n,rho_tilde_n(w)]
    =[U_n,rho_n(w)] tensor I.                            (CAN2)
  ```

  Hence every projective energy in `(PTS1)` is unchanged.  On the other hand,
  `tr(rho_tilde_n(g_j))=0` for `j<=n`.  Thus `(PTS1)` is equivalent to its
  restriction to assignments whose **`A`-character** tends to the regular
  character.  This is the modulus-square analogue of
  `canonical-trace-does-not-weaken-thin-commutant-transfer`; the proof is
  literally the same tensor camouflage.

  This does not eliminate the route's quantifier overstrength.  The HNN proof
  needs `(rho_n,U_n)` to have the regular character on every nontrivial word
  of

  ```text
  <A,t | [t,C]=1>,
  ```

  not merely on words in `A`.  In `(CAN1)` the second tensor factor sends the
  stable letter to `I`; it therefore does not force trace zero for balanced
  stable-letter words whose `A`-projection is trivial.  In particular it does
  nothing to the trace of `[U_n,rho_n(h)]` itself.  Producing full HNN-regular
  camouflage would require finite-dimensional models separating those HNN
  words, which is not supplied by residual finiteness of `A`.  Consequently
  the genuinely minimal terminal is transfer on full regular-character HNN
  microstates; merely saying "regular on `A`" does not weaken the universal
  analytic wall.

- **The adjacent-vertex double removes the remaining quantifier
  overstrength.**  Inside the HNN group, the two adjacent vertex stabilizers
  generate

  ```text
  D=A *_C A = <A,tAt^(-1)>,
  ```

  by `sl3-arithmetic-double-embeds-in-centralizer-hnn`.  A full HNN-regular
  microstate restricts to a canonical-character microstate of this double.
  Apply `(PTS1)` to the block diagonal of its two vertex assignments and the
  block-swap unitary: subgroup energy and presentation defect vanish, so the
  fold-kernel mark `i_0(h)i_1(h)^(-1)` collapses.  Thus the strictly smaller
  terminal `sl3-regular-arithmetic-double-fold-mark-collapse` suffices for
  the goal and is the exact trace-profile class actually consumed.  Its
  zero-defect boundary is complete:
  `sl3-arithmetic-double-finite-representations-fold` proves that every exact
  finite-dimensional representation folds the entire double.  The only
  residue is promoting this block-swap theorem on canonical double
  microstates, not proving `(PTS1)` for arbitrary assignments.

- **Diagonal tensor powers are an exact projective error amplifier.**  Put
  `E(W)=1-|tr(W)|^2`.  Normalized traces multiply, so for every unitary `W`
  and integer `k>=1`,

  ```text
  E(W^(tensor k)) = 1-(1-E(W))^k <= k E(W).                 (AMP1)
  ```

  Apply the same diagonal tensor power simultaneously to `rho` and `U`.
  Every commutator word tensors, hence its projective energy follows `(AMP1)`;
  every ordinary presentation relator obeys the telescoping estimate
  `||rho(r)^(tensor k)-I||_2 <= k ||rho(r)-I||_2`.  Consequently, if a
  sequence had target energy `e_n -> 0` but ordinary relator defect
  `delta_n=o(e_n)` and `C`-energy `q_n=o(e_n)`, choosing
  `k_n=floor(1/e_n)` would produce a new sequence with vanishing relator
  defect and `C`-energy but target energy tending to `1-exp(-1)`.  This is a
  rigorous error-delocalization mechanism: tensoring copies a projective bad
  region until it has constant trace mass.  It does **not** prove `(PTS1)`,
  because an enemy can keep `e_n=O(delta_n+q_n)`; it shows that the remaining
  obstruction is precisely that locked linear-scale regime, not arbitrarily
  dilute target error.
- **Creutz--Peterson character rigidity stops at the generated factor.**
  Their operator-algebraic superrigidity theorem for commensurators
  (arXiv:1311.4513, Theorem B / Theorem 6.3) assumes
  `pi(A)''=M` and concludes that this generated finite factor is either
  finite-dimensional or the regular factor.  In `(PTS1)`, however, `U` lies
  in an ambient matrix ultraproduct outside `pi(A)''`.  Replacing `pi` by
  `Ad(U) pi` gives two representations agreeing on `C`, but the theorem does
  not assert uniqueness of extensions of a fixed `C`-representation inside a
  larger finite algebra.  This scope gap is real, not cosmetic: in the exact
  HNN algebra
  `L(<A,t | [t,C]=1>)`, the embeddings `pi` and `Ad(t) pi` agree on `C` and
  differ on `h`.  Thus exact character/factor rigidity cannot prove the
  transfer; finite-dimensional approximability must enter essentially.

- **The hyperfinite-limit sector does close.**
  `sl3-projective-transfer-holds-on-hyperfinite-limit-sector` applies the
  established character criterion for hyperfinite Hilbert--Schmidt
  stability to the whole ambient tuple.  If an approximate assignment has
  amenable generated ultraproduct algebra, it is flexibly `o(1)`-correctable
  to exact finite-dimensional representations of `A`; padding the witness
  unitary on the vanishing corner and applying the exact projective
  co-density estimate proves `(PTS1)` sequentially in that sector.  Hence a
  surviving enemy must have a genuinely nonamenable generated algebra.
  This is the exact positive reach of character rigidity: the regular
  character has GNS algebra `L(A)`, which is nonamenable, and residual-finite
  tensor camouflage moves every universal enemy into precisely that
  uncorrected sector without changing its energies.

- **Character/Weil classification stops at the Schur-clock firewall.**
  `schur-clock-router-has-maximal-projective-leak` gives an exact finite
  calibration for the remaining dyadic-conductor strategy.  On any cyclic
  family of equal-dimensional isotypic blocks, a router shifting the blocks
  admits a block-scalar unitary `U` which commutes with the entire source
  algebra but has

  ```text
  tr([U,V])=0.
  ```

  The construction preserves all block characters, conductor labels,
  intertwiner ranks, and scalar Weil/Mackey cocycles.  Thus classifying the
  finite congruence constituents and their projective arrow phases cannot
  prove `(PTS1)`: those data permit zero source energy and maximal target
  energy.  This is not an arithmetic countermodel, because exact co-density
  forbids the required router cycle for a genuine representation of `A`.
  It isolates the smallest representation-theoretic obstruction that a
  proof must add: a non-Folner bound for the authenticated conductor
  transport graph, or a literal same-multiplicity-reservoir constraint on
  compositions of different arithmetic paths.  In particular a scalar
  metaplectic/Weil flux computation alone cannot close the projective
  transfer frontier.

- **Exact models now pass with a uniform quantitative gap.**
  `exact-projective-codensity-has-a-uniform-trace-square-gap` proves `(PTS1)`
  with `eta(0)=0` and one dimension-independent `K` for every exact
  finite-dimensional representation.  Perfectness of `SL_3(Z)` cancels the
  scalar phases on fixed commutator expressions, property (T) moves `U` close
  to `rho(C)'`, and co-density identifies that commutant with `rho(A)'`.
  Thus projective centralizers and finite congruence quotients are no longer a
  falsification gate.  What remains is entirely the uniform-outlier sector of
  approximate ambient representations.

  There is no general compactness promotion even after restricting to full
  canonical adjacent-vertex doubles.
  `canonical-free-double-escapes-uniform-exact-projective-folding` constructs
  a fixed finitely presented sofic pair whose exact projective-transfer
  constant is zero and whose every exact double representation folds, but
  whose canonical double microstates keep the fold word trace-zero.  Thus the
  exact arithmetic gap is useful only after one proves an SL3-specific
  correction or mixed-word theorem; exactness plus canonicality does not
  close the outlier sector formally.

- **The target scalar phase is now removed by one bounded rank-one
  identity.**  In the `(1,3)` `SL_2` block, write

  ```text
  h=x(2)y(-1/2)x(2)w(-1),
  y(-1/2)=h y(-2)h^(-1).
  ```

  If `W=[U,rho(h)]`, conjugating this decomposition by `U` gives, up to
  fixed presentation and lattice-commutator errors,

  ```text
  W=x(2)[W,rho(y(-1/2))]x(2)^(-1).
  ```

  Therefore

  ```text
  ||W-I||_2
   <=2 sqrt(2(1-|tr(W)|^2))+K(sqrt(q)+delta).
  ```

  See `sl3-rank-one-denominator-self-commutator-removes-target-phase`.
  This is a finite-dimensional, dimension-free upgrade, stronger than
  killing the limiting phase character by ambient perfectness.  It proves
  that the target phase is not a residual issue, but it does not supply the
  missing inequality forcing the trace-square energy itself to vanish.
- **Coset-Bernoulli firewall.** If the generalized coset Bernoulli crossed
  product of `coset-bernoulli-ce-refutes-relative-commutant-collapse` is
  Connes embeddable, its base-coordinate unitary produces an exact
  `C`-central witness.  Its commutator with `h` is non-scalar, so it also
  refutes `(PTS1)`.  Projectivization weakens RCC but does not evade that CE
  countermodel.
- **Hecke reduction.** `hecke-far-commutator-defect-formula` already compresses
  ordinary commutator energy to one spherical coefficient.  The missing
  calculation is the modulus-square/projective analogue restricted to the
  nonlinear inner orbit `{Ad(U)}`.  Property (T) controls the surrounding
  Hilbert space but not, by itself, this fixed set.
- **The scalarized source Hecke tower leaves even the first coefficient
  completely free.**  `source-hecke-data-leave-projective-square-free`
  identifies the smallest mixed scalar

  ```text
  phi_T(h)=|tau(T^*rho(h)T rho(h)^*)|^2.
  ```

  A central tensor Haar unitary gives value `1`, the HNN stable letter gives
  value `0`, and weighted direct sums give every value in `[0,1]`, while the
  embedded source inclusion, its scalar conditional expectations, its
  entire bifinite Hecke tower, and the `C`-central Haar marginal of `T` are
  unchanged.  Therefore coefficient elimination and source Hecke
  orthogonality cannot imply `(PTS1)`.  A proof must use matrix-coordinate
  embeddability of the joint extension `(rho(A),T)`; there is no smaller
  source-intrinsic positive-definite scalar waiting to be extracted.
- **Finite test.** On congruence quotients minimize the ratio of the left side
  of `(PTS1)` to its `C`-energy.  The exact theorem bounds this ratio uniformly
  in the quotient level; computation is now only a calibration of the proven
  exact constant, not a possible refutation of the zero-defect case.
- **The remaining matrix enemy is now an exhaustive two-branch
  dichotomy.**  `sl3-projective-transfer-enemy-dichotomy` first applies
  residual-finite tensor camouflage and then splits by lattice
  correctability.  Every fixed-gap enemy is either uniformly far from all
  exact lattice representations (the regular inner-adjoint outlier), or an
  available lattice correction has a fixed positive fraction of its
  dimension in irreducibles of positive `2`-conductor.  The odd-correctable
  sector is closed; mixed and pure dyadic mass is not.  This corrects the
  tempting but false summary that only the noncorrectable sector remains.
  The exact regular HNN factor is a simultaneous tracial countermodel, so
  neither branch can be removed by dimension-blind tracial/SOS methods.

- **Every fixed-depth Clifford refinement is still amenable.**
  `every-fixed-dyadic-clifford-window-is-finite-fiber-folner` strengthens the
  last-two-layer calculation to an arbitrary fixed number `k` of deepest
  congruence layers.  Once `a>=2k`, the principal kernel is the additive
  group `sl_3(Z/2^k Z)` and its conjugation action factors through the fixed
  group `SL_3(Z/2^k Z)`.  Hence all depth-`k` Clifford labels form a fixed
  finite fiber over the `A_2` coweight lattice, and every bounded-range type
  graph remains amenable.  Thus increasing the local congruence window from
  two layers to any other fixed depth cannot close the dyadic branch by
  expansion.  The required input must see depth growing with conductor or a
  genuinely same-carrier interference relation.  This is a proof-architecture
  no-go, not a full arithmetic countermodel.

- **Arbitrary codimension does not rescue leakage-small polar enemies.**
  `leakage-small-polar-compressions-obey-projective-transfer` strengthens the
  vanishing-codimension fence.  If a tuple is obtained by polar-compressing
  one exact arithmetic representation and the retained range has vanishing
  normalized leakage for the fixed generator packet, property `(T)` applied
  to the zero-extended corner proves `(PTS1)` with a leakage error,
  independently of the retained rank fraction.  Any remaining
  positive-codimension compression attack must keep macroscopic generator
  leakage while arranging cancellation of its presentation relators, or
  cease to be a compression of an exact ambient model.

- **At macroscopic leakage, polar-compression data are universal.**
  `macroscopic-zero-compressions-make-polar-data-universal` uses an
  independent set in a finite quotient Cayley graph.  On the corresponding
  positive-density coordinate subspace every compressed presentation
  generator is zero, so its unitary polar extension is arbitrary.  Therefore
  every finite tuple, enemy or not, is a polar-correction tuple of an exact
  arithmetic representation with maximal leakage.  This is not a PRCC
  countermodel, because the arbitrary tuple must still solve the arithmetic
  relators and carry the leak.  It proves sharply that exact ambient dilation
  cannot control the remaining branch without small leakage,
  singular-overlap, or additional arithmetic incidence.

- **Every fixed polar enemy has macroscopic singular collapse.**
  `fixed-projective-leak-forces-polar-singular-collapse` turns the aggregate
  leakage fence into a spectral dichotomy.  If target projective energy stays
  above `gamma` while lattice energy is at most `gamma/(2K)`, then for one
  fixed presentation generator at least
  `theta=gamma/(4K|S_A|)` of the retained corner has compressed singular
  value at most `sqrt(1-theta)`.  Thus the only unresolved exact-dilation
  branch is a genuinely information-losing polar block of positive mass.
  Charging that block to arithmetic relator defect, or realizing it in a
  canonical microstate countermodel, is the next precise gate.

- **Singular collapse is compatible with exact canonical polar tuples.**
  `canonical-exact-polar-models-have-flat-singular-loss` realizes every fixed
  `t in (0,1)` by exact ambient representations and positive-density corners
  satisfying `Ppi(s)P=t rho(s)` simultaneously for the full named packet,
  where `rho` is an exact representation with canonical limiting character.
  Hence all compressed singular values equal `t`, the polar factor is unique,
  and every arithmetic relator defect is zero.  This rules out charging the
  extracted bad singular block to relator incidence alone.  The next gate is
  necessarily joint: couple the projective witness `U` to the raw
  compression modulus/phase, since exact transfer shows the polar tuple by
  itself has no leak.

- **The joint gate is one complement-unitary extension problem.**
  `projective-transfer-reduces-to-complement-unitary-extension` gives an
  explicit sufficient inequality.  When the target compression has least
  singular value `sigma`, the corner target energy is at most
  `(8K/sigma^2)` times the scaled infimum, over complement unitaries `Z`, of
  the ambient lattice projective energy of `U direct_sum Z`.  This quantity
  sees exactly what all scalar modulus/relator calibrations omit: whether the
  same `Z` transports `U` coherently across every incoming and outgoing
  compression boundary.  Constructing that `Z` from finite arithmetic
  incidence, or building a canonical enemy for which its cost stays
  positive, is now the exact polar-compression terminal.

- **Positive cross-Gram PVM rounding is gauge-blind at the forbidden
  midpoint.**  `sl3-fold-positive-cross-gram-does-not-select-endpoint`
  proves that for any two projections `P,Q`, the contraction `G=PQ`
  intertwines the complete binary packets `(P,I-P)` and `(Q,I-Q)` with
  exactly zero error and mass `tr(PQ)`.  Thus at a canonical balanced fold,
  where `tr(PQ)->1/4` but `||P-Q||_2^2->1/2`, Lin's positive-Gram theorem
  applies perfectly without moving either original-coordinate endpoint.
  More strongly, `canonical-arithmetic-swap-fold-gram-is-arcsine` proves that
  every hypothetical canonical microstate of the full arithmetic swap
  extension has the limiting Gram law

  ```text
  mu_(QPQ)=(1/2)delta_0+(1/2)Arcsine_[0,1],
  ```

  so its mass near singular value one tends to zero; a residually finite
  `C_2*Z` tower gives an unconditional exact local calibration of the same
  law.  The exact missing modulus is

  ```text
  tr(QPQ-(QPQ)^2)=(1/2)||[P,Q]||_2^2.                 (PTS5)
  ```

  Canonicality forces `(PTS5)->1/16`; if arithmetic forces it to zero, a top
  spectral cut gives a positive near-common sector and simultaneously a
  direct second-moment contradiction.  Positive Gram mass, packet
  exactification, and polar alignment alone do not.  This narrows the
  canonical-double use of Lin's machinery to the defect-only mixed terminal
  `sl3-swap-extension-has-defect-only-fold-square-rigidity` and leaves the
  full arbitrary-unitary endpoint problem open.

- **Explicit falsification gate via a compact homogeneous quotient
  (2026-08-25).**  `homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse`
  shows that `(PTS1)` fails as soon as
  `M = L^infinity(SL_3(Q_2)/Lambda') rtimes A` is Connes embeddable, for any
  torsion-free cocompact lattice `Lambda' < SL_3(Q_2)` with at least two
  `SL_3(Z_2)`-orbits on the quotient: the `+-1` indicator of one orbit is
  `C`-central (`C` acts profinitely, through `SL_3(Z_2)`), and its commutator
  with `rho(h)` has trace of modulus `< 1` in every microstate sequence, so
  no constant `K` and modulus `eta` can hold.  The embeddability question is
  parked as `sl3-homogeneous-quotient-crossed-product-is-connes-embeddable`.
  Consequently any proof of `(PTS1)` must be an argument that this explicit
  crossed product has no matrix microstates.  In particular it cannot use
  only the finite-image representations of `A`, on which `(PTS1)` does hold
  with `K = O(1/kappa^2)` by property (T) of `C` and `rho(C) = rho(A)`; and
  it must see the difference between the congruence filtration of
  `SL_3(Z_2)` and its `h`-conjugate, which is exactly what the profinite
  restriction of `M` to `C` erases.

# Trace promotion and renormalization programme

Date: 2026-08-20

This artifact integrates the trace-host, selector-renewal, self-similar tape,
renormalization, phase, SDP, and quantum-syndrome proposals into Cairn's
nonhyperlinearity programme. It separates established reductions, exact finite
checks, open construction claims, and falsification fences.

## 1. The invariant target

Tensor amplification `U -> U tensor I_k` preserves normalized trace moments
and normalized Hilbert--Schmidt relator defects. It erases absolute rank,
dimension, and every additive index. Therefore the obstruction must be a point
or separation in a fixed compact trace-profile space, or an equivalent
normalized density or phase profile.

This is already formalized by `finite-trace-profile-net-is-dimension-free`,
`additive-index-instability`, `index-density-is-amplification-stable`, and
`marked-hs-separation-forces-spectral-density`.

The new organizing claim is `canonical-trace-promotes-non-ce-profile`: every
mechanism below is judged by whether canonical delta microstates force the
finite profile of a known non-CE trace. `non-ce-trace-on-sofic-racg` proves
that the source trace already lives on an explicit sofic right-angled Coxeter
group. Thus the open task is trace promotion, not construction of a wild host.
The existence of non-CE traces on a free group does not settle this problem:
hyperlinearity concerns its flexible canonical delta trace.

## 2. The common selector disease

Commuting involution words see only affine `F_2` data.
`affine-auxiliary-control-flow-barrier` and
`finite-group-selector-induction-barrier` rule out hiding nonlinear selection
in affine auxiliaries or a standalone finite group.

The naive Weyl-partner completion and selector reset fail for the same reason:
their action on assignments need not preserve the constraint ideal. Toggling a
bit can send a satisfying assignment to a forbidden one. If that forbidden
atom was killed, conjugacy by the reader is inconsistent. Regular traces also
prevent relations from pruning exactly the unwanted character sectors.

Every live construction therefore obeys one rule: readers must be equivariant
for the violation family. They may transport, count, or mix forbidden mass;
they may not delete it or turn an imposed zero atom into a nonzero conjugate.
Multiplicity readers use rank jumps and phase readers use central projective
words. Both still need selector renewal and an infinite-depth ledger.

## 3. Free amalgamation and nonamenable type transfer

`countable-tracial-amalgam-extension` closes completeness for an infinite
iterated packet construction: compatible stage traces extend through reduced
free amalgams over finite-dimensional wires, and freeness adds no relations
between nonadjacent selectors.

Finite graphs of finite groups remain dead. Their complete representation
types are positive stationary integer flows. An infinite Bass--Serre tree helps
only if the complete normalized transfer is uniformly contractive away from
the one scalar reset ray.

The exact finite check `schur-marked-character-transfer-gap` is positive.
Averaging the ten mark-preserving involutive support-packet charts gives

```text
T = (1/5) [[2,1,1,1], [1,2,1,1], [1,1,2,1], [1,1,1,2]],
```

so the marked central-character transverse sector contracts by exactly `1/5`.
The replay is `experiments/schur_marked_transfer_spectrum.py`. Hidden
irreducible multiplicities may still carry a norm-one flow.
`bass-serre-schur-transfer-contraction` names that remaining computation, and
`multiplicity-return-via-free-amalgam` connects it to the return transducer.

Falsification: enumerate the full induction/restriction matrices for each
wiring, remove the scalar stationary ray, and compute the largest weighted
singular value. If every candidate has value at least one, abandon this lane.

### 3.1 Decisive correction: the infinite tree does not consume type mass

`stationary-type-mass-reused-on-infinite-amalgams` closes the proposed route
negatively. A graph-of-groups representation does not allocate disjoint
Hilbert mass to Bass--Serre vertices. Compatible vertex representations are
aligned recursively on the same `C^d`, even for a countable tree. Thus the
constant scalar reset ray is an `ell^infinity` repeated type, not an `ell^2`
flow, and tree nonamenability cannot make it escape.

The exact `1/5` transverse gap remains useful local mixing data, but it cannot
touch the sole scalar current. Free amalgamation still solves tracial
completeness and selector renewal; a soundness construction must add proper
corners, orthogonal branch ranges, or a projective cocycle. The route
`multiplicity-return-via-free-amalgam` is invalidated.

## 4. Thompson--Nekrashevych tape

The prefix geometry already visible in the Leavitt atlas supplies internal
cylinder swaps, disjoint-support commutation, and logarithmic-depth addresses.
The missing kernel is `self-similar-central-sign-cocycle`: a central extension
class fixed by binary wreath recursion, with sections containing a Pauli pair.

`untwisted-sign-replication-flips-minus` is mandatory. If both child signs act
by `-I`, their untwisted product acts by `+I`; hence `J=(J,J)` cannot reproduce
the negative sector. The phase must live in a cocycle or projective lift.

There is also no projective escape inside the bare prefix mixer.
`thompson-v-central-extensions-split`, from Szymik--Wahl acyclicity and the
universal-coefficient sequence, proves that every central extension of
Thompson `V` splits uniquely.  Thus the prefix operations can transport a
local phase but cannot create its holonomy.  The class must involve the
nontrivial state/Clifford kernel or a relative extension containing it.

`nekrashevych-clifford-sign-tape` asks the resulting frame to provide internal
trace-preserving transport, polylogarithmic addresses, disjoint-support
relations, one relative CAR qubit per level, and an exact marked tracial model.
This replaces infinitely many lamplighter commutators and external transport.

### 4.1 Explicit central-product solution

The algebraic tape is now constructed.  In
`thompson-clifford-central-product-tape`, Thompson `V` acts highly
transitively on the rational Cantor orbit `X=V.0^infinity`.  Put one `D_8`
Pauli lamp at every site and identify all lamp centers to one central
involution `J`.  De Cornulier's finite-presentation criterion applies because
the point stabilizer is finitely generated and `V` has only two orbits on
`X^2`.  The two binary child groups commute and meet in `<J>`: they form a
central product, not a direct product.  This is the required nontrivial
self-similar extension and avoids `J=(J,J)`.

The sites `x_n=0^n10^infinity` give a nested CAR prefix with linear-depth
addresses, and the infinite tensor-product crossed-product trace has `J=-I`.
Free product with the non-CE RACG host supplies exact tracial completeness,
but deliberately supplies no matrix soundness or predicate coupling.

## 5. The only viable infinite ledgers

Even a constant local loss makes a forward union bound reach only bounded
depth.  A polynomial loss in the depth is equally acceptable to the backward
ledger because geometric weighting dominates it. Cairn contains both viable
replacements.

### 5.1 Backward contraction

`contractive-computation-ladder` turns

```text
a_n <= lambda a_(n+1) + p(n) sqrt(E),  lambda<1,
```

into a uniform energy floor. `schur-violation-density-gives-contraction`
supplies this shape from one-versus-two branching.

The missing self-similar step is not the slogan "trace of a product equals the
product of traces." Disjoint commuting subalgebras may be correlated.  The
original `subtree-trace-independence-certificate` demanded a fixed
adjoint-mixing bound

```text
|tr(xy)-tr(x)tr(y)| <= C sqrt(E).
```

Reduced free amalgamation supplies exact independence only in the completeness
trace.  The analytic constant-gap averaging statement is correct:
`expander-separated-factors-have-independent-traces` proves the desired
covariance estimate from conditional expectation with constant
`1/(1-lambda)`, independent of spin and multiplicity dimension.  Two later
checks, however, rule out the proposed use.

First, `normalizer-multiplicity-twist-breaks-prefix-expander-rounding` gives an
exact counterrepresentation.  A Clifford implementer in an arbitrary
representation is `C_q tensor W_q`, not `C_q tensor I`; taking
`W_q=conjugate(C_q)` leaves the Bell line fixed.  Therefore embedding Jacobi
normalizers in a Toeplitz head does not establish the tensor-form hypothesis,
and the former Toeplitz proof of the uniform cell theorem is invalidated.

Second, and more decisively for predicate soundness,
`schur-violation-density-is-in-the-spin-commutant` computes

```text
Z_C-Z_B=P_f/(2D).
```

The predicate projection `P_f` acts on selector multiplicity, while every
spin expander acts on the `M_D` coordinate.  It is therefore fixed, not mixed,
by the spin expander.  The proposed route from spin-factor separation to
Schur sibling-density independence is invalidated.  This reunifies the two
"diseases" precisely: **selector renewal cannot be replaced by spin
independence**.

There is nevertheless a useful positive repair.
`pauli-generator-average-has-inverse-linear-gap` diagonalizes the average of
the `2n` coordinate Pauli conjugations and obtains an exact gap `2/n`.
Consequently `thompson-pauli-prefix-rounding-has-polynomial-cost` rounds the
new Thompson cell relative to the old prefix at only polynomial depth cost,
without any normalizer.  That is enough for the geometric ledger.  The sole
remaining Thompson soundness gate is now
`partial-center-thompson-schur-return`: turn the corrected Schur child branch
into the new Pauli coordinate while consuming the old selector center, then
transport a reset chart to the next Fanizza context.  The route
`nekrashevych-violation-recurrence-via-partial-center-return` combines this
with the established balanced reset ray and violation-oriented child identity.

That last proposed return also fails an exact local check.
`branch-flip-pauli-extraction-cancels-schur-surplus` shows that the clean
Pauli endpoint `<J,q_*,eta>` recombines the two child lines into `M_2`, exactly
undoing the rank jump.  Keeping the child chart and using only HNN transport
does not help: `reset-ray-hnn-return-is-stationary` gives

```text
m_Q-m_B=2K_1n,       n_next=n,
```

so the next full-packet mass is again `m_B`, not `m_Q`.  Thompson transport
and selector renewal are therefore solved, but the scalar multiplicity return
still requires a genuine proper corner or one-sided compressor.  The live
claim is `reset-schur-bcs-branching-atlas` with that requirement made explicit.
`reset-schur-atlas-via-toeplitz-proper-corner` wires it to the existing
Toeplitz dichotomy.  The exact remaining analytic statement is no longer a
generic selector reset: `toeplitz-tail-retains-contextual-schur-density` must
show that residual erasure recreates the **predicate-oriented** density in the
compressed coefficient algebra, rather than only the structural child/full
Reynolds wall.

### 5.2 Fault tolerance

`bgv-adversarial-fault-tolerance` accepts a positive fraction of adversarial
site corruption, but the bridge from global HS error to site weight is open.
In the tree frame all local tests are conjugates, so Markov counting gives the
right fraction once coherent local tensor factors have been aligned.
`tree-transitive-site-noise-localization` isolates that noncircular alignment,
and `tree-localization-gives-site-noise-bridge` connects it to the existing
fault-tolerance route.

Recursive equations such as `h=x_0 s h s^(-1)` help only if they yield honest
logical Pauli group words with polylogarithmic derivation cost and preserve the
mark below the code radius. They do not prove an infinite operator product.

## 6. Phase mining

`boolean-predicate-central-phase-word` establishes the local ingredient: every
fixed Boolean predicate is a product of unitriangular iterated commutators
computing its algebraic normal form in a finite `2`-group. Finite-group HS
stability makes this reader robust.

`bcs-projective-kernel-phase-compilation` asks for one predicate word to act as
`-I` in the tracial GNS model, retain the robust finite-matrix gap, and survive
normal closure. Readers must count or permute violation projections rather than
shift satisfying sectors into killed atoms. The route
`phase-safe-toric-via-projective-kernel` connects this to the toric endpoint.

Falsification: require a representation of the full universal algebra, not a
local assignment-sector calculation, and check normal closure first.

## 7. Separator extraction

The radius-nine atlas separator is a valid finite target, but standard tracial
NPA cannot produce it. `tracial-npa-cannot-separate-canonical-trace` proves why:
canonical group moments are feasible in every truncated tracial moment cone,
so weak duality prevents a dual negative on the canonical trace.

The corrected campaign is `matricial-radius-nine-dual-extraction`. Numerical
matrix optimization may discover coefficients, but replay must use a
matrix-specific positivity language: trace invariant theory, exterior powers,
Schur complements, or a dimension-indexed argument made uniform in dimension.
If the proof remains valid on the canonical trace, it is not the separator.

## 8. Quantum-aware local syndromes

Random-hyperplane binaryization relates HS distance to bit disagreement, but
classical cosystolic soundness after that rounding is invalid: exact quantum
solutions can round to many violated classical checks. Cairn records this in
`classical-pcp-gap-is-not-tracial-pvm-gap`.

The repair has two gates. `quantum-context-frame-index` asks for a stable local
`Z_2` index of paired context frames which vanishes on every coherent quantum
solution. `balanced-product-frame-index-expansion` asks a bounded-degree
group-orbit complex to turn the marked twist into positive density of those
indices. `quantum-frame-index-syndrome-route` then yields the existing local
syndrome transducer. CS-angle parity and Pfaffian signs are candidates, but HS
stability near angle crossings remains open.

## 9. Work order and stopping criteria

1. Build the partial-center Thompson--Schur return.  The Clifford tape,
   polynomial prefix rounding, full selector reset, branch flip, and HNN
   context chart are all established separately; the remaining calculation
   is their one-cell intersection and exact marked extension.
2. Reject any return which places the Schur density in a spin-expander
   factor: `(SVC2)` is a zero-error falsification test.  Verify instead that
   the old selector center is absent from the returned prefix algebra.
3. Run radius-nine coefficient discovery unattended, but accept only a
   replayable matrix-specific proof.
4. Test quantum frame indices on exact contextual games and angle-crossing
   perturbations before investing in balanced-product expansion.

At every branch ask: is the forced quantity unchanged by tensor amplification,
and does it separate canonical delta profiles from the finite-matrix profile
closure? If either answer is no, the branch is bookkeeping without an
obstruction.

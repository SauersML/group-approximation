---
rg: 2
id: simple-lamp-hyperlinear-recovery-forces-action-sofic
kind: claim
title: Hyperlinearity of the A5 generalized wreath forces soficity of its coordinate action
distinct_from:
  invariant-cartan-completion: that concerns the abelian C2 Bernoulli algebra and asks for an invariant diagonal ultraproduct; this asks whether intrinsic nonabelian simple coordinate factors force a finite set-action model.
  single-lamps-recover-set-action: that starts from a sofic chart system for the lamp automorphism action; this starts only from arbitrary normalized-HS microstates of the whole semidirect product.
  lamp-charts-recover-set-action: that is a formal chart-to-action implication valid for many lamps; the missing content here is extracting such charts from unitary microstates.
---

OPEN.  Let `Gamma<G` be the pinned Kun--Thom infranormal Kazhdan pair, put
`X=G/Gamma`, take `K=A5`, and set

```text
W_K=K^(X) semidirect G.                                  (SHA1)
```

Prove

```text
W_K hyperlinear  ==>  the action G on X is sofic.        (SHA2)
```

Together with `coordinate-action-not-sofic`, `(SHA2)` would make `W_K` an
explicit finitely generated non-hyperlinear group.

The algebraic half is favorable.  For every finite `F subset X`, the minimal
nontrivial normal subgroups of `K^F` are exactly its coordinate copies
`K_x`; consequently

```text
Aut(K^F)=Aut(K)^F semidirect Sym(F).                      (SHA3)
```

Thus any exact automorphism of a finite lamp packet intrinsically determines
a permutation of its sites.

The analytic extraction is open.  Apply the amenable-base classicalization
theorem of Burton--Chaudkhari--Juschenko--Muliarchyk to the restriction of a
putative `W_K` microstate to the locally finite amenable lamp group `K^(X)`.
On each prescribed finite lamp window it produces, in the same Hilbert
dimension, a nearby permutation approximation.  Finite packet
exactification then leaves mostly regular `K^F` blocks.

What it does **not** do is classicalize the actor unitaries relative to the
chosen lamp basis.  The exact obstruction is
`simple-lamp-normalizers-have-unitary-multiplicity-fibers`: an actor can
implement the correct automorphism of every coordinate factor while mixing
the regular-block multiplicity by an arbitrary unitary.  Minimal normal
subgroups recover the labels `x in F` inside one packet, but do not recover a
permutation of the many packet copies needed for a sofic-action chart.

Therefore `(SHA2)` is not a consequence of amenable-base classicalization
plus abstract automorphism rigidity alone.  The missing theorem is an
**equivariant multiplicity classicalization**: after the lamp restriction is
made permutation-valued, the actor normalizers must be correctable, modulo
the right-regular lamp commutant, to permutations of the regular-block
copies with approximately multiplicative copy permutations.  This is the
nonabelian-simple analogue of invariant Cartan completion, not a solved
shortcut around it.

## Fixed-window audit

Passing to a fixed approximation window does **not** remove this gate.  The
failure occurs before any estimate on multiplicities.  For a finite
`F subset X`, exactification gives a genuine representation of

```text
Q_F=K^F
```

which is regular on `1-o(1)` of the ambient dimension.  If an actor unitary
normalized this whole algebra, then `(SHA3)` would indeed recover a genuine
permutation of `F`, independently of every right-regular or external
multiplicity unitary.  But the microstate covariance equations only give

```text
U_g K_x U_g^* approximately K_(gx)                       (SHA4)
```

for the finitely many named pairs `(x,gx)`.  They do not say
`U_g Q_F U_g^*=Q_F` unless `gF=F`.  For an infinite transitive action there
is no nonempty finite packet invariant under a generating actor set.
Replacing `F` by a larger finite set only moves this boundary.

After exactification, `(SHA4)` therefore determines only the partial
injection

```text
x |-> gx,       x in F with gx in F.                     (SHA5)
```

between intrinsic minimal factors.  Extending `(SHA5)` to a permutation of
all of `F` is extra data.  Actor multiplication controls the original
unitaries, but it does not make arbitrary boundary completions of their
partial factor maps multiply.  Producing completions which are coherent on
most chart states is exactly the sofic-action completion problem one is
trying to prove.

Amplification supplies no hidden completion.  On every regular core

```text
l2(Q_F) tensor C^m
```

an implementer of any chosen completed packet automorphism has the exact
form

```text
(P_beta tensor 1) C,
C in U(lambda_(Q_F)(Q_F)' tensor M_m).                   (SHA6)
```

Thus the intrinsic factors see the one finite label set `F`, while the
entire asymptotically growing carrier can remain in the arbitrary fiber
`C`.  Refusing to classicalize the packet copies discards precisely the
finite probability space on which coherent boundary completions would have
to be compared.  The factor labels alone give a partial orbit fragment, not
a sofic chart ensemble.

Hence fixed-window quantifiers improve the local statement--all named
simple factors can be exactified and their partial transport is intrinsic--
but do not prove `(SHA2)`.  A positive argument must still provide one of:

1. an equivariant completion of the partial factor maps on a near-total
   family of packet copies;
2. a monomialization/classicalization of the multiplicity-copy cocycle; or
3. another finite probability carrier on which the completed actor maps are
   approximately multiplicative.

Minimal normality alone supplies none of these.

The fixed-window residue is now explicit rather than qualitative.  By
`canonical-a5-window-leaves-a-partial-commutant-cocycle`, canonical
microstates exactify `A5^Y` to a `1-o(1)` regular core.  For an actor arrow
defined on `D subset Y`, every implementer is, up to dimension-free HS loss,
a chosen partial coordinate permutation times a unitary in

```text
rho(A5^D)'' tensor B(ell^2(A5^(Y minus D)) tensor C^m).
```

Actor multiplication makes these unitaries a cocycle twisted by the
boundary-completion holonomy.  Canonical mixed traces remain compatible with
tensoring this entire factor by an arbitrary canonical actor microstate.
Thus exactifying the lamp window has already extracted everything it can.
The smallest sufficient extra datum is an actor-normalized, asymptotically
separating copy Cartan; a fixed finite number of additional C2 labels leaves
a positive-density matrix block and cannot monomialize the cocycle.  Such a
growing Cartan is itself the missing finite probability carrier, so this
extra relation is action classicalization in equivalent form.

Property `(T)` of the Kun--Thom actor does not remove the exact fiber in the
current argument.  Property-`(T)` groups can have nontrivial finite-dimensional
unitary representations, and such a representation can be placed entirely
in the lamp commutant while all covariance laws remain exact.

## Two-site reduction

Full action recovery is stronger than the contradiction actually needed.
`two-point-approximation-fails` already forbids a permutation chart for the
single marked pair `(Gamma,hGamma)`.  The established
`two-site-a5-plancherel-center-separates-mark` supplies a canonical rational
two-valued field on those sites with exclusive-or mass `35/72` and all
pair-preserving covariance relations.  Thus the smaller open target
`two-site-a5-center-classicalization` asks only to permutationize the actor
multiplicity cocycle on that fixed separated carrier.  If it holds,
`nonhyperlinear-via-two-site-a5-center` reaches the goal without proving the
whole coordinate action sofic.

This reduction removes global lamp-label recovery but not actor
classicalization: approximate multiplication still has to be realized on a
finite state carrier.  It is therefore a genuine weakening of `(SHA2)`, not
a hidden invocation of the refuted two-point approximation.

## Attempts

- **Classicalize the amenable lamp base.**  This succeeds on every fixed
  lamp window by the published amenable-group theorem, but it does not keep
  the actor unitaries permutation-valued in the selected basis.
- **Use the minimal normal `A5` factors as sites.**  This recovers the
  permutation of the finitely many factors inside each regular packet, but
  the many regular packet copies form a multiplicity space which those
  factors do not distinguish.
- **Round actor normalizers to permutations.**  The exact Fourier-fiber model
  in `simple-lamp-normalizers-have-unitary-multiplicity-fibers` has zero
  covariance defect and stays asymptotically `sqrt(2)` from every monomial in
  the lamp basis, so such a rounding theorem is false without an additional
  multiplicity hypothesis.
- **Invoke property `(T)`.**  The obstruction may be an exact
  finite-dimensional representation in the commutant, so ordinary Kazhdan
  almost-invariant-vector rigidity does not touch it.  A relative cocycle or
  invariant-Cartan theorem strong enough to trivialize the copy action is the
  remaining possible attack.
- **Pass to the regular packet center.**  This removes every commutant unitary
  and remembers the coordinate-factor permutation, but
  `a5-center-spectrum-has-constant-one-site-hamming-gap` shows that one wrong
  site completion already costs `71/100` in Plancherel center measure.  The
  individual center fibers also fail chart injectivity on a `Z`-window with
  fixed probability `1-(59/60)^|Z|`.  Thus centers expose rather than solve
  the finite-window boundary: they need an already coherent global packet or
  a new equivariant bundling theorem.
- **Tensor several regular center packets.**  Fell absorption keeps the
  intrinsic center of the diagonal image Plancherel, but that does not erase
  the canonical center PVM of each tensor leg.  The latter sits in the
  multiplicity commutant and gives independent samples, with good window mass
  `(1-60^(-t))^|Z|` for `A5`; see
  `tensor-leg-centers-give-independent-plancherel-samples`.  Thus tensoring is
  not ruled out by the old center argument.  What remains is to extract and
  transport this reducing PVM coherently from arbitrary approximate packets,
  rather than from a supplied tensor factorization.
- **Absorb the actor gauge using residual-finite quotient packets.**  The
  exact calculation in
  `finite-quotient-fell-untwisting-leaves-kernel-cocycle` leaves a blockwise
  section cocycle valued in the finite-index kernel.  That kernel is
  nonamenable and carries the original arbitrary actor representation, so
  amenable lamp classicalization cannot remove it.
- **Use exact finite quotient expanders as a non-path carrier.**  This closes
  the word-path boundary but destroys the marked lamp profile.
  `exact-expander-a5-carriers-collapse-marked-center` proves uniformly that
  a `delta`-almost-`Gamma`-invariant binary center label in any genuine
  finite actor action has `h`-displacement at most `4 delta/kappa^2`, whereas
  the canonical two-site A5 field has displacement `35/72`.  Thus exact actor
  expansion is the wrong order of operations.  A live proof must extract the
  approximate actor permutations and the center labels together.

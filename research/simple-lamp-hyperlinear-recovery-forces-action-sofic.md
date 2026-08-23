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

Property `(T)` of the Kun--Thom actor does not remove the exact fiber in the
current argument.  Property-`(T)` groups can have nontrivial finite-dimensional
unitary representations, and such a representation can be placed entirely
in the lamp commutant while all covariance laws remain exact.

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
- **Tensor several regular center packets.**  This does not create independent
  Plancherel labels: `diagonal-tensor-powers-do-not-amplify-regular-lamp-center`
  proves `lambda_Q^(tensor t)` is merely an amplification of `lambda_Q`.
  The bad-fiber mass `(59/60)^|Z|` and the one-site `71/100` center gap are
  unchanged.
- **Absorb the actor gauge using residual-finite quotient packets.**  The
  exact calculation in
  `finite-quotient-fell-untwisting-leaves-kernel-cocycle` leaves a blockwise
  section cocycle valued in the finite-index kernel.  That kernel is
  nonamenable and carries the original arbitrary actor representation, so
  amenable lamp classicalization cannot remove it.

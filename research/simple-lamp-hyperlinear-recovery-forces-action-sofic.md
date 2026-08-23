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

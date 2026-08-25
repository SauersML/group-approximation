---
rg: 2
id: corona-coefficient-module-decoder
kind: claim
title: Decode compatible finite root multiplicities into one finite projective corona module
---

OPEN.  Let `R` be a countable ring with a binary Leavitt family and let
`rho:E_n(R)->U(Q_d)` be a norm-corona representation in which a specified
finite-order root `rho(x_ij(r_0))` survives.

Let `P_rho Q_d` be the common nonzero reducing projective carrier supplied by
`finite-root-windows-share-one-reducing-corona-carrier`.  Construct on that
carrier a unital ring homomorphism

```text
R -> End_(Q_d)(P_rho).
```

The finite additive and Heisenberg multiplicity germs already provide exact
finite restrictions of the desired action inside this literal common corner.
The missing content is a coefficient-intertwiner coherence theorem assembling
those compatible restrictions into the four Leavitt arrows.  Sparse escape,
carrier movement, and growth of the stabilization size are no longer part of
the problem.

## Structural reductions

- **Take the inverse limit of rank germs.**  Compatible scalar ranks do not
  determine compatible projection representatives or coefficient
  intertwiners.  The common projection `P_rho` is already a nonzero finitely
  generated projective module, but an inverse limit of multiplicity vectors
  still does not define operators on it.
- **Diagonalize the finite-window intertwiners independently.**  Every window
  now lies in `P_rho Q_d P_rho`, but its exactifying conjugator and irreducible
  matrix units may rotate inside that corner as the window grows.  Sharing
  the ambient projection does not make those internal matrix units nested.

## Remaining failed shortcuts

- **Use only the additive Fourier projections.**  This cannot recover the
  Leavitt arrows: one additive character can remain nontrivial on every
  prefix idempotent, so binary prefix projections do not split the active
  mass into two equivalent copies.
- **Exactify each finite Heisenberg window separately.**  This recovers each
  finite multiplication table on `P_rho`, but the correcting unitaries and
  isotypic corners may depend on the window.  Branching compatibility of rank
  germs does not make those internal decompositions nested or produce common
  coefficient operators.
- **Take an inverse limit of multiplicity vectors.**  The inverse limit gives
  a coherent type measure on the already fixed projective module, not bounded
  operators realizing the four Leavitt coefficients on that module.

- **Choose one nonzero irreducible summand at each growing finite window.**
  A rank-one projection on infinitely many coordinates already defines a
  nonzero finitely generated projective `Q_d`-module, so vanishing normalized
  density is not the obstruction here.  The obstruction is algebraic: an
  irreducible representation of one finite Heisenberg window supplies root
  unitaries and their multiplicity, but its summand need not be preserved by
  later coefficient arrows.  Selecting a new irreducible summand at each
  stage discards the common-carrier invariance just established.

- **Use both branch character labels to remove the marginal ambiguity.**
  `binary-leavitt-two-branch-character-restriction-is-faithful` proves that
  the pair of global restrictions `(F_0 chi,F_1 chi)` determines `chi`
  exactly: additively `R=Rt_0 directSum Rt_1`.  This removes label ambiguity
  but not projection coupling.  The two branch conjugators carry the selected
  atom into projections which need not lie in one common abelian spectral
  algebra, and the group relations give no controlled nonzero meet or common
  intertwiner.  The missing decoder can therefore be stated more sharply as
  a joint-coupling theorem for the two uniquely labelled branch projections,
  not as another character-separation lemma.

- **Make the sparse central atom reduce the self-copy subsystem.**
  `norm-corona-sparse-character-atom-reduces-pointwise-centralizer` strengthens
  sparse atom selection by slowing the moving character window until its full
  cylinder projection commutes with any prescribed countable pointwise
  centralizer.  Applied to the common central root, one nonzero projective
  carrier therefore reduces both Morita branch actors and every Heisenberg
  root in the self-copy subsystem.  What remains is not carrier invariance:
  the two reducing branch representations may still use independent tensor
  coordinates.  A coefficient-module decoder must turn their uniquely
  labelled joint action into the four Leavitt arrows on this carrier.

- **Treat common-carrier Heisenberg absorption as an exact firewall.**
  `orthogonal-heisenberg-self-copy-skeleton-has-marked-microstates` realizes
  both branch actors, every finite Heisenberg multiplication window, all
  transverse shears, and the nontrivial common central sign on the identity
  carrier of a matrix sequence.  The even/odd coordinate split also has the
  same faithful pair of branch character restrictions proved above.  Hence
  no theorem whose hypotheses stop at the common carrier, branch-label
  faithfulness, or Heisenberg-window compatibility can establish this node.
  The remaining intertwiner must be charged to a named mixed/opposite-root
  Steinberg occurrence which is absent from that exact UHF calibration and
  which erases the rectangular source/target object distinction.

- **Use the object-erasing range-sum fold on the common carrier.**
  `leavitt-range-sum-fold-is-first-object-erasing-row` identifies the first
  positive-root word which compares the source and doubled-target identities
  in one long-root coordinate.  This still cannot be the missing occurrence.
  `leavitt-range-sum-fold-does-not-pay-reynolds` keeps the fold exact on an
  auxiliary central-character factor while the packet payload remains
  rectangular.  More decisively,
  `finite-positive-root-fragments-have-marked-regular-models` uses the
  literal Leavitt coefficients and every shared occurrence: every finite
  positive-root fragment, including the fold, has an exact finite regular
  model with the marked root surviving.  Taking its full identity projection
  already gives a nonzero common reducing carrier.  Thus neither sparse
  carrier selection nor literal occurrence reuse promotes the fold to a
  coefficient module.  The first possible decoder row must leave the
  positive unipotent radical.

- **Add one non-scalar signed Whitehead cell.**
  This crosses to opposite roots but is still too small.
  `partial-whitehead-cell-has-marked-finite-model` specializes the complete
  prefix partial-equivalence table to the finite scalar Weyl cell while
  retaining the mark.  Hence the first possible payload return must couple
  both binary branches, destroy that scalar specialization, and tie the
  resulting mixed-root occurrence to the Heisenberg multiplicity being
  returned.  This is a strictly narrower target than an unspecified
  coefficient-intertwiner coherence theorem.

- **Close the sparse character in a finite parabolic orbit.**
  `surviving-leavitt-corona-character-has-infinite-parabolic-orbit` rules this
  out exactly.  For the full last-column root module, every nontrivial global
  character atom has infinitely many pairwise orthogonal conjugates under
  just one upper-left root subgroup.  Finiteness would create a nonzero
  finite-dimensional right module over the binary Leavitt algebra.  The
  corona can absorb the infinite orbit at vanishing coordinate density: the
  resulting projective inequalities are `M[P]<=[1]` for every fixed `M`, not
  the required `2[P]<=[P]`.  Thus the mixed-root return must fold an infinite
  orbit, not close a bounded menu of atoms.

- **Iterate the branch until multiplicity outruns the matrix dimension.**
  At every fixed depth `N`, the transverse shear gives a rank inequality of
  the form

  ```text
  2^N rank(P_n) <= d_n
  ```

  on sufficiently late coordinates.  Letting `N` tend to infinity only after
  the corona-coordinate limit forces normalized character mass to zero; it
  does not make the operator norm of a surviving rank-one projection small.
  Choosing `N=N(n)` after seeing `d_n` is not justified by pointwise corona
  relations: the relator defect can converge arbitrarily slowly compared with
  `d_n`, and simultaneous exactification constants grow with the moving
  window.  Such a moving-depth argument would need the same bounded-cost
  prototype or return-row control isolated in
  `binary-leavitt-three-row-atomic-compiler` and
  `opnorm-leavitt-coarse-fine-return-row`.

The unresolved statement is now a two-branch mixed-root return theorem:
compatible finite Heisenberg multiplicities, already aligned inside one
fixed Morita carrier, must admit a common summand on which a non-scalar
opposite-root/Whitehead occurrence authenticates the coefficient products.
All-positive-root coherence, even with the object-erasing fold, is below the
proved finite-regular-model firewall.

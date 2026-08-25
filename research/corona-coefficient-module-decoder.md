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

The unresolved statement is an intertwiner-coherence theorem: compatible
finite Heisenberg multiplicities, already aligned inside one fixed Morita
carrier, must admit a common summand on which the coefficient products act
coherently.

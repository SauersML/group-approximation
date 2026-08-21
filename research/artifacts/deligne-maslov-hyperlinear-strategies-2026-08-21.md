# Deligne--Maslov routes to an explicit non-hyperlinear group

Date: 2026-08-21

## Executive cut

The graph already attacks non-hyperlinearity through full Hilbert--Schmidt
stability of an S-arithmetic base, Iwahori matching, Schur/Clifford
multiplicity, K-theoretic index marks, traffic distributions, de Finetti,
coherent configurations, and several finite-packet compilers.  The useful new
move is therefore not another source of almost representations.  It is to
shrink the *amount of stability that must be proved*.

Take the connected three-fold cover of `Sp_4(R)` and let

```text
1 -> <z> = Z/3 -> E_3 -> Sp_4(Z) -> 1                 (D1)
```

be the inverse image of `Sp_4(Z)`.  Deligne's theorem says that `E_3` is not
residually finite; in fact every finite quotient kills the full central
`Z/3`.  Because the image of a finite-dimensional unitary representation of a
finitely generated group is a finitely generated linear group, Malcev residual
finiteness upgrades this to

```text
rho(z)=1 for every rho:E_3 -> U(d).                  (D2)
```

Thus exact finite-dimensional representation theory has already erased the
mark we want to preserve.  Hyperlinearity would do the opposite: canonical
microstates for the nontrivial word `z` keep it a fixed normalized-HS distance
from `1`.  It is enough to prove the one-word implication

```text
presentation defect -> 0  ==>  ||phi(z)-1||_2 -> 0. (D3)
```

This is strictly weaker than HS stability, flexible HS stability, local HS
stability, or repair of every generator.  It is the smallest metric upgrade of
Deligne's exact finite-residual theorem that can possibly solve the problem.

The rest of this note gives three attacks on `(D3)`, with an explicit novelty
audit against existing Cairn lanes.

## Literature anchors

- Deligne, *Extensions centrales non residuellement finies des groupes
  arithmetiques*, C. R. Acad. Sci. Paris 287 (1978), A203--A208.
- Stover, *Residual finiteness and discrete subgroups of Lie groups*,
  arXiv:2407.07680, Theorem 1.5: for `g>=2`, `n>=3`, the preimage of
  `Sp_(2g)(Z)` in the connected `n`-fold cover is a non-residually-finite
  `Z/n` central extension; the finite residual contains the image of `2Z`.
  For `n=3`, multiplication by two is invertible, so the whole central
  `Z/3` lies in the finite residual.
- Benson--Campagnolo--Ranicki--Rovi, *Cohomology of symplectic groups and
  Meyer's signature theorem*: the pullback of the universal cover is the
  integral central class, and the Meyer cocycle is four times its generator
  (with the stated low-genus qualification for `g=2`).  Reduction mod `3`
  therefore gives a concrete nonzero multiplier for `(D1)` because four is a
  unit mod `3`.
- Funar--Pitsch, arXiv:2004.04129, gives a modern finite-quotient/K-theoretic
  route back to Deligne's theorem and clarifies that finite symplectic
  quotients see at most the metaplectic two-torsion.
- Fournier-Facio--Gerasimova--Spaas, arXiv:2307.13155 / J. Algebra 663
  (2025), prove that an infinite hyperlinear property-(T) group cannot be
  locally HS-stable.  This is a useful fallback, but `(D3)` asks for much
  less than local stability.
- Spaas, *Hilbert--Schmidt stability for graph products*, arXiv:2603.02058
  (2026), proves same-dimension HS stability for graph products of abelian
  groups over chordal graphs.  That theorem is a new exactification tool for
  the root-chart attack below.

## Route A: fixed Maslov multiplier, not full group stability

Choose a finite presentation of `E_3` with central generator `z` and a section
of the quotient `Gamma=Sp_4(Z)`.  The multiplication law of the section is
encoded by a `Z/3`-valued 2-cocycle `alpha`; one may take the reduction of the
universal-cover/Maslov class.

An approximate representation of `E_3` has an almost order-three, almost
central unitary `Z=phi(z)`.  Functional calculus first rounds `Z` to exact
order three.  Its spectral projections

```text
P_0, P_1, P_2,        Z = P_0 + omega P_1 + omega^2 P_2,
omega=e^(2 pi i/3),                                      (A1)
```

are then almost invariant under the generator images.  The off-diagonal
matrix blocks are quantitatively controlled because the three eigenvalues in
`(A1)` have a fixed separation.  Polar correction inside each `P_j` therefore
turns the original tuple, at asymptotically no weighted HS cost, into three
projective almost-representations of `Gamma` with multipliers

```text
1, alpha, alpha^2.                                      (A2)
```

This gives a sharp reformulation of `(D3)`:

> prove a dimension-free positive relator-defect gap for the two nontrivial
> Maslov sectors `alpha` and `alpha^2`.

No exact **finite-dimensional** projective representation in either sector can
exist: such a representation is the same as a finite-dimensional exact
representation of `E_3` on which `z` acts as `omega` or `omega^2`, contradicting
`(D2)`.  The twisted regular representation still exists in infinite dimension.
The missing theorem is a *quantitative isolation of the finite-dimensional
projective representation varieties* from zero defect, uniformly in matrix
dimension.

This is not full HS stability.  We never need to find a nearby exact
`Sp_4(Z)` representation, and the trivial sector may behave arbitrarily.  We
only need to prove that a fixed nonzero projective cohomology class cannot be
realized with vanishing normalized-HS curvature.

### Analytic forms worth trying

1. **Twisted Fox Laplacian.**  Linearize the presentation at a putative
   `alpha`-projective tuple.  The scalar gauge direction is removed by the
   fixed multiplier.  Seek a uniform lower bound for the smallest singular
   value of the twisted Fox Jacobian on the orthogonal complement of genuine
   infinitesimal symmetries.  A bound independent of matrix dimension would
   give a Newton/implicit-function exclusion because the exact target variety
   is empty.

2. **Maslov curvature energy.**  Use the explicit signature/Maslov cocycle to
   build a finite collection of Lagrangian-triple identities whose total
   mod-three curvature is one.  Convert a nonzero curvature class into a sum
   of squared HS relator errors.  The desired inequality has the schematic
   form

   ```text
   1 <= C * sum_r ||r(U)-omega^(k_r) I||_2^2.           (A3)
   ```

   Unlike a determinant obstruction, `(A3)` is density-sensitive.

3. **Property-(T;FD) only after sectorization.**  Rather than use property T
   to repair the whole tuple, use it to keep spectral mass from leaking
   between `P_1`/`P_2` and the trivial sector while performing local root
   repairs.  This is a much narrower role for spectral gap than in the
   Iwahori route.

## Route B: chordalize the C2 root charts and leave one holonomy cycle

The symplectic group is generated by elementary root subgroups.  In rank two
(type `C2`) each root subgroup is a copy of `Z`; many pairs commute, and the
remaining rank-two Chevalley relations are concentrated in a small root
incidence complex.  This suggests treating the presentation as a collection
of *commuting charts* plus a small amount of noncommutative glue.

Spaas's 2026 theorem gives a new tool here: whenever the commutation graph of
a collection of abelian vertex groups is chordal, all its approximate
relations can be exactified in the same dimension.  The proposed compiler is:

1. choose a finite `C2` Steinberg/Matsumoto presentation adapted to the
   mod-three universal-cover cocycle;
2. cover the root-commutation graph by chordal induced subgraphs;
3. HS-exactify every chordal chart, preserving matrix dimension;
4. synchronize overlaps by the central spectral projections from `(A1)`;
5. leave only the minimal induced non-chordal cycle(s);
6. identify the mod-three Meyer--Maslov class with holonomy around one such
   cycle and prove that nontrivial holonomy has a fixed HS energy cost.

The point is architectural: chordal stability should delete most of the
presentation from the analytic problem.  What remains is not "stability of
`Sp_4(Z)`" but a finite rank-two holonomy inequality.

A falsification test is built in.  If the chosen root-commutation cover can be
made globally chordal without retaining a cycle carrying the cocycle, then it
cannot see the Deligne class and the compiler is useless.  The central class
must survive exactly in the non-chordal residue.

## Route C: a finite-subgroup representation-cone atlas

There is a second way to use finite-dimensionality without trying to repair
the whole arithmetic group.  Restrict a projective almost-representation to
many *finite* torsion subgroups.  On a complete multiplication table Gowers--
Hatami gives flexible normalized-HS exactification with universal constants,
so each local chart becomes a genuine projective representation of a finite
group.  Genuine finite-group projective representations have discrete
multiplicity vectors.

The proposed computation is therefore a representation-ring atlas:

1. start from Bender's two-generator/eight-relator presentation of
   `Sp_4(Z)` and enumerate a useful family of finite subgroups generated by
   short torsion words;
2. pull the mod-three Maslov multiplier to each finite subgroup and enumerate
   its projective irreducibles;
3. compute restriction matrices on subgroup overlaps;
4. form the positive rational cones of compatible multiplicity vectors;
5. search for a homogeneous separating functional showing that any local
   system carrying positive `alpha`-sector mass must pay a *fixed fraction*
   of mismatch on at least one overlap.

The last phrase is essential.  A mere congruence or divisibility obstruction
costs `O(1)` dimensions and vanishes after normalized-HS scaling.  What is
needed is a cone separation of the form

```text
sum_edges ||Res_e(m_source)-Res_e(m_target)||_1
     >= c * sum_vertices ||m_vertex||_1,                 (C1)
```

for all nonzero nonnegative multiplicity vectors in the nontrivial central
sector.  Such an inequality is stable under the `o(d)` flexible enlargement
in Gowers--Hatami and converts directly into positive-density HS mismatch.

This route is deliberately finite and computational: character tables,
twisted Schur multipliers, restriction matrices, and a rational LP dual
certificate.  It resembles the repository's finite-packet philosophy but
uses the classical torsion geometry of `Sp_4(Z)` rather than an engineered
BCS/Schur packet.

A useful negative guardrail: a plain positive-definite/tracial moment SDP
cannot by itself exclude the multiplier.  The twisted left-regular
representation exists in infinite dimension, so the twisted group algebra
has a perfectly valid canonical trace.  Any successful certificate must use
**finite-dimensional multiplicity structure**, not positivity valid in every
tracial von Neumann algebra.

## A tempting route that should *not* be promoted yet: fermionic determinant amplification

Exact commutator identities can force determinant divisibility conditions on
an exact projective representation.  One might try to amplify a determinant
phase into normalized trace using exterior powers or fermionic Fock space.
This looks attractive because a phase on one eigenvalue affects a positive
fraction of `Lambda^(theta d)`.

The obstacle is equally clear: exterior power is not dimension-free
Lipschitz in normalized HS metric when the degree grows with `d`.  Taking a
large enough exterior power to amplify a low-rank determinant defect also
amplifies the relator error.  Without a new dimension-free second-quantization
inequality, this just moves the normalization problem.  Record it as a
negative lead, not a Cairn route.

## Novelty audit against the current graph

- **Versus `hs-stability-forces-nonhyperlinear-central-extension`.**  That
  theorem assumes HS stability of a base with (T;FD) and then manufactures a
  bad finite central extension.  Here the extension is fixed first (`E_3`),
  and the desired analytic statement is only collapse of its one central
  word.
- **Versus the Iwahori lane.**  Iwahori tries to glue two exactified
  `SL_2(Z)` vertex representations to establish stability of
  `SL_2(Z[1/p])`.  The present lane works in `Sp_4(Z)` and only excludes two
  fixed projective multiplier sectors.
- **Versus Exel--Loring / K-theory lanes.**  Those detect winding or index in
  almost commuting matrices/coronas.  The Maslov multiplier is a group
  cohomology class attached to the symplectic universal cover; the proposed
  gap is a normalized-HS projective curvature inequality.
- **Versus `quantum-context-frame-index`.**  That node uses finite BCS/frame
  parity and real/Pfaffian refinements.  Here no contextuality packet is
  required; the nontrivial class is the classical Meyer--Maslov class.
- **Versus existing finite-dimensional-invisible Steinberg marks.**  Those
  marks are engineered through Leavitt/Toeplitz coefficient algebras.  The
  Deligne mark is classical and arithmetic.  The new content is exploiting
  its explicit projective cocycle and symplectic root geometry to obtain the
  missing HS collapse.

## Recommended experimental order

1. Write an explicit finite `Sp_4(Z)` / `E_3` presentation and compute the
   mod-three cocycle on the relators.  This is algebraic and falsifiable.
2. Run a small-dimensional nonlinear optimization for the `alpha` and
   `alpha^2` projective relator energies.  Look for a floor rather than for
   approximate solutions.  If the floor decays with dimension, Route A in its
   strongest form is false.
3. Compute the root-commutation graph of the chosen presentation, enumerate
   minimal chordal covers, and test whether the cocycle support can be pushed
   onto one induced cycle by changing section (coboundary gauge).
4. In parallel, enumerate finite torsion-subgroup charts from short Bender
   words, compute twisted projective character tables/restriction matrices,
   and solve the rational cone-separation LP `(C1)`.

The decisive feature is that every experiment attacks the *same* precise
quantity: the normalized-HS defect floor of the mod-three Maslov projective
sector.  A numerical decay falsifies the route early; a stable floor gives a
concrete theorem to prove.

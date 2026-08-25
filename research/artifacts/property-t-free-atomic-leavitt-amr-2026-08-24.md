# Property-(T)-free Leavitt MF collapse: atomic integration audit

Integrated 2026-08-24.  This artifact records how the supplied Atomic
Leavitt Gap / Atomic Morita Return note is represented in the Cairn graph.
It preserves the note's honesty boundary: the finite-matrix endpoints below
are proved, while the literal binary-Leavitt same-atom decoder is open.

## 1. New established endpoint: the Atomic Leavitt Gap

For every nonzero projection `p in M_d(C)`, every `m>=2`, and every
`s_i,t_i in pM_d(C)p`,

```text
m-1
 <= sum_i ||t_i s_i-p||_op
    + ||sum_i s_i t_i-p||_op.                         (1)
```

The proof uses `tau_p=Tr/rank(p)` and cyclicity.  It is independent of the
ambient dimension and of `rank(p)/d`.  In the binary case the maximum of the
three relevant defects is at least `1/3`.

Cairn nodes:

- `atomic-leavitt-gap-on-nonzero-matrix-corner`;
- `atomic-leavitt-gap-on-nonzero-matrix-corner-proof`.

The same nodes record the corona corollary: no nonzero norm-matrix-corona
corner carries an exact Leavitt family.  This is a quantitative
coordinatewise strengthening of the stable-finiteness endpoint.

## 2. New established conditional theorem: Atomic Morita Return

For a finitely presented group `Gamma=<S|R>` and a finite-order word `w`,
AMR prescribes a nontrivial rounded spectral projection `p_U` of `w(U)`
before coefficient operators are selected.  On every nonzero such
projection it requires

```text
||t_i s_i-p_U||_op <= eta(delta),              i=0,1,
||s_0t_0+s_1t_1-p_U||_op <= eta(delta),
eta(delta)->0.                                         (2)
```

The atomic gap makes `(2)` impossible in any surviving corona coordinate.
Thus `w in Rad_MF(Gamma)`; normal generation gives total MF radical.

Cairn nodes:

- `atomic-morita-return-kills-finite-order-mf-mark`;
- `atomic-morita-return-collapse-proof`.

This statement incorporates the note's diagonal-gluing observation.  The
address and finite coefficient window may vary with the coordinate.  There
is no inverse-limit compatibility requirement and no carrier-density
requirement.

## 3. Literal binary-Leavitt frontier

The nontrivial involution is

```text
z=x_13(q),                       q=s_1t_1,
```

in the fixed finite presentation of
`St_20(L_(F_2)(1,2))`.  The prescribed atom is the nontrivial spectral
projection of the rounded `z` coordinate.

The exact open target is now:

- `binary-leavitt-atomic-morita-return`.

Its concrete moving-address attack is:

- `binary-leavitt-three-row-atomic-compiler`;
- `binary-leavitt-atomic-return-via-three-row-compiler`.

The compiler asks for finitely many prototype discrepancy words and a
dimension-independent bound for the two inverse rows and completeness row.
Remote checks must be literal conjugates of the prototypes, so arbitrary
address length is free in operator norm.  The generic implication is
recorded by:

- `bounded-prototype-rows-imply-atomic-morita-return`;
- `bounded-prototype-row-compiler-proof`.

Finally,
`property-t-free-leavitt-via-atomic-morita-return` connects this open leaf to
the top-level goal using
`full-leavitt-idempotent-defect-saturation`.

The failure modes are part of the open nodes, not hidden assumptions:

- separately exact typed packets admit `rectangular-escape`;
- the three-elementary prefix swap does not identify packet identities;
- fixed typed PI and Reynolds data do not recover the prescribed carrier;
- a functorial group-algebra selector would also act in the regular finite
  trace and therefore proves too much;
- normalized-HS leakage can vanish on a carrier where operator leakage is
  exactly one.

## 4. Existing Cairn results reused instead of duplicated

The supplied cyclic rank-product theorem is the general form of
`operator-norm-rank-monodromy-zero`.  That node and its proof were extended
from the constant equation `a^k r=b^k r` to arbitrary rational fractions

```text
alpha_i r_i=beta_(i+1)r_(i+1),
prod_i alpha_i=prod_i beta_i.                          (3)
```

The coarse/fine `1/2` versus `1/4` cycle is its binary specialization.
The one-row version remains
`rank-deficient-return-row-has-operator-norm-one`.

The supplied finite-packet linearity no-go is already subsumed by
`finite-rational-rank-flows-are-fd-dense` and
`finite-corona-dimension-certificate-calculus`.  The former now states the
unnormalized rational-polyhedral cone corollary explicitly: a nonzero real
solution to fixed homogeneous rational multiplicity constraints scales to a
nonzero integer solution.  Hence fixed semisimple packet bookkeeping needs a
nonlinear holonomy/operator return or another integral exit.

The existing selector route remains distinct:

- `opnorm-leavitt-coarse-fine-return-row`;
- `authenticated-coarse-fine-return-forces-mf-collapse`.

It asks for exact `M_2` and `M_4` packets with one identity and a vanishing
support row.  AMR asks for no exact packet systems and instead returns three
coefficient equations on the prescribed root atom.

## 5. Exact self-copy theorem and calibrations

For the Heisenberg law

```text
(a,b,c)(a',b',c')=(a+a',b+b',c+c'+ab'),
```

the two Leavitt branch maps

```text
alpha_i(a,b,c)=(a t_i,s_i b,c)
```

are injective, have commuting images, intersect in the central third-root
subgroup, and generate the whole Heisenberg group.  Prefix iteration gives
`2^n` commuting self-copies.  Over a finite coefficient field this
Heisenberg group is locally finite.

Cairn nodes:

- `binary-leavitt-heisenberg-is-orthogonal-central-self-copy`;
- `binary-leavitt-heisenberg-central-self-copy-proof`.

The separate finitary elementary calibration is:

- `orthogonal-root-self-copy-is-mf-compatible`;
- `orthogonal-root-self-copy-mf-calibration-proof`.

It records that `E_fin(F_q)` is locally finite/MF, has two commuting
infinite block copies, has the full Steinberg calculus, and is normally
generated by any nontrivial root.  Therefore the raw slogan

```text
orthogonal self-copy + root calculus + normal generation
```

is false as a non-MF criterion.  Same-atom return is the structural dividing
line.

## 6. Status after integration

Established:

- the `m`-ary atomic operator-norm gap;
- no nonzero Leavitt corner in a norm matrix corona;
- AMR implies MF-radical membership and normal-generation collapse;
- the lossless bounded-prototype compiler implication;
- general cyclic rank-product obstruction;
- fixed rational-linear multiplicity scaling no-go;
- exact orthogonal Heisenberg self-copy and its local-finiteness calibration.

Open:

- return the three binary coefficient rows to the prescribed nonzero
  `x_13(s_1t_1)` spectral atom in the literal binary-Leavitt Steinberg
  presentation;
- concretely, build the bounded three-row prototype compiler.

No node created by this integration claims an unconditional
property-`(T)`-free non-MF group.

## 7. Exact finite-dimensional character mechanism and its precise boundary

The global Heisenberg argument is represented by:

- `leavitt-heisenberg-branch-doubles-character-multiplicity`;
- `leavitt-heisenberg-branch-doubles-character-multiplicity-proof`.

For branch pullback `F` and the transverse shear character `eta`, the exact
finite-dimensional multiplicities satisfy

```text
m(F chi) >= p m(chi).
```

Finite support then contradicts maximal multiplicity.  This is an exact-only
result: `leavitt-character-mass-escapes-to-finer-characters` records that a
finite window sees two marginals of a joint character distribution, not one
global multiplicity function.

Two further statements now sharpen that boundary.

- `finite-branch-closure-erases-transverse-character` proves that an
  injective branch on a finite invariant coefficient packet is automatically
  surjective, so every dual character killed by branch pullback is zero.
  Closing the finite window destroys the transverse direction.
- `norm-corona-sparse-global-character-atom` proves that a surviving element
  of a countable elementary abelian `2`-group nevertheless has a nonzero
  global character projection in the norm corona.  The projection may be
  rank one and have zero normalized mass.  The remaining failure is not lack
  of an atom: it is that the returned copies can lie in a larger multiplicity
  sector rather than inside the selected atom itself.

Thus the exact boundary is:

```text
global sparse atom                         established;
same-reservoir multiplicity return        open.
```

## 8. Bounded-area chromatic compactness

The second finite-coordinate endpoint added by the full audit is:

- `bounded-relator-area-controls-opnorm-word-defect`;
- `infinite-chromatic-commutator-code-kills-mf-mark`.

If a finite presentation exposes an infinite-chromatic graph of words with
diagonal commutator `z` up to uniformly bounded relator area and off-diagonal
edge commutator `1` with the same kind of bound, a finite operator-norm cover
of `U(d)` colors the vertices.  A monochromatic edge makes the two first
commutator entries arbitrarily close.  The commutator map is `2`-Lipschitz,
so

```text
||z(U)-I||_op <= (A_Delta+A_0) Def_R(U).
```

The theorem therefore kills `z` in every norm matrix corona.  Its finite
version uses the covering number `N_d(delta)` and gives

```text
||z(U)-I||_op
 <= (A_Delta+A_0) Def_R(U)+2 delta
```

whenever the graph chromatic number exceeds `N_d(delta)`.

The literal Leavitt compiler is the new open node
`binary-leavitt-bounded-area-chromatic-code`, connected to the top goal by
`property-t-free-leavitt-via-chromatic-code`.  It is distinct from Atomic
Morita Return: no coefficient projection is decoded.

The obstruction to the naive two-transitive wreath/Thompson realization is
already captured by:

- `stabilizer-generator-control-has-unbounded-address-loss`;
- `two-transitive-occurrence-sections-have-unbounded-pair-holonomy`.

Finitely many orbits on pairs do not give uniformly bounded presentation
area.  Different names for one address differ by an arbitrary stabilizer
word, and generator-wise covariance telescopes with its word length.  Passing
from two- to three-transitivity merely moves the same problem to a smaller
stabilizer.

## 9. Exact branching, recurrence, and firewalls already in Cairn

The remaining major theorems and no-go statements in the full report were
already represented and are not duplicated.

| Mathematical content | Cairn node |
|---|---|
| supercritical finite-state projective branching vanishes in a matrix corona | `exact-corona-branching-dimension-collapse` |
| cyclic rational rank monodromy forces zero carrier | `operator-norm-rank-monodromy-zero` |
| rank-deficient return has operator norm one | `rank-deficient-return-row-has-operator-norm-one` |
| a uniformly authenticated conjugacy-to-power return kills the mark | `spectral-recurrence-power-return-non-mf-criterion` |
| fixed rational homogeneous multiplicity flow scales to an integer model | `finite-rational-rank-flows-are-fd-dense` |
| ordinary HNN conjugacy cannot remove Schur multiplicity | `hnn-conjugacy-cannot-return-schur-morita-multiplicity` |
| a fixed finite packet retains an arbitrary multiplicity gauge | `fixed-packet-correction-retains-multiplicity-gauge` |
| orthogonal root self-copy and normal generation can remain MF | `orthogonal-root-self-copy-is-mf-compatible` |
| full dual-prefix growth needs two Morita branches | `dual-prefix-growth-needs-two-morita-branches` |
| bounded high-chromatic Carmichael area gives the tracial analogue | `bounded-area-high-chromatic-conjugacy-collapse` |

The regular-trace firewall in
`universal-block-return-violates-the-regular-firewall` now includes the
marked-involution specialization.  For a nontrivial involution `z`, the left
regular spectral projection `(1-lambda(z))/2` has trace `1/2`; two orthogonal
copies of it cannot lie under itself.  Hence no representation-functorial
group-algebra formula can manufacture the desired Cuntz/Leavitt corner.  A
successful selector must use finite-coordinate information.

The one-shift recurrence shortcut is excluded algebraically: if `[T,B]=1`,
then

```text
[TAT^(-1),B]=T[A,B]T^(-1).
```

Requiring the left side to be `1` while `[A,B]=Z` already forces `Z=1`.
This is not a missing estimate but an inconsistent marked presentation.

The Bott and unnormalized Schatten routes remain contextual exclusions, not
open Cairn dependencies.  Survival of a group element does not force a
nonzero Bott class in the small-commutator regime, and
`||E||_p <= d^(1/p)||E||_op` prevents unnormalized Schatten
non-approximability from following from operator-norm microstates.

## 10. Final integrated frontier

For

```text
Delta=St_20(L_(F_2)(1,2)),            z=x_13(s_1t_1),
```

the following are established:

1. `z` is a nontrivial involution and normally generates `Delta`;
2. the Atomic Leavitt Gap and rank-deficient return are dimension-free;
3. exact Heisenberg character multiplicity doubles and therefore vanishes;
4. finite-window closure cannot retain its transverse character;
5. sparse global norm-corona character atoms can be selected;
6. exact supercritical projective branching collapses;
7. a bounded-area infinite-chromatic commutator code kills its mark.

The unconditional statement

```text
Rad_MF(Delta)=Delta
```

remains open.  It would follow from either of two concrete finite-presentation
compilers:

1. return the three binary Leavitt rows to the prescribed nonzero spectral
   atom (`binary-leavitt-three-row-atomic-compiler`); or
2. realize the marked root as a bounded-area infinite-chromatic commutator
   code (`binary-leavitt-bounded-area-chromatic-code`).

The exact unresolved object is therefore a finite-coordinate authenticated
return, not another exact finite-dimensional contradiction.

## 11. The formal predicate has a cardinal-width boundary

The Lean predicate `IsOperatorMF` is universe-polymorphic and uses a sequence
indexed by the natural numbers.  Its unrestricted set-theoretic consequence
is now represented by:

- `finite-matrix-quotient-cardinality-width-bound`;
- `sequential-operator-mf-continuum-cardinality-bound`.

For an index set `J`, every quotient of `product_(j in J) U(d_j)` has
cardinality at most

```text
continuum^|J|.
```

In particular every sequential norm matrix corona has at most continuum many
unitaries.  Hence a group satisfying the unrestricted formal predicate has
cardinality at most the continuum.

This distinction does not alter the standard countable MF theorem or the
countable Leavitt frontier.  It records that extending a sequential predicate
to arbitrary-cardinality groups introduces an information-width obstruction
that is invisible on countable sources.

## 12. An unconditional uncountable example

The claim
`huge-elementary-abelian-two-group-is-not-sequential-operator-mf` records the
exact consequence.  If `|I|>continuum`, then

```text
E_I=directSum_(i in I) C_2
```

cannot embed in a sequential matrix corona.  It is nevertheless abelian,
exponent two, locally finite, amenable and residually finite.  It has no
property `(T)`: every finite candidate Kazhdan set uses only finitely many
coordinates, while a character on a fresh coordinate fixes that set exactly
and remains nontrivial.

This is an unconditional theorem for the unrestricted formal predicate, not
a solution of the countable problem.  The graph keeps those scopes separate
in the claim title, statement and `distinct_from` field.

## 13. A structural non-Kazhdan wrapper

The established claim
`non-mf-times-infinite-cyclic-is-non-mf-and-nonkazhdan` says that for any
countable non-MF seed `B`,

```text
B x Z
```

is again non-MF and does not have property `(T)`.  Non-MF follows by
restricting any hypothetical embedding to `B`; failure of property `(T)` is
witnessed directly by characters of the cyclic coordinate.  Finite generation
and finite presentation are preserved.

The node explicitly records the provenance boundary: this makes the resulting
group non-Kazhdan but does not replace whichever analytic argument established
the seed's non-MF property.

## 14. Residual finiteness blocks pure conjugacy hashing

The new general no-go theorem is
`rf-conjugacy-difference-graphs-finitely-colorable`.
For a residually finite actor `H` and finitely many nonidentity prototypes
`w_1,...,w_r`, join `x,y in H` when `x^(-1)y` is conjugate to one of the
`w_i^(+1 or -1)`.  A product of finite quotients separating all prototypes
colors this graph properly.

This is stronger in one direction and weaker in another than
`finite-quotients-bound-carmichael-conjugacy-chromatic-number`.  It needs no
Carmichael relations but assumes the edge relation comes from finitely many
literal conjugacy differences.  Together with the regular-trace firewall it
creates two clean design walls:

```text
universal exact proper-infinite branching   blocked by regular trace;
finite pure-conjugacy chromatic hashing     blocked by residual finiteness.
```

The live countable corridor therefore requires an approximation-specific
return, bounded-area holonomy beyond pure conjugacy differences, a suitable
stability theorem, or another finite-coordinate mechanism.

# Five-equation linear systems and minimal nonhyperlinear groups (2026-09-16)

Swarm lane `hi-coun-non-hyperlinear-group`, angle: counterexample and
minimal-counterexample analysis for the root `non-hyperlinear-group`.

This artifact carries the complete proofs behind two claims.
- `lcs-with-at-most-five-equations-has-no-ru-gap` (Part I): an exact
  classification of the binary linear systems with at most five equations whose
  solution group has `J != 1`. All of them have an operator solution of
  dimension 1 or 8. So any tracial/non-`R^U` gap system, which is what
  Paddock--Slofstra's Proposition 5.8 turns into a finitely presented
  nonhyperlinear group, needs at least six equations.
- `minimal-nonhyperlinear-group-structure` (Part II): structural restrictions on
  a group that is not hyperlinear but all of whose proper subgroups are.

Scripts: `experiments/lcs-five-equations-2026-09-16/` (`verify.py`,
`census6.py`, with their outputs `verify.out`, `census6.out`).

## Part I. Binary linear systems with at most five equations

### I.0 Conventions

Let `A in F_2^(m x n)` and `b in F_2^m`. The solution group is

```text
Gamma(A,b) = < x_1,...,x_n, J |  x_j^2 = J^2 = [x_j,J] = 1,
                                 [x_j,x_k] = 1  if A_ij = A_ik = 1 for some i,
                                 prod_(j : A_ij = 1) x_j = J^(b_i)  for all i >.
```

The product in row `i` is well defined because its factors pairwise commute. An
empty row reads `1 = J^(b_i)`. An **operator solution of dimension `d`** is a
homomorphism `rho : Gamma(A,b) -> U(d)` with `rho(J) = -I`. The support of a
column `A_j` is `supp A_j = {i : A_ij = 1}`, and `[m] = {1,...,m}`.

A **parity certificate** is a vector `y in F_2^m` with `y^T A = 0` and
`y^T b = 1`. Over a field, `Ax = b` has no solution iff a parity certificate
exists, because `b` lies in the column space iff it is orthogonal to the left
kernel.

### I.1 Statements

**Theorem LCS5.** Let `m <= 5`. The following are equivalent.

1. `J != 1` in `Gamma(A,b)`.
2. `Gamma(A,b)` has an operator solution of dimension 1 or 8.
3. Either `Ax = b` has a solution in `F_2^n`, or all of the following hold:
   - `m = 5`;
   - every column of `A` has even weight;
   - every 2-subset of `[5]` is the support of some column of `A`;
   - `b_1 + ... + b_5 = 1`.

**Theorem CERT** (any `m`). Let `y` be a parity certificate for `(A,b)` with
support `S`. Suppose either `|S| <= 4`, or `|S| = 5` and some 2-subset of `S`
is not of the form `supp A_j cap S`. Then `J = 1` in `Gamma(A,b)`.

**Corollary.** Let `(A,b)` be a binary linear system that is tracially
satisfiable but not `R^U`-satisfiable, in the sense of
`lcs-tracial-ru-gap-equiv-nonhyperlinear` (Paddock--Slofstra, Lemma 5.7).
1. It has at least six equations.
2. It has no classical solution, and every parity certificate `y` has
   `|supp y| >= 5`.
3. If `|supp y| = 5`, the restrictions `supp A_j cap supp y` realize all ten
   2-subsets of `supp y`.

There is no restriction on the number of variables.

### I.2 Subsystems and the incidence group

**Lemma 1 (subsystems).** For `S subset [m]`, let `Gamma_S = Gamma(A_S, b_S)`,
where `A_S` keeps the rows in `S` and all `n` columns. The identity on
generators induces a homomorphism `Gamma_S -> Gamma(A,b)` with `J |-> J`. So
`J = 1` in `Gamma_S` implies `J = 1` in `Gamma(A,b)`.

*Proof.* Every defining relation of `Gamma_S` is a defining relation of
`Gamma(A,b)`. ∎

Now fix a parity certificate `y` with support `S`. For each column `j`, put
`s_j = supp A_j cap S`. Since `y^T A_j = |s_j| mod 2 = 0`, every `s_j` has even
size. Let `C` be the **set** of nonempty `s_j`, with repetitions identified.
The **incidence group** of `(S,C)` is

```text
H(S,C) = < xi_c (c in C) |  xi_c^2 = 1,
                            [xi_c, xi_d] = 1   whenever c cap d != empty,
                            gamma_v is central for every v in S >,
gamma_v := prod_(c in C, v in c) xi_c.
```

The product `gamma_v` is well defined because its factors pairwise commute:
they all contain `v`.

**Lemma 2 (transfer).** There is a homomorphism `psi : H(S,C) -> Gamma_S` with
`psi(gamma_v) = J^(b_v)` for all `v in S`. Hence, if `prod_(v in S) gamma_v = 1`
in `H(S,C)`, then `J = 1` in `Gamma_S`, and so in `Gamma(A,b)`.

*Proof.* Put `psi(xi_c) = prod_(j : s_j = c) x_j`. Check the relations:
- Fix `v in c`. Every `x_j` with `s_j = c` occurs in row `v` of `Gamma_S`, so
  these factors pairwise commute, and `psi(xi_c)` is an involution.
- If `v in c cap d`, all factors of `psi(xi_c)` and of `psi(xi_d)` occur in
  row `v`, so the two products commute.
- The variables of row `v` are exactly the `x_j` with `v in s_j`, that is, the
  factors of the `psi(xi_c)` with `c` containing `v`. They pairwise commute, so
  `psi(gamma_v)` is the row-`v` product `J^(b_v)`, which is central.

So `psi` is a homomorphism. Since the `gamma_v` are central in `H(S,C)`,

```text
psi( prod_(v in S) gamma_v ) = J^( sum_(v in S) b_v ) = J^( y^T b ) = J.  ∎
```

**Lemma 3 (abelian gives the identity).** If `H(S,C)` is abelian, then
`prod_(v in S) gamma_v = prod_(c in C) xi_c^|c| = 1`, because every `|c|` is
even.

**Lemma 4 (closure rule).** In `H(S,C)`, fix `v in S` and `e in C` with
`v in e`. Suppose `xi_d` commutes with `xi_c` for every `c in C` containing `v`
other than `e`. Then `xi_d` commutes with `xi_e`.

*Proof.* `xi_e = gamma_v prod_(c ni v, c != e) xi_c`, because the factors of
`gamma_v` are commuting involutions. The element `xi_d` commutes with `gamma_v`
and with each remaining factor. ∎

**Lemma 5 (monotonicity).** Let `C subset C'` be families of nonempty even
subsets of `S`. Sending `xi_c` to `xi_c` for `c in C` and `xi_c` to `1` for
`c in C' \ C` defines a surjective homomorphism `H(S,C') -> H(S,C)`. In
particular, if `H(S,C')` is abelian then so is `H(S,C)`.

*Proof.* Each defining relation of `H(S,C')` maps to a defining relation of
`H(S,C)` or to a trivial one, and `gamma'_v` maps to `gamma_v`. The map is
surjective on generators. ∎

### I.3 Small patterns are abelian

**Proposition 6.** Let `|S| <= 5`, and let `C` be a family of nonempty even
subsets of `S`. Let `G = {c in C : |c| = 2}`, viewed as a simple graph on `S`.
If `|S| <= 4`, or if `|S| = 5` and `G` is not the complete graph `K_S`, then
`H(S,C)` is abelian.

*Proof.* Members of `C` have size 2 or 4.

A member `c` of size 4 meets every member `d`:
- if `|S| = 4`, then `c = S`;
- if `|S| = 5`, then `|c| + |d| >= 6 > |S|`.

So the generators `xi_c` with `|c| = 4` are central by the defining relations.
Central generators are always among the commuting ones in Lemma 4, so they
never block the rule. It remains to show that the edges pairwise commute.

By Lemma 5 it suffices to treat the maximal families:
- all 2-subsets and 4-subsets of `S` when `|S| <= 4`;
- `(K_5 minus one edge)` together with all five 4-subsets when `|S| = 5`.

By symmetry, the missing edge is `45` with `S = {1,2,3,4,5}`. Write `ij` for
the edge `{i,j}` and `xi_ij` for its generator.

- **`|S| <= 3`.** Any two 2-subsets of a set of size at most 3 meet.
- **`|S| = 4`.** The disjoint pairs are `12|34`, `13|24` and `14|23`. The rows,
  up to central generators, are `row 2 = {12,23,24}` and `row 3 = {13,23,34}`.
  - `xi_12` commutes with `xi_13` and `xi_23`, so by row 3 it commutes with
    `xi_34`.
  - `xi_13` commutes with `xi_12` and `xi_23`, so by row 2 it commutes with
    `xi_24`.
  - `xi_14` commutes with `xi_12` and `xi_24`, so by row 2 it commutes with
    `xi_23`.
- **`|S| = 5`, edge `45` absent.** The rows, up to central generators, are

  ```text
  row 1 = {12,13,14,15}   row 2 = {12,23,24,25}   row 3 = {13,23,34,35}
  row 4 = {14,24,34}      row 5 = {15,25,35}
  ```

  There are twelve disjoint pairs. In each step below the listed generators
  commute with the first edge, either because they share a vertex with it or by
  an earlier step, and Lemma 4 gives the conclusion.

  ```text
  (1)  12 ~ 34   row 4: 14, 24 adjacent
  (2)  12 ~ 35   row 5: 15, 25 adjacent
  (3)  13 ~ 24   row 4: 14, 34 adjacent
  (4)  13 ~ 25   row 5: 15, 35 adjacent
  (5)  23 ~ 14   row 4: 24, 34 adjacent
  (6)  23 ~ 15   row 5: 25, 35 adjacent
  (7)  24 ~ 15   row 1: 12, 14 adjacent; 13 by (3)
  (8)  25 ~ 14   row 1: 12, 15 adjacent; 13 by (4)
  (9)  34 ~ 15   row 1: 13, 14 adjacent; 12 by (1)
  (10) 35 ~ 14   row 1: 13, 15 adjacent; 12 by (2)
  (11) 24 ~ 35   row 3: 23, 34 adjacent; 13 by (3)
  (12) 25 ~ 34   row 3: 23, 35 adjacent; 13 by (4)
  ```

  The twelve disjoint pairs of `K_5 minus 45` are

  ```text
  12|34, 12|35, 13|24, 13|25, 14|23, 14|25, 14|35, 15|23, 15|24, 15|34, 24|35, 25|34
  ```

  and steps (1)--(12) cover each of them once.

In every case all generators pairwise commute. ∎

`verify.py`, Part 2, replays the closure rule mechanically on `K_4`,
`K_5 minus 45` and `K_5`. It derives exactly the commutations above:
- 3 steps for `K_4` and 12 for `K_5 minus 45`, with complete closure in both;
- none for `K_5`, where all 15 disjoint pairs stay open.

Part 3 of `verify.py` finds complete closure for 1023 of the 1024 labelled
graphs on five vertices, all except `K_5`. This census is a cross-check, not an
input to the proof.

**Proof of Theorem CERT.** Let `S = supp y` and form `(S,C)` as in I.2.
- If `|S| <= 4`, Proposition 6 applies.
- If `|S| = 5`, the hypothesis says that some 2-subset of `S` is not in `C`, so
  `G != K_S` and Proposition 6 applies.

So `H(S,C)` is abelian. By Lemma 3, `prod_v gamma_v = 1`, and by Lemma 2,
`J = 1` in `Gamma(A,b)`. (If `|S| = 1`, then `C` is empty, and row `v` reads
`1 = J`.) ∎

### I.4 The `K_5` pattern: the Mermin pentagram

Label the rows `0,...,4`; below they are shifted to `1,...,5`. Assign one
3-qubit Pauli operator to each edge of `K_5`, with `Y = [[0,-i],[i,0]]`:

```text
01: XXX   02: XYY   03: YXY   04: YYX
12: XII   13: IXI   14: IIX
23: IIY   24: IYI   34: YII
```

This is Mermin's pentagram. The rows are its five lines and the edges are its
ten points. Every point lies on exactly two lines, as every edge has two ends.

**Lemma 7.** These ten operators are involutions. The four operators at each
vertex pairwise commute. Their products are `-I` at vertex 0 and `+I` at
vertices 1--4, so the total parity is odd.

*Proof.* Each operator is a tensor product of Hermitian involutions. Two Pauli
strings commute iff they anticommute in an even number of positions.

**Commutation.**
- At vertex 0, any two of `XXX, XYY, YXY, YYX` differ, as `X` versus `Y`, in
  exactly two positions.
- At vertices 1--4, the weight-one strings sit on distinct qubits. Each one
  agrees with the vertex's weight-three string at its non-identity qubit:
  - vertex 1: `XXX` with `XII, IXI, IIX`;
  - vertex 2: `XYY` with `XII, IYI, IIY`;
  - vertex 3: `YXY` with `IXI, IIY, YII`;
  - vertex 4: `YYX` with `IIX, IYI, YII`.

**Products,** computed qubit by qubit.
- Vertex 0: `(XXYY) (x) (XYXY) (x) (XYYX) = I (x) (XY)^2 (x) I = I (x) (iZ)^2 (x) I = -I`.
- Vertices 1--4: each qubit sees the same letter twice, or never, so the
  product is `+I`.

∎

`verify.py`, Part 1, checks all of this exactly in Gaussian-integer arithmetic
on `8 x 8` matrices.

**Lemma 8 (sign adjustment).** For every `b in F_2^5` with odd parity, some
sign changes `X_e -> -X_e` give an operator solution of the `K_5` incidence
system with right-hand side `b`.

*Proof.* Changing the sign of `X_e` keeps the involution and commutation
relations. It changes the sign of the products at both ends of `e`, and at no
other vertex. Let `b0 = (1,0,0,0,0)` be the base right-hand side and
`d = b + b0`, which has even parity. Negate `X_(0v)` for each `v in {1,...,4}`
with `d_v = 1`. This toggles vertex `v` exactly when `d_v = 1`. It toggles
vertex 0 `|{v >= 1 : d_v = 1}| = d_0 mod 2` times. ∎

`verify.py` builds the flip set for all 16 odd `b` and re-verifies each
solution exactly.

### I.5 Proof of Theorem LCS5

**3 => 2.**
- *Classical solution.* If `z in F_2^n` solves `Ax = b`, put
  `rho(x_j) = (-1)^(z_j)` and `rho(J) = -1`. This has dimension 1.
- *`K_5` pattern.* Otherwise, for every 2-subset `uv` of `[5]`, choose one
  column `j(uv)` with `supp A_(j(uv)) = uv`. By Lemma 8, choose sign-adjusted
  pentagram operators `X_uv` for the right-hand side `b`, which has odd
  parity. Put `rho(x_(j(uv))) = X_uv` and `rho(x_j) = I` for every other
  column: those of weight 0 or 4, and duplicate weight-2 columns. Put
  `rho(J) = -I`.

  Now check the relations:
  - all images are involutions;
  - in row `v`, the non-scalar images are the four `X_uv` with `u != v`, and
    these commute by Lemma 7;
  - the row product is `prod_(u != v) X_uv = (-1)^(b_v) I`.

  So `rho` is an operator solution of dimension 8.

**2 => 1.** `rho(J) = -I != I`.

**1 => 3.** Suppose `J != 1` and `Ax = b` has no classical solution. Take a
parity certificate `y` with support `S`. By Theorem CERT, `|S| = 5`, and every
2-subset of `S` is some `supp A_j cap S`. Since `m <= 5`, we get `m = 5` and
`y = (1,1,1,1,1)`. Then `y^T A = 0` says that every column has even weight, and
`y^T b = 1` says that `b` has odd parity. As `S = [5]`, every 2-subset of `[5]`
is the support of a column. ∎

### I.6 Consequences, scope, and where the method stops

**Proof of the Corollary.** A homomorphism `Gamma(A,b) -> U(8)` with
`J |-> -I` composes with a unital trace-preserving embedding `M_8 -> R^U`. It
then becomes an exact representation into `U(R^U)` in which `J` is nontrivial,
so the system is `R^U`-satisfiable.
- *At least six equations.* A tracially satisfiable system has `J != 1`. If
  `m <= 5`, Theorem LCS5 supplies such a `U(8)` representation, so the system
  is not a gap system. Hence `m >= 6`.
- *No classical solution.* A classical solution is a 1-dimensional
  representation with `J |-> -1`, so a gap system has none, and parity
  certificates exist.
- *Certificate weights.* A certificate of weight at most 4, or of weight 5
  missing a pair, would force `J = 1` by Theorem CERT, which contradicts tracial
  satisfiability. ∎

**Interpretation for games.**
- By Cleve--Liu--Slofstra (arXiv:1606.02278, abstract checked 2026-09-16),
  perfect commuting-operator strategies for the linear system game correspond
  to operator solutions in possibly infinite dimension.
- By `solution-group-central-order-is-operator-solvability`, these exist iff
  `J != 1`.
- The Cleve--Mittal correspondence (finite-dimensional perfect strategies iff
  finite-dimensional operator solutions) is cited, not fetched.

So for at most five equations, a perfect commuting-operator strategy implies a
perfect finite-dimensional one.

**Relation to Arkhipov / PRSS.** Paddock--Russo--Silverthorne--Slofstra
(arXiv:2205.04645) treat graph incidence systems, in which every variable
occurs in exactly two equations, with any number of equations. Theorem LCS5
instead bounds the number of equations and allows every column weight. The
closed-component half of `lcs-occurrence-two-qc-equals-q` does not contain
Theorem LCS5, which permits columns of weight 3 to 5, nor the reverse.

**What changes at six equations.**
1. **The magic square.** The Mermin--Peres magic square is the `K_(3,3)`
   incidence system: 6 equations, 9 variables, a 4-dimensional operator
   solution, and no classical solution. So the list of patterns in item 3 of
   LCS5 grows at `m = 6`.
2. **New column types.** For `|S| = 6`, a column of size 4, `S \ {u,v}`, fails
   to meet only the column `{u,v}`. It is no longer automatically central, and
   PRSS says nothing about it. Columns of size 6 are central.
3. **The closure rule is weaker than Arkhipov's theorem on six vertices.**
   `census6.py` runs the rule of Lemma 4 on the incidence group `H(G)` of all
   `2^15` labelled graphs on six vertices, and decides planarity by Kuratowski
   subgraph tests.

   | Closure | Planar | Nonplanar |
   |---|---|---|
   | complete | 28416 | 0 |
   | incomplete | 3655 | 697 |

   For example, the octahedron `K_(2,2,2)` is planar, but the rule derives
   nothing on it. PRSS Theorem 1.1 together with
   `lcs-occurrence-two-qc-equals-q` still gives `J = 1` for every odd
   right-hand side on it. So Proposition 6's method
   does not extend on its own. A six-equation theorem needs PRSS-type arguments
   together with a treatment of the size-4 columns.

## Part II. Minimal nonhyperlinear groups

### II.0 Definition and source

A group `G` is **minimal nonhyperlinear** (MNH) if `G` is not hyperlinear and
every proper subgroup of `G` is hyperlinear.

This is the hyperlinear form of Ersoy's Definition 1.3, in *On minimal
non-sofic and ω-non-sofic groups* (arXiv:2604.19174, v1 2026-04-21,
v4 2026-06-08; HTML v4 read 2026-09-16). There a group is *minimal non-sofic*
if it is not sofic but every proper subgroup is sofic. Ersoy's Remark 2.8 says
verbatim: "One may also discuss minimal non-hyperlinear groups, but we will not
do that in the present paper."

Ersoy's abstract states the sofic theorem: if `M` is a finitely generated,
residually finite, maximal normal subgroup of a minimal non-sofic group `G`,
then `M` is central and `G` is a perfect central extension of a finitely
generated non-amenable simple group. The proof of that theorem was not read.
Everything below is proved from this repository's permanence nodes, except the
remarks in II.3, which say which classical theorems they import.

Existence of an MNH group is open, even assuming a nonhyperlinear group exists;
see (M6).

### II.1 Statement

**Theorem MNH.** Let `G` be minimal nonhyperlinear.

- **(M1)** `G` is finitely generated, infinite and nonamenable.
- **(M2)** If `N` is normal in `G` and `G/N` is amenable, then `N = G`. So `G`
  is perfect, has no proper subgroup of finite index, and has no nontrivial
  amenable quotient.
- **(M3)** Every homomorphism from `G` to a residually finite group is trivial.
- **(M4)** Let `G = pi_1(Gcal)` for a finite connected graph of groups `Gcal`
  with amenable edge groups. Then some vertex group `G_v` is nonhyperlinear,
  and its canonical image in `G` is all of `G`.
- **(M5)** `G` has a maximal normal subgroup. For every maximal normal subgroup
  `M`, the group `M` is hyperlinear and `G/M` is a finitely generated, infinite,
  nonamenable simple group.
- **(M6)** *(existence dichotomy)* Let `K` be any nonhyperlinear group. Either
  `K` contains an MNH subgroup, or `K` contains a strictly descending chain
  `G_0 > G_1 > G_2 > ...` of finitely generated nonhyperlinear subgroups.

In (M4), the second half uses the injectivity of the canonical maps
`G_v -> pi_1(Gcal)`. This is standard Bass--Serre theory (Serre, *Trees*,
Ch. I §5; cited, not fetched), and AEG1 presupposes the same theory.

### II.2 Proofs

The imports are all ESTABLISHED nodes.
- **(L)** `local-approximation-properties-are-marked-closed`, clauses 1--2:
  hyperlinearity is hereditary and local.
- **(Q)** `amenable-quotient-preserves-metric-approximability`: if `N` is
  normal in `G`, `N` is hyperlinear and `G/N` is amenable, then `G` is
  hyperlinear. With `N = 1`, amenable groups are hyperlinear.
- **(AEG1)** `amenable-edge-graph-corners-cannot-groupify-a-nonce-game`: the
  fundamental group of a finite connected graph of countable groups with
  hyperlinear vertex groups and amenable edge groups is hyperlinear.

**(M1).** By (L), the nonhyperlinear group `G` has a finitely generated
nonhyperlinear subgroup `K`. By minimality `K` is not proper, so `K = G`. By (Q)
with `N = 1`, `G` is not amenable. Finite groups are amenable, so `G` is
infinite.

**(M2).** If `N != G`, then `N` is a proper subgroup, so it is hyperlinear, and
(Q) makes `G` hyperlinear, a contradiction.
- *Perfect.* Apply this to `N = [G,G]`, whose quotient is abelian and hence
  amenable.
- *No proper finite-index subgroup.* If `L < G` is proper of finite index, its
  normal core is a finite intersection of conjugates. It is normal, of finite
  index and contained in `L`, hence proper, and the quotient is finite, hence
  amenable. This contradicts the first part.
- *No nontrivial amenable quotient.* This is the first part restated.

**(M3).** Let `phi : G -> R` be nontrivial, with `R` residually finite. Pick `g`
with `phi(g) != 1`, and a finite quotient `pi : R -> Q` with `pi(phi(g)) != 1`.
Then `ker(pi o phi)` is a proper normal subgroup of finite index, which
contradicts (M2).

**(M4).** `G` is countable by (M1). The canonical maps are injective, so every
vertex and edge group is isomorphic to a subgroup of `G` and hence countable.
- *Some vertex group is nonhyperlinear.* If all vertex groups were hyperlinear,
  (AEG1) would make `G = pi_1(Gcal)` hyperlinear.
- *Its image is all of `G`.* The image of that `G_v` is isomorphic to `G_v`,
  so it is a nonhyperlinear subgroup of `G`. By minimality it is not proper.

∎

**(M5).** `G != 1`, and by (M1) `G` is generated by a finite set `X`.
- *Existence.* Proper normal subgroups exist, for instance `1`. The union of a
  chain of proper normal subgroups is normal, and it is proper: otherwise the
  finite set `X` would lie in a single member. Zorn's lemma gives a maximal
  proper normal subgroup `M`.
- *Properties of `G/M`.* It is simple by the correspondence theorem, and
  finitely generated. It is nonamenable by (M2), since `M` is proper, and hence
  infinite.
- *`M` is hyperlinear,* as a proper subgroup.

**(M6).** Suppose `K` contains no MNH subgroup. By (L), choose a finitely
generated nonhyperlinear subgroup `G_0` of `K`. Given `G_i`: it is not MNH, so
it has a proper nonhyperlinear subgroup `P`, and by (L) `P` has a finitely
generated nonhyperlinear subgroup `G_(i+1)`, with `G_(i+1) <= P < G_i`.
Dependent choice gives the chain. ∎

The intersection of such a chain may be hyperlinear, for instance trivial.
Zorn's lemma therefore does not apply downward, and (M6) does not decide
existence. I know of no compactness argument that produces an MNH subgroup.

### II.3 Remarks resting on classical theorems

None of these is part of the node's established content: each imports a
classical theorem that was not re-fetched this session.

- **(R1) Malcev.** Finitely generated linear groups are residually finite. With
  (M1) and (M3), every finite-dimensional linear representation of an MNH group
  is trivial. So no MNH group is linear, and no MNH group has a nontrivial
  finite-dimensional unitary representation.
- **(R2) Baumslag.** The automorphism group of a finitely generated residually
  finite group is residually finite.
  - *Central normal subgroups.* Suppose `N` is a normal subgroup of an MNH
    group `G`, and `N` is finitely generated and residually finite. Then the
    conjugation map `G -> Aut(N)` lands in a residually finite group, so it is
    trivial by (M3), and `N` is central.
  - *Hyperlinear analogue of Ersoy's theorem.* Combine this with (M2) and (M5).
    If some maximal normal subgroup `M` is finitely generated and residually
    finite, then `G` is a perfect central extension of the finitely generated,
    infinite, nonamenable simple group `G/M`.
- **(R3) Stallings and Bass--Serre.** A finitely generated group with more than
  one end splits over a finite subgroup. With (M4), an MNH group is one-ended.
  - *Normal forms.* In a nontrivial free product, or in `A *_C B` with
    `A != C != B`, the factors are proper subgroups. The base of an HNN
    extension is proper. So (M4) excludes all these splittings over amenable
    groups.
  - *Tree actions.* A finitely generated group acting on a tree without inversions
    has an invariant subtree with finite quotient graph. So every such action of
    an MNH group with amenable edge stabilizers has a global fixed point.
- **(R4) Consequence for candidates.** A known nonhyperlinearity candidate that
  is residually finite, linear, virtually splits over an amenable subgroup, or
  has a nontrivial amenable quotient is not itself MNH. This is compatible with
  it being nonhyperlinear: a nonhyperlinear witness only needs to *contain* a
  nonhyperlinear finitely generated subgroup, and by (M6) that subgroup either
  contains an MNH group or starts an infinite descending chain.

### II.4 Where this stops

Theorem MNH holds for any hypothetical MNH group. It does not produce one.
- No argument is known that derives the existence of MNH groups from the
  existence of nonhyperlinear groups; see the (M6) discussion.
- (M5) matches `nonhyperlinear-existence-is-two-generator-simple`, which works
  on the quotient and embedding side. An MNH group maps onto an infinite simple
  group whose kernel is hyperlinear. The simple quotient need not be
  nonhyperlinear, since there is no permanence for hyperlinear kernel and
  nonamenable quotient.

## Reproduction

```text
cd experiments/lcs-five-equations-2026-09-16
timeout 600 python3 verify.py   > verify.out    # ALL CHECKS PASSED, < 1 s
timeout 600 python3 census6.py  > census6.out   # 2x2 table of I.6, about 30 s
```

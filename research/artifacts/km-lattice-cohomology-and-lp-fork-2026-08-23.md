# Kac--Moody lattices: second cohomology, end cohomology, and the LP fork (2026-08-23)

Session note accompanying the nodes `triangle-colimit-rational-h2-vanishes`,
`km-group-ring-h2-is-development-end-cohomology`,
`km-development-has-nonzero-end-cohomology-in-degree-one` and the route
`km-lp-fails-via-development-end-cohomology`.  Nothing here is a literature
import beyond the cited statements; every argument is written out in the nodes.

## What was decided

1. `H^2(Lambda;Q) = 0` for every colimit `Lambda` of a developable triangle of
   finite groups, in particular for the simple Kazhdan Kac--Moody lattices
   `Lambda_(2,4,6)(q)`.  Tool: the Cartan--Leray spectral sequence of the
   development `X` (simply connected by Bridson--Haefliger III.C.3.13), which
   needs only `H^1(X)=0`, not contractibility; the first spectral sequence
   with finite stabilizers and rational coefficients collapses to the cochains
   of the quotient triangle.  This corrects the tilt recorded in
   `compact-hyperbolic-km-lattices-fail-lp` and kills the trivial-coefficient
   clause of Ioana--Spaas--Wiersma Corollary E at every triangle colimit.

2. `H^2(Lambda; Z Lambda) = H^1_infty(X;Z) = ker(H^2_c(X) -> H^2(X))`: the
   group-ring cohomology is the degree-one end cohomology of the development.
   Corollary D therefore fires iff this end cohomology is nonzero, which is
   the new open input.

## Structure of the development (opposition complex of the twin building)

- Every 2-cell lies in exactly one twin-apartment plane; `X` is a union of
  hyperbolic `(2,4,6)` planes glued along wall segments; each edge lies in
  `q(q+1)` planes; no 2-cycle is supported in a vertex star.
- `H_2(X) != 0` UNCONDITIONALLY: for a vertex `v` of `X_+`, an `s`-panel
  `e'` of `X_-` and two generic chambers `y_i, y_j` of that panel, the
  chambers through `v` opposite to `y_i` and to `y_j` coincide (the
  opposition subgraph of the link polygon with respect to the common
  co-projection), and for any cycle `z` in it the 2-chain
  `sum eps_x [(x,y_i) - (x,y_j)]` is an embedded 2-sphere of `X` (two
  fans glued along the far-edge circle `(e_s(x), e')`).  So the development
  is never contractible, the point class of a 2-cell is never in
  `H^1_infty(X)`, and Corollary D needs a compactly supported 2-cochain
  orthogonal to all these spheres.  (An earlier draft of this note used a
  point-class argument; it is withdrawn.)

## The filtration of the twin-building product

Filter the contractible product `Z = X_+ x X_-` by minimal codistance
length.  The bottom level `X^ = Z_(<=0)` is the union of the closed product
cells over opposite chamber pairs: four-dimensional, simply connected, and
homotopy equivalent to `X` only after deleting its mixed-type 1-skeleton.
Descending faces of a chamber pair at codistance `w` are those whose
cotypes meet the descent sets `L(w)`, `R(w)`; the relative complex at each
level is a wedge over residue pairs of `(cl O_w, D)`.  With
`K = J cap wJ'w^(-1)`:

- `K = emptyset`: product of two opposition sets; relative homology only
  in degree four (opposition graphs of thick polygons connected for `q`
  large).
- `K != emptyset`: all labels of `(2,4,6)` are even, so `K = {r}` with
  `w` centralizing `r`; such levels are impossible for rank-one residues
  (wall geometry: a chamber with an edge on `M_r` cannot lie in the sector
  opposite to `c_0` at the vertex of the other two walls), so every twisted
  level is a rank-`(2,2)` pair.  There `O_w = union_(i != j) A_i x B_j`
  (classes = projections to the matched `r`-panels), the relative complex
  is the suspension of the join `A * B` minus the matched single-class
  vertex edges, and `H_3(rel) = coker(H_1(A) (x) H_1(B) -> (+) Z_1(K_(q,q)))`.
  This vanishes for the grid type (proved) and reduces to connectivity of
  explicit class graphs for `B_2`, `G_2` (`km-twisted-level-product-cycles-surject`).

Hence, if the cokernels vanish, `X^` is 2-connected, `Lambda` is of type
`F_3`, and `H^2(Lambda;Z Lambda) = H^2_c(X^) = H^3_c(Z minus X^)`.  A
downward induction over cusp levels (each has cohomology only in degree
four) then gives `H^3_c(Z minus X^) = 0`: the SAME finite input that
yields `F_3` also computes `H^2(Lambda;Z Lambda) = 0`, so ISW Corollary D
would be DEAD at these lattices, alongside the trivial-coefficient clause
of Corollary E.  The status of the surjectivity input, for `q`
COPRIME TO SIX: proved for grid levels and `B_2` line-panels (symplectic
model: the two-class graph is `q` disjoint `K_(q,q)`'s, three classes
reach everything by a perp-pencil argument); `B_2` point-panels, `G_2`
point-panels (stabilizer `X_alpha` plus the visible `x_(alpha+beta)`
translation span the Frattini plane) and `G_2` line-panels (distance
sphere `c^2 = lambda bd` computed in the seven-dimensional
representation) are reduced to short genericity counts.
Characteristics two and three are genuinely open (structure-constant
degenerations), so the chain is scoped to lattices with `q` coprime to
six -- a legitimate restriction of the candidate class.  For affine `A~_2` the odd labels allow
rank-`(1,2)` twisted levels with nonzero relative `H_3`, consistent with
finiteness length three and with the possibility of nonzero group-ring
`H^2` there.

## Net status of the LP fork

`H^2(Lambda;R)=0` is established; `H^2(Lambda;Z Lambda)=0` follows from the
remaining finite surjectivity cell; the `L^0(Y,R)` clause of Corollary E is
then the only Ioana--Spaas--Wiersma mechanism left for LP failure at the
Kac--Moody lattices, while LP holding would still close the whole program
(`compact-hyperbolic-km-lattices-fail-lp`, stakes paragraph).  The lattice
being of type `F_3` (conditional on the same cell) appears to be a new
finiteness property for compact hyperbolic Kac--Moody groups.

## Why this matters for the program

The LP fork is a side question (its refutation branch, LP holding, would close
the goal outright; its positive branch separates LLP from LP at the
Kac--Moody candidates).  The structural facts about the development are also
the cleanest finite-dimensional description of what a hyperlinear microstate
of `Lambda` must glue: three regular charts of the finite Levi groups along
the three edge groups, i.e. the regular microstate problem is the question
whether the two copies of `P_3` inside the virtually free tree amalgam
`P_13 *_(P_1) P_12 *_(P_2) P_23` can be made asymptotically equal in
normalized Hilbert--Schmidt norm while every word nontrivial in `Lambda`
keeps vanishing trace.

## Final state (end of 2026-08-23 session)

The finite surjectivity was REFUTED at every `G_2` twisted level: the
one-class-deleted opposition geometry of the split Cayley hexagon is
disconnected (computed at `q = 2` and `q = 3`; scripts in experiments/),
and component-indicator annihilators give nonzero integral cokernel.
Grid and `B_2` levels survive (their one-deleted graphs are connected;
symplectic theorems verified at `q = 3`).  Consequently the conditional
conclusions (type `F_3`; `H^2(Lambda;Z Lambda) = 0`; death of Corollary
D) are all withdrawn: every hexagon level of the codistance filtration
carries explicit nonzero relative `H_3` classes, in every
characteristic, and the group-ring `H^2` -- hence ISW Corollary D and
the LP fork -- is decided by whether some such class has nonzero
connecting map.  What remains established unconditionally from today:
`H^2(Lambda;Q) = 0`; the end-cohomology identification of
`H^2(Lambda;Z Lambda)`; the 2-spheres in the development; the
structure theorem for the filtration with its per-level homology
formulas; the exact solution of the `B_2` class-graph geometry; and the
triple-validated computational models.

## Truly final state (after the H(4) computation)

The day ended with one more reversal, resolving all earlier ones.  The
class-stabilizer subgroups trace a rational normal curve in the
Frattini quotient of the parabolic radical, so the class-walk graphs on
`k` classes have `q^(max(0,dim-k))` components in every characteristic
(verified exactly at `q = 2, 3, 4`; the characteristic-two collapse
claim came from an adjoint-vs-module structure-constant bug and is
retracted).  Hence: the hexagon-level refutations of the twisted
surjectivity live only at `q <= 3`; for the actual lattices
(`q > 1764^3`) the disjoint-class construction applies at every level
(`q >= 8` suffices, four intermediate classes per side at hexagon
levels), and the chain

    twisted surjectivity  =>  thick part 2-connected  =>
    Lambda is type F_3  and  H^2(Lambda; Z Lambda) = 0  =>
    ISW Corollary D dead (any characteristic)

is restored as the expected outcome, pending one careful write-up of
the single-slot construction.  The LP fork's only surviving known
failure mechanism is the L^0 clause of Corollary E, now equipped with
the explicit sphere-pairing obstruction identities; LP holding would
still close the whole program.  Established unconditionally today:
`H^2(Lambda;Q) = 0`; the end-cohomology identification; the 2-spheres
in the development (never contractible); the filtration structure
theorem with per-level formulas (validated numerically in both
connected and disconnected regimes); the exact `B_2` class-graph
geometry; the curve-span threshold law; and the small-`q` cokernel
theorems.

## Addendum 8: explicit stabilizer data for the 49-orbit invariants complex

From the (KM2) generalized Cartan matrix `[[2,0,-1],[0,2,-1],[-2,-3,2]]`
(`a_13 a_31 = 2`, `a_23 a_32 = 3`, `a_12 = a_21 = 0`), the rank-two
subsystems and their positive roots:

| J | type | Phi_J^+ | N_J |
|---|------|---------|-----|
| {} | -- | (empty) | 0 |
| {i} | A_1 | a_i | 1 |
| {1,2} | A_1 x A_1 | a_1, a_2 | 2 |
| {1,3} | B_2 (a_1 long, a_3 short) | a_1, a_3, a_1+a_3, a_1+2a_3 | 4 |
| {2,3} | G_2 (a_2 long, a_3 short) | a_3, a_2, a_2+a_3, a_2+2a_3, a_2+3a_3, 2a_2+3a_3 | 6 |

Orbit `(J,K)` (proper subsets, dimension `4-|J|-|K|`) has stabilizer
`P_J^+ cap P_K^- = T . <U_alpha : alpha in Phi_J^- cup Phi_K^+>`, with
EXACT root content `Phi_J^- cup Phi_K^+` (a root group lies in the
intersection iff its root is in `(Phi^+ cup Phi_J^-) cap (Phi^- cup
Phi_K^+)`).  CORRECTION (self-caught, same day): the two root sets
meet in `-Phi_(J cap K)^+ cup Phi_(J cap K)^+` when `J cap K != {}`,
so opposite pairs generate the finite Levi `L_(J cap K)(q)` and the
order is `|L_(J cap K)(q)| . q^(N_J + N_K - 2 N_(J cap K))`, NOT
`|T| . q^(N_J+N_K)` in general (that holds iff `J cap K = {}`).
Largest stabilizers sit on the diagonal: `(J,J)` vertex pairs carry
the full rank-two finite Levi groups, e.g. `G_2(q)`-type at
`J = {2,3}`, `Sp_4(q)`-type at `J = {1,3}` (`|T| = (q-1)^3`, simply
connected form).

Invariant-module sizes for the `H^2` window (`C^1 -> C^2 -> C^3`):
18 one-cell orbits (`|J|+|K|=3`), 15 two-cell orbits (`=2`), 6
three-cell orbits (`=1`).  For `V = L^0(Y)`: `V^F = L^0(Y/F)`.

Sanity checks recorded: `H^0` of the complex is `V^Lambda` because the
nine maximal Birkhoff intersections include the diagonal rank-two Levi
pairs `(J,J)`, which generate `Lambda` (they contain every `U_(+-a_i)`).

## Addendum 9: the double complex and the opposition-complex columns

The `Delta^2 x Delta^2` identification makes the 49-orbit complex the
TOTAL COMPLEX of a 3x3 double complex `C^(a,b) = sum over |J| = 2-a,
|K| = 2-b of V^(P_J^+ cap P_K^-)` (horizontal = grow `J`, vertical =
grow `K`).  Columns-first analysis of the fixed-`K` column:

1. `P_K^-` is transitive on each cotype-`J` stratum of the
   opposite-compatible set `O(sigma_K) = {sigma_+ : (sigma_+,
   sigma_K) in X^}` (stabilizer transitivity on the `w = 1` Birkhoff
   fiber), with finite cell stabilizers; so for divisible `V` the
   column computes the equivariant cohomology
   `H^*_(P_K^-)(O(sigma_K); V)`.

2. For `K = {}` (a chamber `y`), `O = Opp(y)` is Abramenko's
   opposition complex: under the thickness hypotheses of his
   sphericity theorem (Twin buildings and applications, LNM 1641;
   rank 3, so 1-connected with free `H_2`), the coefficient rows are
   `q = 0` (`V`) and `q = 2` (`Hom(H_2 Opp, V)`) only.

3. `B_- = T x| U_-` with `U_-` the INCREASING UNION of the finite
   `U_w` (locally finite).  Milnor sequence for an increasing union,
   with `H^q(finite, divisible) = 0` for `q > 0`:
   `H^1(U_-, V) = lim^1_w V^(U_w)` and `H^2(U_-, V) = lim^1_w
   H^1(U_w, V) = 0`; finite `T` then gives `H^2(B_-, V) = 0`,
   `H^1(B_-, V) = (lim^1_w V^(U_w))^T`.

So the chamber column's cohomology is: `V^(B_-)` in degree 0, the
`T`-invariant `lim^1` of the unipotent invariants tower in degree 1,
and a `B_-`-equivariant functional space on `H_2` of the opposition
complex in degree 2 (up to the `d_3` edge).  The clause is therefore
governed by exactly two kinds of quantities: derived-limit terms of
invariant towers along the unipotent filtration, and equivariant
functionals on opposition-complex `H_2` -- the same `H_2` whose
sphere classes are the day's explicit `S_z` cycles.  The `|K| = 1, 2`
columns are the face (panel / vertex) opposition analogues.

## Addendum 10: the (1,1) entry survives, and a lim^1 nonvanishing model

Index the double complex spectral sequence by (a,b) = (K-degree,
J-line degree), a,b in {0,1,2} (the base is a triangle, so a <= 2).

1. **Degeneration at the (1,1) spot.**  d_2 : E_2^(1,1) -> E_2^(3,0)
   = 0 (out of range) and E_2^(1,1) receives only from E_2^(-1,2) =
   0.  So E_infty^(1,1) = E_2^(1,1) = H^1 over the K-triangle of the
   coefficient system K |-> H^1(P_K^-, V), EXACTLY.  A nonzero value
   here forces H^2(Lambda, V) != 0 -- no differential caveats.

2. **The entries are lim^1 towers.**  H^1(P_K^-, V): P_K^- = L_K x|
   U-part with the unipotent directions locally finite; by the Milnor
   sequence (Addendum 9) these are derived limits of averaging-tower
   invariants (lim^1_w V^(U_w))-type groups, `L_K`-twisted for K != {}.

3. **Bottom row dies for Bernoulli.**  The (2,0) and (a,0) entries use
   H^0(J-line at K) = V^(P_K^-) (the line's stabilizers generate
   P_K^-).  The restriction of a Bernoulli shift to ANY infinite
   subgroup is a Bernoulli shift with enlarged base, hence mixing and
   ergodic, so V^(P_K^-) = R for all seven K and the bottom row is
   the constant complex: H^* (Delta^2; R) = R in degree 0 only.

4. **Model theorem (rigorous): the tail tower has lim^1 != 0.**  In
   L^0(prod_(k>=0)[0,1]) let T_n = L^0 of the coordinates >= n.  Take
   b_k = independent fair signs eps_k(x_k) in T_k.  A telescoping
   solution a_n - a_(n+1) = b_n with a_n in T_n gives, for every n,
   a_0 = (eps_0 + ... + eps_(n-1)) + a_n with a_n independent of the
   first n coordinates; hence |phi_(a_0)(t)| <= |cos t|^n -> 0 for
   t not in pi Z, so phi_(a_0) vanishes a.e. -- impossible for the
   characteristic function of an a.e.-finite random variable
   (continuity, phi(0) = 1).  So no solution exists and
   lim^1 {T_n} != 0.

5. **The honest gap.**  In the true tower A_w = L^0(Y)^(U_w),
   solutions need only be INVARIANT, not tail-measurable: the
   independence step fails, and richer a_n are available (e.g.
   partial averages of earlier b's).  The sharp open subquestion is
   therefore: is H^1(B_-, L^0(Y)) != 0 for the Bernoulli action
   restricted to B_-?  (Equivalently: does the averaging tower of the
   locally finite unipotent group have nonvanishing algebraic lim^1
   against its Bernoulli L^0?)  A positive answer, if it also
   survives the K-direction H^1 across the triangle, fails LP for
   C*(Lambda) and resolves the forced-witness fork to its
   LLP-failure branch.

## Addendum 11: the stable-element endgame for E_2^(1,1)

All negative standard parabolics contain `B_-` with FINITE index
(the chamber count of the K-residue), so on divisible coefficients
every restriction in the K-direction complex is INJECTIVE (transfer:
cores o res = index), and by Cartan--Eilenberg the image of
`H^1(P_K^-, V) -> H := H^1(B_-, V)` is the subspace `St_K` of
`P_K^-`-stable classes, with `St_K c St_K'` for `K' c K`.  The
established theorem `locally-finite-bernoulli-first-l0-cohomology-
nonzero` makes every one of these groups nonzero.

**The obstruction map.**  Fix the edge pair `{2},{3}` with vertex
`P_23^- = <P_2^-, P_3^->`.  For `alpha in St_2 cap St_3` the two
extensions are UNIQUE as classes (injectivity), glue on the amalgam
`P_2^- *_(B_-) P_3^-`, and the kernel `N` of the amalgam onto
`P_23^-` is free (Bass--Serre) and acts TRIVIALLY on `V` (the action
factors through `P_23^- <= Lambda`).  Hence `V^N = V`, the five-term
sequence collapses, and

```text
alpha in St_23  <=>  obs(alpha) = 0,
obs : St_2 cap St_3 -> Hom(N, V)^(P_23^-)
```

is a WELL-DEFINED linear map (coboundary ambiguities die on N since
N acts trivially).  `obs(alpha)` is explicitly computable: my
cocycles have `c(g) = (1-g) S_(n(g))` (finite block sums), so
`obs(alpha)(n)` for a word `n = g_1 h_1 ...` is a finite signed sum
of prefix-translated block functions.  Note the philosophical rhyme:
`N` is exactly the same kind of free relator kernel as in the
triangle-LLP reduction (TC2) -- the L^0-cohomology obstruction and
the ucp-section obstruction live on the same relator data.

**Joint data beyond the jointly-averaged.**  A class in
`St_2 cap St_3` arises from any tower data `e_k` invariant under
`M_k = <H_k^(2), H_k^(3)>` with BOTH next-level averages zero
(`P^(2) e_k = P^(3) e_k = 0`); both restrictions are then literally
the same `B_-`-cocycle.  On a fresh free `M_(k+1)`-block with
sub-blocks `B_k = M_k \\ M_(k+1)` carrying iid fair signs `F_b`, the
data `e = sum_b lambda_b F_b` qualifies iff `lambda` has mean zero
on every `H^(2)_(k+1)`-orbit AND every `H^(3)_(k+1)`-orbit of `B_k`
-- an annihilator-existence question of exactly the
`km-opposition-class-walk-threshold-law` type: such `lambda != 0`
exist iff the two orbit partitions' indicator span is a proper
subspace, a walk-graph/threshold computation in the finite groups.
The candidate certificate for `E_2^(1,1) != 0` (hence
`H^2(Lambda, L^0(Y)) != 0`, hence NO LP by Ioana--Spaas--Wiersma
Corollary E) is: such a `lambda`-class with `obs != 0`.

**Precise stakes.**  Corollary E kills the LP (= global ucp
splitting of the relator extension).  Whether LLP (= local
splitting) also dies requires an `LLP => LP` bridge for property (T)
groups that is NOT in the recorded source audit -- VERIFY against
arXiv:2006.01874 before claiming the LLP side.  Independently of
that bridge, `obs != 0` would already close the GLOBAL half of
(TC4) and, per `kac-moody-lattice-is-non-hyperlinear-or-llp-failure`,
sharpen the forced-witness alternative.

**Caveats still open.**  (i) The J-line identification
`H^1(J-line at K) = H^1(P_K^-, V)` needs connectivity and simple
connectivity of the FACE opposition complexes `O(sigma_K)` (chamber
case: Abramenko; face cases: to be verified).  (ii) The
`E_2^(1,1)`-quotient involves all three vertices; `(St_2 cap
St_3)/St_23` maps into it, and nonvanishing of the full quotient
needs the other vertices' relations tracked.  (iii) The
`lambda`-annihilator existence at every level along cofinal chains
needs the actual orbit counts (threshold-law computation on
`M_k \\ M_(k+1)`).

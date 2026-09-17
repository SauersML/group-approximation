# Brick codings of 2-graphs, and why Robertson–Steger 2-graphs have none

Lane swarm-0917-w4-nv-rel-t, 2026-09-17. Code: `experiments/nv-brick-coding-2026-09-17/`.

Part A proves that a brick coding of a finite 2-graph embeds its cylinder-exchange group in
`mV`. Part B proves that the cohomology of the square complex forces every brick coding
into a rigid shape. Part C applies this to five explicit triangle presentations over
`PG(2,2)`: the shape is forced into dimension 2, and an exhaustive SAT search there is
UNSAT. So the natural route "Ã₂ group -> its Robertson–Steger full group -> mV by coding
edges as bricks" dies for these groups. Part D lists what survives.

## Part 0. Setting

**2-graphs.** A finite 2-graph `Λ` is given by:

- a finite vertex set `V`;
- finite edge sets `E_1` (colour 1) and `E_2` (colour 2), each edge `e` with a start `o(e)`
  and an end `t(e)` in `V`;
- a **square bijection** between the composable pairs `(e,f)` in `E_1 × E_2` with
  `t(e) = o(f)` and the composable pairs `(f',e')` in `E_2 × E_1` with `t(f') = o(e')`,
  preserving the start `o(e) = o(f')` and the end `t(f) = t(e')`. We write `ef = f'e'`.

For `k = 2` no associativity condition is needed.

- **Rectangles.** A rectangle of degree `(p,q)` is a labelling of the grid `[0,p]×[0,q]`:
  vertices at lattice points, colour-1 edges on horizontal unit segments oriented
  rightwards, and colour-2 edges on vertical unit segments oriented upwards. Every unit
  cell must be a square `ef = f'e'`, with `e` at the bottom, `f` on the right, `f'` on the
  left and `e'` at the top.
- **Infinite paths.** An infinite path is the same kind of labelling of the quadrant
  `N^2`. `Λ^∞(a)` is the set of infinite paths with vertex `a` at the origin, and
  `X_Λ = ⊔_a Λ^∞(a)`.
- **Topology.** The topology is pointwise convergence on finite regions.
- **Unique filling.** A monotone staircase path determines the labelling of the region
  it bounds. Take a cell whose left and top edges are known: the pair `(f',e')` is known,
  so the inverse square bijection gives `(e,f)`.
- **Consequences.** Monotone lattice paths between two points are connected by
  elementary square flips. For a rectangle `λ` of degree `(p,q)` and
  `z ∈ Λ^∞(t(λ))` there is a unique infinite path `λz` whose `[0,p]×[0,q]` part is `λ`
  and whose translate by `(p,q)` is `z`. The two strips are filled uniquely, starting
  from the corner cell `[p,p+1]×[q-1,q]`, whose left and top edges are known.
- **Cylinders.** `Z(λ) = {λz}`.

`M_i(a,b)` is the number of colour-`i` edges from `a` to `b`. The degree cochains are
`d_1 = 1` on `E_1`, `0` on `E_2`, and `d_2` symmetrically.

**Square complex.** `K(Λ)` is the 2-complex with vertices `V`, edges `E_1 ⊔ E_2` and one
2-cell per square. A real 1-cochain `c` on edges is a cocycle iff
`c(e) + c(f) = c(f') + c(e')` for every square. For `g : V -> R`,
`(δg)(e) = g(t(e)) - g(o(e))`.

**Cylinder-exchange group.** `[[Λ]]` is the group of homeomorphisms `g` of `X_Λ` for which
there are finitely many pairs of rectangles `(μ_k, λ_k)` with `t(μ_k) = t(λ_k)` such that:

- `{Z(μ_k)}` and `{Z(λ_k)}` are both partitions of `X_Λ`;
- `g(μ_k z) = λ_k z`.

When the compact open bisections of the Kumjian–Pask groupoid `G_Λ` are finite unions of
the basic sets `Z(λ, μ)`, this group is the topological full group `[[G_Λ]]`. That basis
fact is recorded (not pinned) in `finite-k-graph-boundary-groupoid-standard-facts`.

**Bricks.** Let `C = {0,1}^N`. A brick code is `w = (w_1,…,w_m)` with binary words `w_j`.

- `[w] = w_1C × … × w_mC ⊆ C^m`, with Lebesgue volume `2^{-|w|}`, where
  `|w| = Σ|w_j|`.
- Concatenation is coordinatewise: `vw = (v_1w_1, …, v_mw_m)`.
- The canonical map `[v] -> [w]` is `vz ↦ wz`.
- `[v]` and `[w]` are disjoint iff some coordinate has incomparable words, that is,
  neither is a prefix of the other.

**Definition (brick coding in dimension m).** A map `φ : E_1 ⊔ E_2 -> ({0,1}*)^m` such that:

- **(B1) partition.** For every vertex `a` and colour `i`, the bricks `[φ(e)]`, for
  `e ∈ E_i` with `o(e) = a`, are pairwise disjoint and cover `C^m`.
- **(B2) squares.** For every square `ef = f'e'` and every `j`,
  `φ_j(e)φ_j(f) = φ_j(f')φ_j(e')`.
- **(B3) nondegeneracy.** There is `N` such that every rectangle of degree `(N,N)`
  has a nonempty code in every coordinate.

By (B2) and the flip connectivity of lattice paths, `φ` extends to rectangles: `φ(λ)` is
the concatenation of edge codes along any monotone path from `(0,0)` to `(p,q)`, and it
does not depend on the path. The extension satisfies `φ(λρ) = φ(λ)φ(ρ)` whenever `λρ` is
a rectangle.

**Factorization.** Let `λ` be a rectangle of degree `(p+1,q)` at `a`. Write `e` for its
bottom-left colour-1 edge and `ρ` for its restriction to `[1,p+1]×[0,q]`, translated back
to the origin. The column `[0,1]×[0,q]` is then determined cell by cell from the bottom.
The bottom cell has known bottom `e` and right side `f`, so the square bijection gives its
left and top edges; the next cell up now has a known bottom and right side, and so on.
So `λ ↦ (e,ρ)` is a bijection between rectangles of degree `(p+1,q)` at `a` and pairs
with `o(e) = a`, `t(e) = o(ρ)`, `deg ρ = (p,q)`. The same holds with the colours exchanged.
In particular `|Λ^{(p,q)}(a)| = (M_1^p M_2^q 1)(a)`, so this set is nonempty whenever
every vertex emits edges of both colours.

## Part A. A brick coding embeds `[[Λ]]` in `mV`

**Theorem A.** Let `Λ` be a finite 2-graph in which every vertex emits edges of both
colours, and let `φ` be a brick coding in dimension `m`. Then:

1. `h_a(x) = ∩_n [φ(x|[0,n]^2)]` defines a homeomorphism `h_a : Λ^∞(a) -> C^m` for
   every `a`.
2. `h(λz) = φ(λ)h(z)` for every rectangle `λ` and every `z ∈ Λ^∞(t(λ))`.
3. For every `g ∈ [[Λ]]`, the conjugate `h g h^{-1}` is a piecewise canonical brick map of
   `⊔_a C^m`.
4. After identifying `⊔_a C^m` with `C^m` through a brick partition `{[u_a]}`,
   `g ↦ u h g h^{-1} u^{-1}` sends `[[Λ]]` injectively into Brin's `mV`, and it is
   multiplicative on composable elements.

So every group of homeomorphisms of `X_Λ` contained in `[[Λ]]` embeds in `mV`.

*Proof.*

**Step A1 (nested bricks, and h is a point).** Write `x_n = x|[0,n]^2`. Since
`x_{n+1} = x_n ρ` on a monotone path, `φ(x_{n+1})` extends `φ(x_n)` coordinatewise, so
the bricks are nested and closed. By factorization, `x_{kN}` is a concatenation of `k`
rectangles of degree `(N,N)` along the diagonal, and by (B3) each contributes at least
one letter in every coordinate. So `|φ_j(x_{kN})| ≥ k` for every `j`, and the
intersection is a single point `h_a(x)`. Two paths that agree on `[0,n]^2` have images
in the same brick `[φ(x_n)]`, whose diameter tends to 0 as `n -> ∞`. So `h_a` is
continuous.

**Step A2 (partitions P(p,q)).** Claim: for every vertex `a` and degree `(p,q)`, the
bricks `[φ(λ)]`, `λ ∈ Λ^{(p,q)}(a)`, partition `C^m`. The proof is by induction on
`p+q`, and `P(0,0)` is trivial because `φ(a)` is the empty code. Assume `P(p,q)` at every
vertex and take `λ ∈ Λ^{(p+1,q)}(a)`, factorized as `λ = eρ`. Then
`[φ(λ)] = φ(e)[φ(ρ)]`, the image of `[φ(ρ)]` under the canonical map `z ↦ φ(e)z`. That
map is a bijection `C^m -> [φ(e)]`. So for fixed `e`, the bricks `[φ(eρ)]` partition
`[φ(e)]` by the induction hypothesis at `t(e)`. By (B1) the `[φ(e)]` partition `C^m`. By
the factorization bijection every `λ` arises exactly once. The step `(p,q+1)` is the same.

**Step A3 (bijective).**

- *Injective.* If `x ≠ y` in `Λ^∞(a)`, then `x_n ≠ y_n` for some `n`. The bricks
  `[φ(x_n)]` and `[φ(y_n)]` are disjoint by `P(n,n)`, and they contain `h(x)` and `h(y)`.
- *Surjective.* Given `c ∈ C^m`, `P(n,n)` gives a unique `λ_n ∈ Λ^{(n,n)}(a)` with
  `c ∈ [φ(λ_n)]`. The restriction of `λ_{n+1}` to `[0,n]^2` has a brick containing
  `[φ(λ_{n+1})] ∋ c`, so by uniqueness it equals `λ_n`. The `λ_n` define `x ∈ Λ^∞(a)`
  with `h(x) = c`.

A continuous bijection from a compact space to a Hausdorff space is a homeomorphism. It
follows that `h(Z(λ)) = [φ(λ)]`.

**Step A4 (equivariance).** For `λ` of degree `(p,q)`, the restrictions of `λz` to
`[0,p+n]×[0,q+n]` are cofinal among finite regions, and they factor as `λ z_n`. So
`h(λz) = ∩_n φ(λ)[φ(z_n)] = φ(λ)h(z)`.

**Step A5 (conjugation).** Let `g ∈ [[Λ]]` have data `(μ_k, λ_k)`. By A3 and A4,
`h g h^{-1}` maps `[φ(μ_k)] = h(Z(μ_k))`, in the cube of `o(μ_k)`, onto `[φ(λ_k)]`, in the
cube of `o(λ_k)`, by `φ(μ_k)w ↦ φ(λ_k)w`. This is canonical. The domain bricks partition
`⊔_a C^m`, and so do the image bricks.

**Step A6 (landing in mV).** Choose a complete prefix code `u_a`, `a ∈ V`, of size `|V|`
in the first coordinate, and let `u` be the chart `z ↦ u_a z` on the cube of `a`. Then
`u h g h^{-1} u^{-1}` maps each brick `[u_{o(μ_k)}φ(μ_k)]` canonically onto
`[u_{o(λ_k)}φ(λ_k)]`, and both families partition `C^m`. Brin's `mV` consists of the
homeomorphisms of `C^m` that are canonical on the pieces of a dyadic (guillotine)
partition with dyadic image partition. An arbitrary brick partition need not be
guillotine, so refine:

- Subdivide the domain bricks into the uniform grid `G_L` for large `L`. This is
  guillotine, and the map stays canonical on each grid brick.
- The images of the grid bricks form a brick partition. Subdivide each image brick
  `[w]` uniformly to the grid `G_R` for large `R`.
- The pieces `[ww']` pull back to uniform subdivisions `[vw']` of the grid bricks `[v]`.
  So both partitions are guillotine, and the map is canonical piece by piece.

Conjugation is injective and multiplicative. ∎

## Part B. Rigidity: cohomology forces the shape of a brick coding

**Hypotheses.**

- **(R1)** `M_1` and `M_2` are irreducible, with constant row sums `N_1` and `N_2`.
- **(R2)** `H^1(K(Λ); R) = R[d_1] ⊕ R[d_2]`.
- **(R3)** Under the relation generated by `e ~ e'` over all squares `ef = f'e'`, the
  colour-1 edges form a single class. Likewise the colour-2 edges form a single class
  under `f ~ f'`.

`[d_1]` and `[d_2]` are always linearly independent. A coboundary sums to 0 around
every cycle, while around a colour-1 cycle `d_1` sums to its length and `d_2` sums to 0.
So (R2) says exactly that `dim H^1(K(Λ); R) = 2`.

**Proposition B.** Assume (R1)–(R3) and let `φ` be a brick coding in dimension `m`.
Write `ℓ_j(e) = |φ_j(e)|` and `L = Σ_j ℓ_j`.

- (a) `N_1 = 2^α` and `N_2 = 2^β` for integers `α`, `β`. Every colour-1 edge has total
  code length `α`, and every colour-2 edge has total code length `β`.
- (b) For every `j` there are reals `α_j, β_j > 0` with `Σ_j α_j = α` and `Σ_j β_j = β`.
- (c) If `M_1` is primitive, every `α_j` is a positive integer, so `m ≤ α`. Similarly
  `m ≤ β` if `M_2` is primitive.

**Corollary B1.** If (R1) and (R2) hold and `N_1` or `N_2` is not a power of 2, then `Λ`
has no brick coding in any dimension. Only Step B1 below is used.

**Corollary B2.** If (R1)–(R3) hold, `N_1 = N_2 = 4`, and `M_1`, `M_2` are primitive, then
every brick coding has `m ≤ 2` and total code length exactly 2 on every edge.

*Proof.*

**Step B1 (Kraft and Perron–Frobenius).** By (B2) lengths add along squares, so each
`ℓ_j` is a cocycle, and so is `L`. By (R2), `L = αd_1 + βd_2 + δg` for some reals `α`,
`β` and some `g : V -> R`.

The brick `[φ(e)]` has volume `2^{-L(e)}`, and by (B1) the colour-1 bricks at `a` have
total volume 1:

`Σ_{o(e)=a, e∈E_1} 2^{-α - g(t(e)) + g(a)} = 1`, i.e. `M_1 v = 2^α v` with `v = 2^{-g} > 0`.

For an irreducible nonnegative matrix, the spectral radius is the only eigenvalue with a
positive eigenvector, and its eigenspace is one-dimensional. The constant vector is a
positive eigenvector for the eigenvalue `N_1`. Hence `2^α = N_1`, `v` is constant, and
`g` is constant. The same argument in colour 2 gives `2^β = N_2`. So `L = α` on `E_1` and
`L = β` on `E_2`, and both are integers because code lengths are. This proves (a) and
Corollary B1.

**Step B2 (per coordinate).** By (R2), `ℓ_j = α_j d_1 + β_j d_2 + δg_j`. Summing over `j`
and using the uniqueness of coordinates in `H^1` gives `Σα_j = α` and `Σβ_j = β`. By
irreducibility there is a colour-1 cycle, say of length `p`. Along it `ℓ_j` sums to
`α_j p`, which is `≥ 0`, so `α_j ≥ 0`. Similarly `β_j ≥ 0`.

**Step B3 (nondegeneracy gives α_j + β_j > 0).** Fix `k ≥ 1` and a rectangle `λ` of
degree `(kN,kN)`. It exists by the factorization count. Summing `ℓ_j` along a monotone
path, `|φ_j(λ)| = kN(α_j+β_j) + g_j(t(λ)) - g_j(o(λ))`. By Step A1, `|φ_j(λ)| ≥ k`. So
`k ≤ kN(α_j+β_j) + 2 max|g_j|` for every `k`, which forces `α_j + β_j ≥ 1/N`.

**Step B4 (pure coordinates are constant).** Suppose `β_j = 0`.

- On colour-2 edges, `ℓ_j(f) = g_j(t(f)) - g_j(o(f)) ≥ 0`.
- Each colour-2 edge lies on a colour-2 cycle (irreducibility), and `δg_j` sums to 0 around
  it. All terms are nonnegative, so all are 0.
- Hence `φ_j` is empty on `E_2`, and `g_j` is constant (strong connectivity of colour 2).
- By (B2), `φ_j(e) = φ_j(e')` on every square `ef = f'e'`. By (R3), `φ_j` is a constant
  word `w_j` on `E_1`.
- By Step B3, `|w_j| = α_j > 0`.

**Step B5 (no pure coordinates).** Let `S = {j : β_j = 0}` and suppose `S ≠ ∅`. By B4,
every colour-1 brick at `a` lies inside `{c ∈ C^m : c_j ∈ w_jC for all j ∈ S}`. That set
is a proper subset of `C^m` because each `w_j` is nonempty, which contradicts the covering
part of (B1). So `β_j > 0` for every `j`. Symmetrically, `α_j > 0` for every `j`. This
proves (b).

**Step B6 (integrality).** If `M_1` is primitive, the gcd of its cycle lengths is 1, so
there are cycles whose lengths `p_1, …, p_r` have gcd 1. Each `α_j p_i` is an integer,
since it is a sum of code lengths, and by Bézout `α_j ∈ Z`. With (b) this gives
`α_j ≥ 1`, so `m ≤ Σ α_j = α`. This proves (c). ∎

Corollary B2 follows from (a) and (c) with `α = β = 2`.

**Remark (padding).** A coding in dimension 1 padded by an empty second coordinate
satisfies (B1) and (B2), though not (B3). So a search for dimension-2 solutions of
(B1)+(B2) with total length 2 covers dimensions 1 and 2 at once.

**Sanity check: the rigidity is genuinely two-dimensional.** For one-graphs the analogue
of Corollary B1 is false. Take the one-vertex graph with three loops, whose full group is
Higman–Thompson `V_{3,1}`. The prefix code `{0, 10, 11}` is a brick coding in dimension
1, and it embeds `V_{3,1}` in `V`. Here `H^1` of the graph is 3-dimensional, so (R2)
fails. In a 2-graph the squares cut `H^1` down, and this is what forces the rigidity.

## Part C. Robertson–Steger 2-graphs of CMSZ groups over PG(2,2) and PG(2,3)

**Model.** Fix a triangle presentation `T` compatible with `λ : points -> lines` of
`PG(2,q)`, and let `Γ_T = ⟨a_x | a_xa_ya_z = 1, (x,y,z) ∈ T⟩`.

- The code checks (A1)–(A3) (`tp.py`, `check_q3.py`).
- A tile is a Γ-orbit of shape-(1,1) words in the building apartment, recorded as labels
  `(x,y,z,u,w)` with `(x,y,z) ∈ T`, `(y,u,w) ∈ T` and `u ≠ z`.
- Edge rules and squares are as in `rs2graph.py`. The script asserts the unique-filling
  property and that the square map is a bijection, which is how the model is checked.
- For `q = 2` this gives 42 tiles, `168 + 168` edges and 672 squares, with row sums 4.
- For `q = 3` it gives 156 tiles, `1404 + 1404` edges and 12636 squares, with row sums 9.

That this tile 2-graph is the Robertson–Steger 2-graph is recorded in the graph node
`a2-group-embeds-in-full-group-of-its-rs-two-graph`, not proved here. All statements
below are about the explicit finite 2-graphs `Λ_T` built by the code.

**q = 2.** There are five presentations `T0..T4` (`tp_q2.json`, found by exact cover).
`certificate.py nosat` checks each one:

- (A1)–(A3) hold.
- Row sums are 4.
- `M_1` and `M_2` are primitive, with exponents 5,5 (4,4 for T2).
- (R2): `dim H^1(K(Λ_T); Q) = 2`. The rank of the coboundary `C^1 -> C^2` over `GF(1000003)`
  is a lower bound for its rank over `Q`, which gives `dim H^1 ≤ 2`. The independence of
  `[d_1]` and `[d_2]` gives `≥ 2`.
- (R3): one transport class per colour (union–find).

By Corollary B2 every brick coding has `m ≤ 2` and total length 2 on every edge, and by
the padding remark a single SAT instance per presentation covers it.

**SAT encoding** (`brick_sat.py`, `uniform=True`).

- Codes: the 12 two-letter brick codes in dimension 2.
- Partitions: the 7 partitions of `C^2` into 4 such bricks.
- For each vertex and colour, one selector per ordered partition, covering its 4 edges.
- For each square, auxiliary product variables forced by both factorizations, with at
  most one of them true. This encodes `φ(e)φ(f) = φ(f')φ(e')`.

UNSAT is sound for nonexistence: from any coding, set the corresponding variables and
the single product variable of each square.

**Results** (`certificate_uniform.py`, log `certificate_uniform.log`).

| instance | CaDiCaL 1.5.3 | Glucose 4 |
|---|---|---|
| T0 | UNSAT, 13.9 s | UNSAT, 5.2 s |
| T1 | UNSAT, 16.2 s | UNSAT, 1.9 s |
| T2 | UNSAT, 26.7 s | UNSAT, 3.5 s |
| T3 | UNSAT, 14.3 s | UNSAT, 1.8 s |
| T4 | UNSAT, 28.0 s | UNSAT, 3.0 s |

Each instance has 128688 variables and 419412 clauses.

**Cross-checks.** None of these depend on Proposition B.

- The full-domain dimension-2 instance uses all 49 codes of total length at most 3 and
  all 39 four-brick partitions, so it is complete for `m ≤ 2` with no rigidity input.
  It is UNSAT for T0 with both solvers (231.8 s and 63.5 s) and for T1 with CaDiCaL
  (507.9 s) (`certificate.log`).
- The uniform `m = 3` instance for T0 is UNSAT (`run_T0_m34.log`).
- Controls (`control_product.log`): the product 2-graph `B_4 × B_4` is SAT at `m = 2`
  and finds the expected coding. A twisted one-vertex 2-graph is UNSAT.

**Corollary C1.** For `T0..T4` over `PG(2,2)`, `Λ_T` admits no brick coding in any
dimension. This rests on Proposition B plus the recorded solver runs; there are no DRAT
proof logs, and the results were cross-checked with two solvers.

**q = 3.** There are two presentations over `PG(2,3)` (`tp_q3.json`, random `λ` plus
exact cover, verified by `check_q3.py`). `q3_hypotheses.py` computes the row sums
(9 = `q^2`), primitivity, and `dim H^1(K(Λ_T);Q)`. The results are in `q3_hypotheses.log`.

- For T0 and T1, all row sums are 9 and both colour matrices are primitive with
  exponent 4.
- The integer Gram matrix `DᵀD` of the coboundary has rank 2651 over `GF(32749)`.
- So `dim H^1 ≤ 2808 − 2651 − 155 = 2`, and hence `= 2`.

(R1) and (R2) therefore hold, and Corollary B1 applies: 9 is not a power of 2, so neither
2-graph has a brick coding in any dimension, and no SAT is needed.
(Route `cmsz-pg23-no-brick-coding-by-kraft`.)

## Part D. What this kills, and what survives

**Decomposition of the route.** Route: an infinite Kazhdan subgroup of `mV` via
Ã₂-groups:

- **(P1)** `Γ_T` has (T). This is imported: CMSZ groups act properly and cocompactly on
  Ã₂ buildings.
- **(P2)** `Γ_T ↪ [[Λ_T]]`, the node `a2-group-embeds-in-full-group-of-its-rs-two-graph`.
- **(P3)** `[[Λ_T]] ↪ mV`.

Theorem A reduces (P3) to the existence of a brick coding of `Λ_T`.

**Obstruction (killed class).** Consider the approaches that realize (P3) by one
homeomorphism `X_{Λ_T} -> ⊔ C^m` sending each cylinder `Z(λ)` to a brick and each
cylinder map `z ↦ λz` to the canonical map. This is the class of edge-wise brick codings
of the tile 2-graph.

- **Invariant:** `H^1` of the tile square complex together with the Perron eigenvalue.
- **Where it dies:**
  - For `N = q^2` not a power of 2 (every `q` other than `2^r`, given (R2)), every member
    dies at Step B1: the Kraft equality forces `2^α = q^2`.
  - For `q = 2`, every member is pushed by Steps B4–B6 into dimension `≤ 2` with uniform
    length 2, and dies at the square equations (B2), by the UNSAT certificate of
    Part C for T0..T4.

**Survivors (not killed).**

1. **Block recodings.** Replace `Λ_T` by a higher-block 2-graph `Λ^{[k]}`, whose vertices
   are rectangles of degree `(k,k)`. Its full group is the same `[[Λ_T]]`, and its row sums
   are still `q^2`, by unique filling of the new column. A brick coding of `Λ^{[k]}` gives
   the same kind of embedding.
   - For `q` not a power of 2, Corollary B1 still kills it whenever
     `dim H^1(K(Λ^{[k]}); R) = 2`.
   - Whether that holds for all `k` is the precise open point. It is a "Livšic rigidity"
     statement for the Ã₂ square complex.
   - For `q = 2` and `k ≥ 2`, the SAT instances are larger and were not run.
2. **Measure-theoretic form.** Suppose `h : X_Λ -> Y ⊆ ⊔C^m` is a homeomorphism onto a
   clopen set that conjugates every compact open bisection of `G_Λ` to a piecewise
   canonical brick map. Pull back Lebesgue measure. Its Radon–Nikodym cocycle
   `c = log_2 (dμ∘γ/dμ)` is a continuous `Z`-valued cocycle on `G_Λ`.
   - *Missing prerequisite (OPEN):* every continuous real cocycle on `G_{Λ_T}` has the
     form `⟨s,D⟩ + g∘r - g∘s` with `g` continuous, where `D` is the degree cocycle.
   - *Argument, given the prerequisite:* the measure `2^g μ` scales cylinders by
     `2^{-⟨s,D⟩}`. Perron–Frobenius then gives `2^{s_1} = N_1` and `2^{s_2} = N_2`.
   - At the fixed point `ξ^∞` of `z ↦ ξz`, for a cycle rectangle `ξ` of degree
     `(p,q) ≠ 0`, the value `c = s_1p + s_2q` is an integer. With
     `N_1 = N_2 = 9` this reads `(p+q) log_2 9 ∈ Z`, which is impossible.
   - So for `q = 3` this single prerequisite would kill **every spatial groupoid-level
     embedding**, not only brick codings of a fixed presentation.
   - The prerequisite is plausible but not automatic. The tail relation of `G_Λ` can
     carry `lim^1` classes, and for one-graphs it fails (the `V_{3,1} ≤ V` example).
3. **Non-spatial embeddings.** An abstract embedding `[[Λ_T]] ↪ mV` need not come from any
   conjugacy of groupoids. Nothing here touches these, nor embeddings of `Γ_T` alone
   (bypassing (P2)), nor Kazhdan subgroups not arising from Ã₂-groups. The assigned
   question stays open.
4. **q = 2^r, r ≥ 2.** For `q = 4`, Corollary B2's analogue allows `m ≤ 4`, and nothing
   was computed.

**Belief update.** Before this, the natural expectation was that `[[Λ_T]]` sits in `2V`
"because the boundary is a product of two Cantor coordinates". That is false at the
level of edge-wise codings. The two colours of `Λ_T` cannot be separated into brick
coordinates, and for `q` not a power of 2 (9, 25, …) the entropy `log_2 q^2` is not
even an integer.

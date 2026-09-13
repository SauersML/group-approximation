# A coset system with no affine relabeling (but an abelian algebra)

Lane `ex-kac-quantum-compiler`, 2026-09-13, part 6.  Corrects the title form
of `coset-system-algebras-reduce-to-abelian-coset-systems`.  Part 5 listed
three places where a proof of relabelability could fail.  This example lives
in the second: one nonabelian section shared by several fibres through
different extensions.

## 1. The system

Let `Q = Q_8`, with its three cyclic subgroups `C_1, C_2, C_3 ≅ Z_4` and
centre `Z`.  For `i = 1,2,3` put

```text
K^(i) = { (g,h) in Q x Q : g C_i = h C_i }        (order 32),
N_1^(i) = C_i x 1,    N_2^(i) = 1 x C_i,    N_3^(i) = { (a,a) : a in C_i }.
```

**Normality.**  `N_1, N_2` are clearly normal.  For `N_3`, write `g = h c`
with `c in C_i`.  Then
`(g,h)(a,a)(g,h)^(-1) = (h c a c^(-1) h^(-1), h a h^(-1)) = (h a h^(-1), h a h^(-1))`,
since `C_i` is abelian.

**A diamond.**  The three subgroups pairwise intersect trivially, and each
pairwise product is `T = C_i x C_i`.  So they form a diamond with abelian
section `T ≅ Z_4^2`, as in (A3) of part 5.

**Fibres and relations.**
- One fibre `q` with group `Q`.
- Fibres `k_i` with groups `K^(i)`.
- Fibres `r_(i,1)`, `r_(i,3)` with groups `K^(i)/N_1^(i)` and `K^(i)/N_3^(i)`.
- Relations are graphs of quotient maps:
  - `k_i -- q` through `K^(i) -> K^(i)/N_2^(i) ≅ Q`, `(g,h) |-> g`;
  - `k_i -- r_(i,1)` and `k_i -- r_(i,3)` through the other two quotients.

Each relation is a Goursat coset.  The constraint graph is a tree, so there is
no holonomy, and every point is supported by a classical solution.  Hence
neither the support fixpoint nor pruning changes anything.

## 2. No affine relabeling

Suppose abelian labelings `β` make every relation an abelian coset.

**Step 1 (quotients become affine).**  A relation that is the graph of a
quotient map `π` becomes an affine surjection `A_(k_i) -> A_r`.  Its fibres
are the cosets of a subgroup `M_j = β(N_j)`.  Common refinements and joins of
coset partitions are cosets of intersections and sums.  So in `A_(k_i)`:

```text
|M_j| = 4,   M_j ∩ M_l = 0 (j != l),   M_j + M_l = W with |W| = 16.
```

**Step 2 (Albert).**  On a `T`-coset of `K^(i)`, the three quotient maps
send cells to `T/N_1`, `T/N_2`, `T/N_3`.  The set of triples of cells that
meet is the Cayley table of `Z_4`, as a Latin square: `(a, b) |-> a b^(-1)`.
After relabeling, the same triples are the Cayley table of
`W/M_1 ≅ M_2` inside an abelian group.
- An affine relabeling is an isotopy of these Latin squares.
- Isotopic groups are isomorphic (A. A. Albert, *Quasigroups I*, 1943; not
  re-read here).
- So `M_2 ≅ M_1 ≅ Z_4`: the relabeling is cyclic on the section.

**Step 3 (at `q`).**  `A_q = A_(k_i)/M_2` affinely, and the partition of
`Q` into `C_i`-cosets is carried by `W/M_2 ≅ M_1 ≅ Z_4`.  So `A_q`, an abelian
group of order 8, contains a cyclic subgroup realizing the `C_i`-partition, for
each `i = 1,2,3`.  These partitions are distinct, so the three cyclic
subgroups are distinct.

**Step 4 (contradiction).**  No abelian group of order 8 has three distinct
cyclic subgroups of order 4:
- `Z_8` has one;
- `Z_4 x Z_2` has two, `<(1,0)>` and `<(1,1)>`;
- `Z_2^3` has none.

So this presentation admits no affine relabeling.  QED.

## 3. But its algebra is abelian

Every fibre `r_(i,j)` is a coarse-graining of `k_i`, and `k_i` refines `q`
with 4-point cells.  So

```text
A(S) ≅ C(K^(1)) *_(C(Q)) C(K^(2)) *_(C(Q)) C(K^(3)),
```

amalgamated over the eight atoms of `C(Q)`.  Atom by atom this is
`C^4 * C^4 * C^4`.  The same algebra is presented by the abelian coset system:
- one fibre `Z_8`;
- three fibres `Z_8 x Z_4`, each related to the first by the projection.

So `A(S)` is a solution-group corner.  Relabeling failed only because the
leaves `r_(i,j)` add redundant partitions that record the *group* structure
of the sections.

## 4. What this changes

1. `relabelable-coset-systems-are-solution-group-corners` is a property of a
   presentation, not of the algebra.  This example shows that it is strictly
   presentation-dependent.
2. The title form of `coset-system-algebras-reduce-to-abelian-coset-systems`
   ("every coset system admits an affine relabeling after pruning") is
   **false**.  The algebra-level form survives, and a proof must change
   presentations: delete redundant coarse-grainings, merge fibres, refine.
3. The mechanism is a Latin-square isotopy invariant of the sections.  It
   becomes algebra-level data only when the forcing fibres `r_(i,j)` carry
   independent PVMs glued to further structure, not mere coarse-grainings.
   That is where a genuinely nonabelian coset-system algebra, if one exists,
   should be sought.

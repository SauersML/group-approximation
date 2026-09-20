# Scalar five-twist detectors have regular edge spectra away from characteristic five

2026-09-20. The full hyperbolic residual-finiteness target remains open.
This note gives regular edge spectra over every algebraically closed
field of characteristic other than five, including zero. Its composition
balances and small-dimension classification specialize to characteristic
19. Vertex modules need not be semisimple or isotypic. No computation is used.

## 1. Setup and the conjugacy calculation

Let `S=PSL_2(F_19)` and pin the triangle edge generators by the classes of

```
x12=[[2,11],[16,3]], x13=[[5,11],[4,9]], x23=[[6,15],[12,8]].
```

Their determinants are one. Their traces are respectively `5,14,14`.
Thus the three lifts `-x12,x13,x23` have the same characteristic
polynomial `t^2-14t+1`. Its discriminant is `14^2-4=2` in `F_19`,
which is nonsquare: the nonzero square classes are
`1,4,9,16,6,17,11,7,5`. In particular these are regular nonsplit
semisimple matrices.

Matrices over `F_19` with this irreducible characteristic polynomial
are conjugate in `GL_2(F_19)`: identify the natural plane with the
field `F_361`, so each matrix acts by multiplication by a root.
They are also conjugate in `SL_2(F_19)`. Indeed the centralizer of
one is `F_361^*`, whose determinant is the norm to `F_19^*` and is
surjective. Multiply a `GL_2` conjugator by a suitable centralizer
element to correct its determinant to one. The norm is surjective
because finite-field multiplicative groups are cyclic and the norm
is the twentieth-power map from a group of order 360 to one of
order 18.

The inverse of each displayed lift has the same characteristic
polynomial. The same argument shows conjugacy to its inverse in
`SL_2(F_19)`. Passing to `S`, all three `xij` therefore belong to
one conjugacy class `C`, and `C=C^-1`.

For completeness the roots have order five. Let `z` satisfy
`z^2-4z+1=0`, so `z+z^-1=4`. Then `z^2+z^-2=14`, and

```
z^-2(1+z+z^2+z^3+z^4)=14+4+1=0.
```

Since `z!=1`, it has order five, and the roots of `t^2-14t+1`
are `z^2,z^-2`. Fix `eta=z^2` as the primitive fifth root used
below. Changing this choice only permutes the nonzero eigenvalue
indices and does not change uniformity or the balance equations.

## 2. One nonzero twist forces uniformity everywhere

Let `K` be algebraically closed of characteristic different from five,
including characteristic zero. Consider any
finite-dimensional representation of the centrally twisted triangle,
with central `Z^5=1` acting as a nontrivial scalar `eta^t`, where
`t in F_5^*`. The twist triple `d` is nonzero.

For vertex `i`, let `n_i(j)` denote the multiplicity of `eta^j`
on its representation of any element in `C`, for `j in F_5`.
It is independent of the chosen edge element by conjugacy. Every
order-five matrix is diagonalizable in these characteristics, even if
the entire vertex module is not semisimple. Inversion-conjugacy gives

```
n_i(j)=n_i(-j).                                  (1)
```

On edge `i--l` the relation
`s_i(x)=Z^(d_il)s_l(x)` gives, with `s=t d_il`,

```
n_i(j)=n_l(j-s).                                 (2)
```

Choose an edge with `d_il!=0`, hence `s!=0`. Combining (1) and (2),

```
n_i(2s-j)=n_l(s-j)=n_l(j-s)=n_i(j).
```

Thus `n_i` is invariant under both reflections `j -> -j` and
`j -> 2s-j`; their composite is translation by `2s`. This nonzero
element generates the additive group `F_5`, so `n_i` is constant.
Equation (2) makes `n_l` constant too. Each remaining edge equation
is a translation of multiplicity vectors, including when its twist
is zero; connectedness of the triangle makes the third vertex
constant as well. The common ambient dimension forces the same
constant at all vertices.

Consequently the dimension is `5m`, and every vertex restriction
to each cyclic edge is exactly `m` copies of the regular `K[C_5]`
module. This proves the spectral statement for arbitrary modules,
with no classification or cohomology input.

## 3. Exact integer balance on composition factors

For this and all subsequent sections, assume `K` has characteristic
19. The defining-characteristic simple modules of `S` over `K` are

```
L_r=Sym^r(K^2),  r=0,2,4,...,18,
```

of dimensions `r+1`. This standard classification is stated explicitly
in the university-repository copy of David A. Craven, *Maximal PSL2
Subgroups of Exceptional Groups of Lie Type*, Memoirs AMS 276 (2022),
no. 1355, [Section 7.3, printed page 57](https://pure-oai.bham.ac.uk/ws/portalfiles/portal/58662428/rank1memoir.pdf):
the symmetric powers of degrees `0,...,p-1` exhaust the simple
`SL_2(p)` modules, and exactly the even degrees factor through
`PSL_2(p)`. The present note does not claim this classification as
a new theorem. In particular, simplicity of the weights `r>=10`
comes from this sourced classification, not from the distinct
finite-torus-weight argument used only for `r<=8` in the root's
elementary Sym4 rigidity proof.

Let `n_r` be the composition multiplicity of `L_r` at a fixed vertex.
The cyclic edge restriction is semisimple, so its eigenvalue
multiplicities add across every composition series, whether or not
the original vertex module splits. On `L_r` the eigenvalues are
`eta^(r-2i)` for `0<=i<=r`. Counting these exponents gives:

| highest weight r | multiplicity of 1 | multiplicity of each eta^±1 | multiplicity of each eta^±2 |
|---|---:|---:|---:|
| 0 | 1 | 0 | 0 |
| 2 | 1 | 0 | 1 |
| 4 | 1 | 1 | 1 |
| 6 | 1 | 2 | 1 |
| 8 | 1 | 2 | 2 |
| 10 | 3 | 2 | 2 |
| 12 | 3 | 2 | 3 |
| 14 | 3 | 3 | 3 |
| 16 | 3 | 4 | 3 |
| 18 | 3 | 4 | 4 |

Equality between the first and third columns gives

```
n0+n10=n8+n18.                                  (3)
```

Equality between the first and second columns, minus (3), gives

```
n2+n12=n6+n16.                                  (4)
```

Conversely (3)--(4) make all five eigenvalue multiplicities equal.
These are equalities of nonnegative integers, not congruences modulo
19 or five. Both hold independently at all three vertices.

Equivalently, the nonnegative monoid of balanced composition vectors
is generated by the following ten vectors:

```
L4; L14;
Li+Lj with i in {0,10}, j in {8,18};
Li+Lj with i in {2,12}, j in {6,16}.
```

Indeed (3) permits pairing every occurrence on its left with one
on its right, and (4) permits the independent second pairing; `n4`
and `n14` are unrestricted. Each displayed vector is indecomposable
in this monoid. This statement concerns composition multiplicities,
not a direct-sum decomposition of the vertex module or of the global
triangle representation.

## 4. First mixed sectors and a sharp small-dimension boundary

In dimension five the only balanced module has the sole factor `L4`.
In dimension ten the only possible vertex composition types are

```
2 L4,   L0+L8,   L2+L6.                         (5)
```

All three split. For `2 L4`, the established Sym4 rigidity proof
applies. For the other two, `Ext^1(L0,L8)` and its reverse vanish,
as do `Ext^1(L2,L6)` and its reverse. Here is a specialized reason:
for even `r,s` with `r+s<16`, the low-weight Clebsch--Gordan
decomposition of `L_r^* tensor L_s` has only even summands `L_j`
with `j<16`. Restriction of `H^1(S,L_j)` to the order-19 Sylow
subgroup is injective by averaging its 180 cosets. Its image is
normalizer-fixed, whereas the one-dimensional Sylow cohomology
has torus weight `a^(-j-2)`; for `j<16` this is nontrivial on
`F_19^*`. Hence every summand has zero `H^1`.

The Clebsch--Gordan maps can be proved in this range exactly as
in the root's Sym4 rigidity artifact: multiply the polarized
degree-`r+s-2j` form by `(xY-yX)^j`, extract bidegree `(r,s)`,
and specialize the two pairs of variables. The resulting binomial
coefficient has top degree below 19 and is nonzero, so all simple
summands inject and their dimensions add to `(r+1)(s+1)`.
This proves the particular mixed extension vanishings without using
the full Ext classification.

In dimension fifteen the possible composition types are

```
L14, 3 L4, L4+L0+L8, L4+L2+L6.                 (6)
```

They too are semisimple: distinct factors in the latter cases have
pairwise weight sums below 16, and the only repeated factor is
`L4`, whose self-extensions vanish. This can be iterated along a
composition series because Ext is additive on a split kernel.

Therefore any scalar central detector of dimension below twenty
has semisimple vertex restrictions, and its positive dimension is
ten or fifteen: the dimension-five case is excluded by the already
proved amplified Sym4 theorem. In dimension ten at least one vertex
must have one of the two mixed types in (5); the all-`2 L4` case is
excluded by that theorem. No existence assertion for the remaining
types is made, and different vertices may have different types.

## 5. Full Ext adjacency: recorded prior input, not needed above

Craven Section 7.3, printed pages 57--58, states the projective
covers of simple modules for `SL_2(p)`, with explicit trivial and
Steinberg exceptions. Translating its dimension labels `i=r+1`
to highest weights gives, for `S=PSL_2(F_19)`,

```
dim Ext^1(L_r,L_s)=1  iff r,s<=16 and r+s is 16 or 18;
dim Ext^1(L_r,L_s)=0  otherwise.
```

Here both weights are even. Thus the adjacency graph is

```
0 -- 16 -- 2 -- 14 -- 4 -- 12 -- 6 -- 10 -- 8
                                                  loop at 8
18 is isolated and projective.
```

The memoir cites the standard projective-module descriptions and
Andersen--Jorgensen--Landrock, *The projective indecomposable modules
of SL(2,p^n)*, Proc. London Math. Soc. 46 (1983), 38--52
([publisher record](https://doi.org/10.1112/plms/s3-46.1.38)).
The primary publisher record and the explicit university-repository memoir
were checked; the paywalled AJL Corollary 4.5 itself was not inspected.
Accordingly this full adjacency is a sourced prior input, not a
new elementary proof or a premise of the canonical balance claim.

The first possible balanced nonsplit modules have dimension twenty.
For example `Ext^1(L14,L4)` is nonzero according to the stated
classification, and both constituents already have uniform C5
spectra, giving balanced nonsplit modules of dimension twenty.
There are also allowed extension sectors joining `L2` with `L16`,
`L6` with `L12`, or `L8` with `L10`. This shows exactly where the
small-weight rigidity mechanism stops; it does not construct a
representation of the triangle or a detector.

## 6. Why local balance and Ext splitting do not finish the task

Distinct balanced composition sectors have identical order-five
spectra after adjusting their common dimension. Edge intertwiners
can mix equal-eigenvalue spaces belonging to different simple
constituents. A vertex's isotypic decomposition is not thereby
preserved by either of the other vertex groups. Neither the monoid
decomposition nor the Ext graph supplies a global invariant subspace
of the triangle representation. Passing to a putative smaller
detector along those local summands would be unjustified.

Thus (3)--(4) are a genuine arbitrary-module reduction, but not a
reduction of all mixed detectors to the excluded Sym4 family. The
first open mixed placements are concretely (5), while higher
dimensions also introduce the sourced extension sectors above.
No finite-dimensional search, local computation, or MSI job ran.

The root lane independently reviewed the spectral argument, table,
and low-dimensional enumeration and returned PASS. Its requested
characteristic refinement has been incorporated: only Sections 3--5
use characteristic 19, while Section 2 works in every characteristic
other than five.

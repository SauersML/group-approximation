# First mixed ten-dimensional placements: exact equations and structural reductions

2026-09-20. No detector is constructed and no all-placement exclusion
is claimed. The hyperbolic residual-finiteness target remains open.
This bounded pass supplies a gauge-correct polynomial system and
excludes reducible, imprimitive, and tensor-product placements by
proof. No computation was launched, including the optional MSI pilot.

## 1. Scope and non-duplication

Use the pinned triangle with vertices `S=PSL_2(F_19)`, central
`Z^5=1`, a nonzero edge-twist triple, and generators represented by

```
x12=[[2,11],[16,3]], x13=[[5,11],[4,9]], x23=[[6,15],[12,8]].
```

Work over `K=overline(F_19)` with a nontrivial scalar central image.
Every ten-dimensional vertex restriction is semisimple and has one
of the three types established in the mixed spectral-balance audit:

```
A = L4 + L4,  B = L0 + L8,  C = L2 + L6,
Lr = Sym^r(K^2).
```

All-A placements are already excluded by the stable Sym4 theorem.
The other 26 ordered type triples are not identified with one
another here. In particular there is no assumed symmetry of the
pinned triangle exchanging vertices or exponent triples.

The current wave-five audit and detector nodes were read before
this pass. They concern other-prime K7 restrictions and mod-three
homology of the specified PSL2(19)-squared kernel, not these mixed
matrix placements. No concurrent wave-five files were changed.
Existing `hrf-amplified`, `hrf-mixed`, and `hrf-sym4` work is reused,
not overwritten. All reductions below are elementary consequences
of those stated results; no new external classification is invoked.

## 2. Every surviving placement is absolutely irreducible and primitive

The established all-characteristic degree bound says that every
representation of this twisted triangle of positive dimension at
most nine kills `Z`. On the present ten-dimensional space `Z`
acts as a nontrivial scalar. Any proper nonzero invariant subspace
would inherit that scalar and have dimension at most nine, which
is impossible. Thus every possible detector in this sector is
irreducible over `K`, hence absolutely irreducible. Its commuting
endomorphisms are scalars.

Suppose there were a nontrivial imprimitivity decomposition into
`r` equal-dimensional blocks permuted by the triangle. Then
`2<=r<=10`. Each `S` vertex acts on these blocks through `Sym_r`.
Since nineteen does not divide `r!`, its order-nineteen upper
root subgroup acts trivially. The conjugate lower root subgroup
does too, and these generate `S`, so the entire vertex action
on the set of blocks is trivial. Each block is therefore preserved
by all three vertices and by the scalar `Z`. The blocks are
globally invariant, contradicting irreducibility. Hence every
possible detector here is primitive.

These are statements about the entire triangle image. They do
not falsely identify a vertex's proper simple summands with global
invariant subspaces.

## 3. Coprime tensor-factor placements are impossible

Suppose the entire image preserves a tensor-product structure
`K^10=K^2 tensor K^5`, in the sense that every image matrix is a
tensor product of invertible factor matrices. The unequal dimensions
exclude a factor-exchange ambiguity. Fix one vertex. For each
`g in S`, choose `a_g in GL_2(K)` and `b_g in GL_5(K)` with
`rho(g)=a_g tensor b_g`, normalized at the identity. Then

```
a_g a_h = c(g,h) a_gh,
b_g b_h = c(g,h)^-1 b_gh.
```

Taking determinants gives `delta(det a)=c^2` and
`delta(det b)=c^-5`, where `delta t(g,h)=t(g)t(h)/t(gh)`.
Therefore the scalar cochain

```
t(g)=det(a_g)^3 det(b_g)
```

satisfies `delta t=c^(6-5)=c`. Replacing `a_g` by `t(g)^-1 a_g`
and `b_g` by `t(g)b_g` gives genuine linear representations on
both factors while preserving the vertex tensor representation.
This is an explicit coprime-dimension lifting argument, not an
assumption that arbitrary projective representations lift.

In characteristic nineteen every two-dimensional genuine `S`
representation is trivial. The defining-characteristic simple
modules have dimensions `1,3,5,...,19`; thus its factors are
trivial, and its image is solvable unitriangular. The perfectness
of `S` makes that image trivial. Consequently the vertex module
is two copies of a five-dimensional module. The regular edge
spectrum in total dimension ten makes the latter module's edge
spectrum uniform in dimension five. Composition balance forces
that factor to be `L4`. Every vertex is therefore of type A,
contradicting the amplified Sym4 obstruction.

Thus no surviving ten-dimensional mixed detector preserves a
`2 tensor 5` tensor-product structure. This argument does not
exclude all tensor constructions in larger dimensions or infer
anything about arbitrary radical extensions.

## 4. Exact equations for an arbitrary ordered type triple

Choose the indicated direct-sum models `R1,R2,R3` for the three
vertex types, and put

```
A1=R1(x12), B1=R1(x13),
A2=R2(x12), C2=R2(x23),
B3=R3(x13), C3=R3(x23).
```

Each of these six matrices has every fifth root as eigenvalue
with multiplicity two. Choose a primitive fifth root `eta` and
ordered eigenbases `P_X` satisfying

```
X P_X = P_X diag(I2,eta I2,...,eta^4 I2).
```

All coefficients can be chosen in `k=F_361`: the representations
are defined over `F_19`, and the fifth roots lie in `F_361`.
Fix vertex one by global conjugation. Write the vertex maps as
`R1`, `U R2 U^-1`, and `V R3 V^-1`, with `W=V^-1 U`.
For the central image `eta I`, the exact edge equations are

```
U A2=eta^a A1 U,
V B3=eta^b B1 V,
W C2=eta^c C3 W,
U=VW,
(a,b,c)=(-d12,-d13,d23).                         (1)
```

For another nontrivial scalar mark the exponents are multiplied
by its nonzero character exponent. No reduction of the 124
nonzero triples by scalar multiplication is assumed.

Let `T_s e_j=e_(j-s mod5)`. Every invertible solution to the
second and third equations of (1) is uniquely parametrized by
ten invertible `2x2` blocks:

```
V=P_B1 (T_b tensor I2) diag(V0,...,V4) P_B3^-1,
W=P_C3 (T_c tensor I2) diag(W0,...,W4) P_C2^-1.   (2)
```

These formulas hold even when adjacent vertex types differ: the
source and target eigenbases must not be confused. They follow
entry by entry from the distinct fifth roots, leaving arbitrary
isomorphisms between each pair of two-dimensional eigenspaces.

There are forty scalar block entries. Substituting (2), the only
remaining equation is

```
(VW) A2 - eta^a A1 (VW) = 0.                    (3)
```

Its one hundred entries are ordered bilinear polynomials. If
`M=P_B3^-1 P_C3`, the middle expression in eigenbasis coordinates
contains products `V_i M_(ij) W_j`; the `2x2` constant blocks
`M_(ij)` are generally not scalar. This is a second reason why
the scalar/all-A four-generator algebra cannot simply be reused.

Adding one scalar variable `q` and the equation

```
q product_(j=0)^4 det(Vj)det(Wj) - 1 = 0        (4)
```

gives an exact polynomial system in forty-one variables over `k`.
Solutions over `overline(F_19)` correspond exactly to all such
mixed placements. There are no finite-field equations or sampling
restrictions. Although (3) is displayed with one hundred entries,
its residual matrix has only eighty independent linear coordinates:
the kernel of `X -> X A2-eta^a A1 X` has dimension twenty, since
the five matching source/target eigenspace pairs each contribute
four dimensions. Selecting eighty independent linear coordinates
of that map would remove redundant equations without changing
the solution set.

Conversely, a solution of (2)--(4) defines invertible `U=VW` and
three genuine vertex representations satisfying every central
edge relation, hence a representation of the stated triangle.
Its scalar mark is nontrivial. Every entry lies in a finite
extension of `F_19`, so this would be an actual finite detector,
not merely an approximate or infinite-field witness.

## 5. The correct gauge and the failed tempting normalization

Let `D_i=Cent_GL10(R_i(S))`. By Schur's lemma and the distinct
simple summands,

```
D_i = I5 tensor GL2(K) for type A,
D_i = K^* times K^* on the two summands for types B and C.
```

Changing conjugators by `U -> U G2`, `V -> V G3`, with
`Gi in D_i`, leaves their vertex maps unchanged. Simultaneous
conjugation by `G1 in D1` leaves vertex one fixed. Together these
act as

```
U -> G1 U G2, V -> G1 V G3, W -> G3^-1 W G2.      (5)
```

In each ordered edge eigenbasis a `Gi` has five diagonal `2x2`
blocks, denoted `Gi^X(j)`. Equation (5) gives

```
Vj -> G1^B1(j-b) Vj G3^B3(j),
Wj -> (G3^C3(j-c))^-1 Wj G2^C2(j).              (6)
```

These two block descriptions of `G3` come from the same vertex
commutant element. They are not independently selectable.

For type A, choose compatible tensor eigenbases: the same arbitrary
`GL2` matrix appears on all five eigenspaces. For type B, with
eigenbases respecting constituents, the zero-eigenvalue-index block
is `diag(s,t)` on `L0 + L8`, while all four other blocks are
`t I2`. For type C, the blocks are `diag(s,t)` on the three
eigenvalues present in `L2`, and `t I2` on the other two. The
support is read in the selected primitive-root labeling; no fixed
label is assumed if the primitive root changes.

Therefore the all-A normalization `V0=W0=I2` by arbitrary
right multiplicity gauges is not available in mixed cases. The
smaller torus gauges generally cannot turn an arbitrary invertible
edge block into the identity. Such a normalization would silently
discard potential detectors. Equations (2)--(6), without that
normalization, are the exact remaining algebra.

## 6. Outcome and next certificate boundary

The genuine new analytical reductions are global irreducibility,
primitivity, and exclusion of a coprime `2 tensor 5` structure.
They leave primitive tensor-indecomposable placements of the
twenty-six mixed ordered type triples. The supplied exact system
does not assert that any one of these systems is consistent or
inconsistent. No forty-one-variable Groebner search was attempted,
and the optional single MSI pilot remains unused.

A future positive result needs explicit matrices and verification
of the three edge equations. A future exclusion needs a certificate
valid for all placements in its stated type/exponent sector. The
old scalar and stable-isotypic associator certificates do not meet
that boundary for the mixed systems above.

Root review checked the dimension argument, the block permutation
obstruction, the explicit determinant cochain, signs in (1), eigenvalue
shifts in (2), and linked commutant gauges in (6). No repair was needed.
This is internal written review, not Lean or external human certification.

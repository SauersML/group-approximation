# Wave 2 independent audit and the cyclotomic cover of GHB7

2026-09-20. Written mathematical work and a reproduced exact finite
calculation. The hyperbolic residual-finiteness problem remains OPEN.

## 1. The index-seven homology is a cyclotomic module

Let `G=G_HB2(7)`, `chi:G->C_7` send `a,b,c` to one, and `K=ker chi`.
The established orbit calculation gives `b_2(K;Q)=6` and property (T).
There is a little more structure available without a new computation.

On the contractible triangle complex `Y`, the quotient `K\Y` has one vertex
of each type, one edge of each type, and seven faces. Each edge group and
each vertex group maps onto `C_7`, whereas the face stabilizer is trivial.
All face boundaries are the same oriented three-edge cycle. Therefore

```
H_2(K\Y;Q) = {(x_0,...,x_6): sum x_i=0}.
```

Finite stabilizers have zero positive rational homology, so the equivariant
homology spectral sequence identifies this canonically with `H_2(K;Q)`.
The deck quotient `C_7` cyclically permutes the faces, so this identification
is equivariant. Consequently `H^2(K;Q)` is the dual augmentation module,
the irreducible six-dimensional rational representation whose minimal
polynomial is `1+t+...+t^6`. Every nonzero rational cohomology class has
conjugates spanning this entire space, and their sum is zero.

Choose an integral `c in H^2(K;Z)` with nonzero rational image. Such classes
exist by universal coefficients and the established positive second Betti
number. There is also a specified choice with no search: orient all seven
faces by the ordered triangle and label them by the cosets `a^i K`. Let
`omega_0` be the integer two-cochain taking value one on face zero and zero
on the other faces. Pull its cohomology class back along the canonical map
from the Borel construction `E K times_K Y` to `K\Y`. Since `Y` is
contractible, the source computes `H^*(K;Z)`. The resulting integral class
has nonzero rational image: the rational edge map is the isomorphism above,
and `omega_0` evaluates to one on the orbit-cycle `face_0-face_1`.
Denote this specified class by `c_0`. All constructions below work for
every nonzero rational class, and taking `c=c_0` specifies one cover up to
the standard equivalence of extensions. No finite presentation for it or
finite quotient detector is computed here. Let

```
1 -> <z>=Z -> B_c -> K -> 1
```

be its central extension. Its abelianization is finite: the homology
five-term map `H_2(K;Z)->Z` is nonzero and `H_1(K;Z)` is finite. Therefore
`B_c` is Kazhdan by the central-cover property-(T) theorem. No claim about
finite quotient visibility of `z` has been established.

## 2. A rank-six Kazhdan cover of the ambient group

Take coset representatives `t_i=a^i`, `0<=i<7`. Write

```
g t_i = t_(i+chi(g)) h(g,i),   h(g,i) in K.
```

The identity `h(gh,i)=h(g,i+chi(h))h(h,i)` gives the standard monomial
embedding `j:G->K^7 semidirect C_7`. This is injective: if its permutation
and all entries are trivial, its entry at `i=0` is the original element.

Let `T_c` be the inverse image of `j(G)` under
`B_c^7 semidirect C_7 -> K^7 semidirect C_7`. It has kernel `Z^7` over `G`.
The diagonal subgroup `Delta=Z(1,...,1)` is central in `T_c`: the coordinates
are central in `B_c` and the permutation action fixes the diagonal. Define

```
E_c^cyc = T_c/Delta,
A = Z^7/Delta.
```

This is an exact extension of `G` by the free abelian rank-six group `A`,
with conjugation on `A` given by cyclic permutation through `chi`.

Let `L` be the preimage of `K` in `E_c^cyc`. The extension `L->K` is central
by `A`. Before quotienting the diagonal, its seven coordinate extension
classes are the seven conjugates of `c`. The rational transgression

```
H_2(K;Q) -> Q^7 -> A tensor Q
```

has rank six. Indeed, the seven evaluation functionals span the dual by
Section 1. Their sum is zero, so the first map has image the augmentation
subspace. Projection of that subspace to `Q^7/Q(1,...,1)` is an isomorphism.
Thus `A` modulo the image of the integral transgression is finite. The
five-term sequence, together with finite `H_1(K;Z)`, gives finite
`H_1(L;Z)`. All these groups are finitely generated: an extension of a
finitely generated group by a finitely generated kernel is finitely
generated. The central-cover criterion makes `L` Kazhdan, and its index
seven overgroup `E_c^cyc` is also Kazhdan.

This construction does not prove the cover residually finite, linear,
hyperlinear, or nonhyperlinear. In particular it contains `Z^6` and is not
word-hyperbolic.

## 3. All generator lifts have exact order seven

The cyclic permutation `T` has no nonzero fixed vector on `A`. To check
this integrally, if `(T-I)v=k(1,...,1)` in `Z^7`, summing coordinates gives
`7k=0`, hence `k=0`; then `v` is constant and represents zero in `A`.

Let `x` be any lift of `a`, `b`, or `c`. Its seventh power lies in `A`,
because the quotient generator has order seven. Every element commutes
with its own powers; conjugation by `x` acts on `A` as the generator of
the cyclic permutation action. Thus `x^7 in A^T=0`. The lift has exact
order seven because its quotient does.

This is stronger than making the power relators merely small. The
remaining eight relator values lie in the normal abelian kernel `A`.
They commute with each other, but need not commute with the generators.
Wave 1's exact-central-relator rounding theorem does not cover this case.

## 4. How finite visibility would make an actual instability witness

Suppose finite quotients of `B_c` contain images of `z` of orders
`m_n->infinity`. This is the same missing type of premise as the existing
central-survival route, not a consequence of the construction above.

Restrict the regular representation of each finite quotient to the
eigenspace of its central generator for `lambda_n=exp(2 pi i/m_n)`.
This gives genuine `rho_n:B_c->U(d_n)` with `rho_n(z)=lambda_n I`.
On `B_c^7`, take the representation

```
beta_n(b_0,...,b_6)=rho_n(b_0) tensor conjugate(rho_n(b_1)).
```

Induce it to `B_c^7 semidirect C_7`; its dimension is `7d_n^2`.
The diagonal `z` acts trivially, so restriction to `T_c` descends to
a genuine representation `Pi_n` of `E_c^cyc`. On its seven blocks an
element of `A` represented by `v in Z^7` acts by the characters

```
lambda_n^(v_j-v_(j+1)),   j mod 7,
```

up to reversing the common cyclic indexing. Each character is nontrivial
on `A` when `m_n>1`, so `Fix_A(Pi_n)=0`. For every fixed `v`, all these
phases tend to one; indeed the kernel is pointwise almost trivial in
operator norm.

Choose a section `s:G->E_c^cyc` with the specified generator lifts.
The maps `Pi_n o s` are asymptotic representations of `G`. The
Kazhdan-cover criterion already proved in Cairn says that flexible
rounding would force the normalized `A`-fixed dimension to tend to one.
Here it is zero, so no subsequence rounds flexibly.

The three generator matrices have exact seventh powers by Section 3.
Each generator cyclically permutes the same seven blocks. Every defining
relator has permutation part zero and lies in `A`, so its matrix is
block scalar. This supplies the precise noncentral shape left outside
the wave-1 theorem. It does not manufacture the missing finite quotients.

## 5. What does and does not follow from current nonhyperlinear groups

The new nonhyperlinear examples do not imply the finite-visibility premise
for `B_c`. They give no finite quotient of this cover and no estimate on
the orders of its centre in all finite quotients. Liu internality applies
to any resulting Kazhdan matrix model; it is compatible with the
nonroundable projective and induced models, as wave 1 already demonstrated.

If central orders in finite quotients of `B_c` were bounded, their least
common multiple would be some finite `M`. For every prime `p` not dividing
`M`, `B_c/<z^p>` would be a non-residually-finite hyperbolic group, with its
entire central `C_p` invisible in finite quotients. Hyperbolicity follows
from its finite-kernel map onto the hyperbolic subgroup `K`.

Thus the unresolved profinite alternative is sharp: unbounded central
visibility refutes GHB7 stability, while a proved bound produces the
desired counterexample. Neither branch follows merely from existence of
unrelated nonhyperlinear groups. This observation is not a new proof of
either branch.

The earlier artifact `hl-ghb7-central-survival-2026-09-14.md` contains
finite quotient tests at `C_7`, `C_7^2`, `C_7^3`, and a vertex-group
quotient of order 2401. As reported and reread by the coordinating lane,
their cycle pushforward elementary divisors are all one for `C_7` and
`1,1,1,1,7,7` in the other displayed tests. Those finitely many bounded
values provide no unbounded central visibility and no uniform bound
over every finite quotient. They do not choose either alternative above.

**Independent review.** The matching lane checked Sections 1--5 and
returned PASS for the cyclotomic module, coinduced pullback, diagonal
quotient, full-rank transgression and Kazhdan argument, integral fixed-point
calculation, conditional tensor-neighbor models, and bounded-visibility
alternative. The coordinating lane also checked the construction and
proposed pinning `c` by the face-zero cochain as done above. These are
written reviews with the named CCKW, central-cover property-(T), and
Kazhdan-cover rounding criterion retained as explicit dependencies.

## 6. Independent review of the wave-2 matching work

Read `hyperbolic-rf-wave2-matching-2026-09-20.md`, Sections 1--5, and
returned **PASS** for the phase-elimination theorem and scalar-phase
camouflage obstruction. In particular:

- The doubled energy normalization gives scalar-distance bound
  `kappa/(2 sqrt(c))`, and phase projection gives `1/sqrt(2c)`.
- The fixed Hopf identities are evaluated as free-word identities, so
  approximate scalar relators are never promoted to exact characters.
  Their occurrence counts are finite constants, explicitly not computed.
- The stated smallness threshold selects the root near one correctly.
- Applying the same scalar to both generator copies preserves adjoint
  gap, copy defects, and centrality defects exactly.
- The phase-normalized defect is comparable to centrality error, while
  phase correction does not reduce that centrality error.
- The camouflage choice `t=epsilon^(1/(k+1))` makes the raw defect
  asymptotic to `7t`, preserving a positive flexible-rounding obstruction.

Consequently a ratio against raw, unnormalized defect cannot supply the
missing new argument. No full rounding theorem is proved there.

## 7. Independent review and reproduction of the PSL2(19) computation

Read the actual script
`experiments/hrf-wave2-detectors-2026-09-20/psl19_kernel.py` and its outputs.
The explicit three order-five matrices generate the whole `PSL_2(19)`
pairwise, and their link girths are `6,8,6`. The strict hyperbolicity test
was changed to exact fractions after this review noted a float in a
script described as exact; the tested strict inequality was never close
to equality.

The canonical torsion-free kernel's quotient complex has three vertices,
2052 edges and 3420 faces. Deleting one edge of each of two types contracts
a spanning tree. The resulting integral boundary matrix has 2050 rows;
its cokernel is exactly the kernel's integral first homology.

The sparse elimination was checked line by line. A pivot `+1` or `-1`
permits integral column elimination of its row; implicit row clearing of
its column then removes a unimodular direct summand. The adjacency-set
updates preserve all nonzero entries. Deleting a zero column does not
change the image lattice. No modular rank is substituted for integer
lattice surjectivity.

I independently reran the entire script with Python 3.13.13 and
python-flint 0.9.0 in `/tmp/hrf-wave2-py313`. It reproduced the same
matrices, link girths, 1962 unit pivots, and 88-by-1458 residual matrix.
I also separately loaded the saved residual integer matrix and computed
its transpose Hermite normal form: every entry agrees with `[I_88;0]`.
Thus the exact computation does establish `H_1(N;Z)=0` for this specified
kernel, not merely vanishing modulo five.

The proposed consequence is valid. A solvable image of this perfect
kernel is trivial. Moreover the nonzero central `C_5` twist restricts
nontrivially to `N` by the previously proved injectivity theorem. Its
preimage is perfect too: any nonzero abelianization would retract onto
the central `C_5` and thereby split the extension. Hence a finite detector
over the canonical quotient cannot have a solvable kernel. This removes
an actual class of candidate detectors, but does not exclude nonsolvable
refinements or quotients outside the canonical quotient tower.

The same lane then supplied an actual nonsolvable refinement. I read
`wave2-detector-psl19-second-simple-quotient-proof` and independently reran
`psl19_quotient_census.py`. This reproduced the two conjugator pairs in
`PGL_2(19)`, with the nonidentity pair

```
u=[[1,5],[9,17]], v=[[1,14],[12,13]],
```

and shared new edge image `[[1,8],[12,6]]`. The three vertex maps, identity
and conjugations by `u^-1` and `v^-1`, agree on every edge. They give a
second surjection to `Q=PSL_2(19)`. Its product with the canonical map is
onto `Q^2`: the image is subdirect, and the graph-of-an-automorphism
alternative would have to be the diagonal because the two maps agree
identically on the whole first vertex group. The changed third-edge image
rules out that alternative. Thus the first perfect kernel surjects onto
`Q`. This explicit refinement confirms the limitation of the solvable-kernel
exclusion. It is still not a central-twist detector, since `H^2(Q^2;F_5)=0`.
No integral homology of its much larger kernel was computed or inferred.

## 8. Wiring and validation

The two owned `wave2-audit` files were loaded with Cairn's actual parser;
their route schema, required-node references and artifact paths passed.
The initial whole-tree load also reported a malformed ID in a concurrently
written, separately owned node; this was sent to the coordinating lane
rather than repaired by changing another author's files. The coordinating
lane then shortened that ID and updated its references. Cairn's `why`
query derives the cyclotomic-cover claim as ESTABLISHED through the named
dependencies. Neither schema
checking nor the recorded independent proof reviews certify a finite
quotient of the cyclotomic cover. Its visibility remains unresolved.

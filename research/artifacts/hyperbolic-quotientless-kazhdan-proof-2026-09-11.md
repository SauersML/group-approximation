# Hyperbolic finite residuals and Kazhdan groups without finite quotients

Checked 2026-09-11. This artifact proves the equivalence of the following
existence statements:

1. Some word-hyperbolic group is not residually finite.
2. Some infinite word-hyperbolic group has no nontrivial finite quotient.
3. Some infinite word-hyperbolic group with property (T) has no nontrivial
   finite quotient.

It establishes the reductions, without asserting that any of these
existence statements holds. All occurrences of hyperbolicity here mean
word-hyperbolicity. The proof uses the exact literature inputs below and
ordinary free-product and Bass--Serre normal-form facts.

## 1. The geometric input and a tree observation

The reusable input is
`olshanskii-g-subgroup-quotient-theorem`. In the case used here it says:
if `C` is non-elementary hyperbolic with `E(C) = 1`, and finitely many
non-elementary subgroups `L_i` normalize no nontrivial finite subgroup of
`C`, some non-elementary hyperbolic quotient `C -> Q` maps every `L_i`
onto `Q`. This follows from the characterization of G-subgroups and the
simultaneous-surjection theorem. Only these clauses are used; no torsion
conclusion about `Q` is needed.

The original reference is A. Yu. Ol'shanskii, *On residualing homomorphisms
and G-subgroups of hyperbolic groups*, IJAC 3 (1993), 365--409,
[DOI](https://doi.org/10.1142/S0218196793000251), Theorems 1 and 2 and
Proposition 1. The original paper was not accessed in this audit; the exact
statements and attribution were read in A. Minasyan,
[*On residualizing homomorphisms preserving quasiconvexity*](https://arxiv.org/pdf/math/0406126),
pages 2--3, Lemma 1.1 and Theorem 1. The finite-set special case requires
no quasiconvexity or smallness condition on the subgroups `L_i`.

Here is the elementary tree fact that checks the hypotheses. Let `C = B * D`
with both factors nontrivial, and let `T` be its Bass--Serre tree. Its vertices
are cosets of `B` and `D`, and every edge stabilizer is trivial. The action has
no inversions. Every finite subgroup fixes a vertex: the convex hull of a
finite orbit is a finite invariant tree, whose center is fixed (if the center
is an edge, both endpoints are fixed because there are no inversions).

A nontrivial finite subgroup `F` has exactly one fixed vertex. Two fixed
vertices would force `F` to fix the path between them, hence an edge, contrary
to trivial edge stabilizers. Consequently the normalizer `N_C(F)` fixes its
unique fixed vertex, since the fixed set is invariant under the normalizer.
In particular, a subgroup containing a translation of `T` cannot normalize
any nontrivial finite subgroup.

## 2. Turning one undetectable element into a free subgroup

Assume statement 1. Choose a word-hyperbolic group `A` and `a != 1` such
that every homomorphism `A -> F` to a finite group kills `a`. Form six
isomorphic copies `A_i`, with corresponding elements `a_i`, and put

```text
B = A_1 * A_2 * A_3,
D = A_4 * A_5 * A_6,
C = B * D,
h = a_1 a_2 a_3,
k = a_4 a_5 a_6,
L = <h,k> <= C.
```

Finite free products of word-hyperbolic groups are word-hyperbolic: their
Cayley graphs are trees of copies of the factor Cayley graphs, attached at
vertices, and geodesic triangles inherit a uniform thinness bound from the
finitely many factors. Thus `C` is hyperbolic.

The word `h` is cyclically reduced of syllable length three in `B`, so every
positive power has syllable length three times its exponent; hence `h` has
infinite order. The same argument applies to `k` in `D`. Normal form in
`B * D` now identifies `L` with `<h> * <k>`, a free group of rank two.
In particular `C` and `L` are non-elementary. The cyclically reduced word
`hk` has syllable length two in `B * D`; its powers translate along a
bi-infinite edge path of `T`. Thus `L` contains a translation of that tree.

By the tree fact, `L` normalizes no nontrivial finite subgroup of `C`:
`E_C(L) = 1`. Every finite normal subgroup of `C` would in particular be
normalized by `L`, so `E(C) = 1` as well. The conjugation-action indices
in Olshanskii's characterization are both one. Therefore `L` is a
`C`-subgroup.

Every homomorphism `f : C -> F` to a finite group restricts on each `A_i`
to a finite homomorphism. It kills `a_i`, then `h` and `k`, and therefore
all of `L`. This checks that the entire subgroup, not just one chosen
element, lies in the finite residual of `C`.

## 3. Applying the quotient theorem

Apply the geometric input with the single `C`-subgroup `L`. It gives an
epimorphism `p : C -> Q` such that `Q` is non-elementary word-hyperbolic
and `p(L) = Q`. If `u : Q -> F` is any homomorphism to a finite group,
the previous section shows that `u p` kills `L`. Since `p(L) = Q`, the
map `u` is trivial. Non-elementarity implies that `Q` is infinite. This
proves statement 2.

Conversely, every nonidentity element of a group having only trivial finite
homomorphisms is undetectable in finite groups. An infinite such group is
nontrivial, hence is not residually finite. Thus statements 1 and 2 are
equivalent.

This gives an alternative proof of the published Kapovich--Wise theorem,
with Olshanskii's theorem as the explicit small-cancellation input. It is
not a claimed new equivalence. I. Kapovich and D. T. Wise,
[*The equivalence of some residual properties of word-hyperbolic groups*](https://www.researchgate.net/publication/223118363_The_Equivalence_of_some_Residual_Properties_of_Word-Hyperbolic_Groups),
J. Algebra 223 (2000), 562--583, Theorem 1.2, gives this equivalence, with
both nontriviality qualifiers present. The author-uploaded primary paper
was read on the audit date. Its Section 3 instead uses a malnormal
quasiconvex amalgam construction. The same paper's Theorem 5.1 already
gives the residual-finiteness/virtual-torsion-freeness equivalence; using
Osin filling for it is another proof of an established result.

## 4. Adding property (T) while preserving word-hyperbolicity

Assume statement 2 and choose its witness `G_0`. First, `G_0` is
non-elementary. Indeed an infinite elementary hyperbolic group is
virtually infinite cyclic and is residually finite. For completeness, if
`V` contains an infinite cyclic subgroup of finite index, its normal core
`Z_0` is infinite cyclic and normal of finite index. The subgroups
`m Z_0` are characteristic in `Z_0`, normal in `V`, and have finite index
in `V`. The quotients `V/(m Z_0)` separate points of `Z_0`, while `V/Z_0`
separates points outside `Z_0`. Thus `V` is residually finite and cannot
be `G_0`.

Let `E_0` be the maximal finite normal subgroup of `G_0`, and put
`G_1 = G_0/E_0`. Quotienting a finitely generated group by a finite normal
subgroup is a quasi-isometry: with the quotient generating set, a shortest
word for the quotient lifts to within an element of the finite kernel,
whose word lengths are uniformly bounded. Consequently `G_1` is
non-elementary hyperbolic. It is infinite and has no nontrivial finite
quotient. Moreover `E(G_1) = 1`, because the preimage of a finite normal
subgroup would be a finite normal subgroup of `G_0`, already contained
in `E_0`.

Take a torsion-free non-elementary hyperbolic Kazhdan group `K` supplied
by `torsion-free-hyperbolic-kazhdan-partner-exists`. One established source
is a torsion-free subgroup of finite index in a cocompact lattice of
`Sp(2,1)`, as explained in that claim's citation route. Form the
word-hyperbolic free product `H = G_1 * K` and use its Bass--Serre tree.

Suppose a nontrivial finite subgroup `F` is normalized by `G_1`. Its unique
fixed vertex must then be fixed by `G_1`. This factor already fixes its
own vertex, and a nontrivial subgroup cannot fix two vertices because
edge stabilizers are trivial. Therefore `F` fixes that same vertex, so
`F <= G_1`. It is then finite normal in `G_1`, a contradiction. Hence
`E_H(G_1) = 1`. The identical argument for `K` gives `F <= K`, impossible
by torsion-freeness, so `E_H(K) = 1`. A finite normal subgroup of `H`
would be normalized by either factor, so `E(H) = 1`.

Both factors are non-elementary `H`-subgroups by the characterization.
Apply simultaneous surjection to obtain `p : H -> Q` onto a
non-elementary word-hyperbolic group with `p(G_1) = p(K) = Q`. Quotients
of Kazhdan groups are Kazhdan, so `Q` has property (T). Every finite
homomorphism of `Q` pulls back to one of `G_1`, hence is trivial.
Non-elementarity makes `Q` infinite. This proves statement 3.

Finally statement 3 implies statement 2 by forgetting property (T), and
therefore implies statement 1. The three statements are equivalent.

## 5. Certificate boundary

The argument keeps the quotient word-hyperbolic at the precise point where
Olshanskii's theorem is applied. An acylindrically hyperbolic quotient
theorem cannot discharge that step. No claim of simplicity or
torsion-freeness of the final quotient is made. No implication involving
MF approximation is used or established by this artifact.

The small-cancellation theorem and existence of the Kazhdan partner are
literature inputs represented by named Cairn claims. The free-product
construction, finite-radical checks, and all implications between the
three existence assertions are proved above. This is a Cairn mathematical
proof with explicit literature dependencies; it is not a Lean
formalization of those inputs.

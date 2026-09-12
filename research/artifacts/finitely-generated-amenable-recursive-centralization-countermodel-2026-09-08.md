# Recursive centralization with a finitely generated amenable host

2026-09-08. There is a finitely generated amenable group `Gamma` with
a finitely generated subgroup `H`, a stable letter `T`, and an embedded
head group `D=GL_3(F_2)` such that

```text
T H T^-1 <= H,                 [D,T H T^-1]=1.              (1)
```

Every exact finite-dimensional complex unitary representation of
`Gamma` kills `D`, but `Gamma` is operator MF and retains every
nonidentity element of `D` in an injective norm-corona representation.
Thus recursive centralization, even with both groups finitely generated,
cannot by itself supply a uniform norm-matrix obstruction.

This is a comparison for the exact-collapse mechanism in
[the recursive Jacobson candidate](jacobson-shift-exact-collapse-and-monomial-gap-2026-09-08.md).
It is not asserted to satisfy that candidate's full finite boundary
packets or mixed words, and it does not refute positivity of its
unrestricted matrix infimum.

## 1. The ray permutation group and explicit finite generators

Put `r=7` and `X=N_0 x {1,...,r}`. A permutation `p` of `X`
belongs to `H` when, for all sufficiently large `n`, it has the form

```text
p(n,i)=(n+k_i,sigma(i)),
sigma in S_r,                  k_i in Z,
sum_i k_i=0.                                              (2)
```

The eventual data are unique. Composition and inversion preserve this
form, so `H` is a group. The zero sum is also forced by bijectivity:
for a sufficiently large cutoff `N`, the complement of the image of
the tails `n>=N` has size `sum_i(N+k_i)`, while their domain
complement has size `rN`.

The eventual-data homomorphism has kernel exactly the finitary
permutation group `Sym_fin(X)`. Its image is

```text
Z_0^r semidirect S_r,
Z_0^r={k in Z^r:sum_i k_i=0}.                             (3)
```

Here the action is permutation of coordinates; input-index and
output-index conventions give the same semidirect product after
reindexing the translation vector.

There is a concrete finite generating set for `H`. Include the
permutations of the `r` points at level zero, the global permutations
of the `r` rays, and the following `r-1` transfers `a_j`,
`2<=j<=r`:

```text
a_j(n,1)=(n+1,1)                    for n>=0,
a_j(0,j)=(0,1),
a_j(n,j)=(n-1,j)                    for n>=1,
a_j(n,i)=(n,i)                      for i not in {1,j}.
```

Each transfer is a bijection. Its eventual ray permutation is the
identity, and its translation vector is `e_1-e_j`. These vectors
generate `Z_0^r`, while the global ray permutations supply `S_r`.
Thus the displayed generators map onto (3).

They also generate its entire finitary kernel. Let `b_j` be the
head transposition exchanging `(0,1)` and `(0,j)`. Conjugation
by `a_j^n` gives

```text
a_j^n b_j a_j^-n
 =((n,1),(n-1,1))                   when n>=1,
a_j^-m b_j a_j^m
 =((m-1,j),(m,j))                   when m>=1.
```

Together with the head links `b_j`, these are the edge
transpositions of a connected graph on `X`: each ray has every
adjacent edge, and its initial point is connected to the first ray.
Edge transpositions along a finite path generate the transposition
of its endpoints. Every permutation of finite support is a product
of transpositions, so all of `Sym_fin(X)` is generated. For an
arbitrary element of `H`, first match its eventual data by a word
in the displayed generators; the remaining factor is finitary.
This proves finite generation of `H` and surjectivity in (3).

The finitary kernel is locally finite: a finite collection of its
elements is supported on one finite subset and generates a subgroup
of that finite symmetric group. The quotient (3) is virtually
abelian. Hence `H` is amenable, by the elementary closure of
amenability under extensions.

## 2. Unilateral compression and a genuine bilateral stable letter

Let `s:X->X` be the injective map `s(n,i)=(n+1,i)`.
For `p in H`, define a permutation `alpha(p)` by

```text
alpha(p)(0,i)=(0,i),
alpha(p)(n+1,i)=s(p(n,i))            for n>=0.             (4)
```

This is an injective homomorphism. It has the same eventual data
as `p`, so `alpha(H)<=H`. Every element of its image fixes
level zero pointwise. Consequently the head `S_r` centralizes
`alpha(H)`.

To implement this compression by a group element, pass to
`X_Z=Z x {1,...,r}`. Extend every element of `H` by the
identity at negative levels, and set

```text
T(n,i)=(n+1,i)                       for every integer n,
Gamma=<H,T> <= Sym(X_Z).                                 (5)
```

The bilateral shift is a bijection and satisfies
`T p T^-1=alpha(p)`. It therefore realizes (4) by ordinary
conjugation, with no inverse for a unilateral injection being assumed.
Both `H` and `Gamma` are finitely generated.

For completeness, put

```text
H_n=T^-n H T^n,                  n>=0,
N=union_(n>=0) H_n.
```

The subgroups `H_n` are increasing because `alpha(H)<=H`.
Their union is a subgroup normal in `Gamma`: conjugation by `T`
or `T^-1` preserves the union, and it contains `H`. It is
amenable as an increasing union of amenable groups. The quotient
`Gamma/N` is generated by the image of `T` and is infinite
cyclic. Indeed, every element of every `H_n` has positive-tail
translation sum zero, whereas `T^k` has translation sum `rk`.
Thus `T^k` lies in `N` only for `k=0`.

It follows that `Gamma` is an extension of an amenable group by
`Z`, hence amenable. This argument also verifies the concrete
embedding and survival of the head; no abstract embedding theorem
for an ascending presentation is needed.

## 3. The perfect head and the finite-packet splitting

Identify the seven ray labels with the nonzero vectors of `F_2^3`.
The natural permutation action of `G=GL_3(F_2)` on those seven
vectors is faithful: a linear map fixing every nonzero vector fixes
every vector. Let `D=G_Q` be this permutation group acting only
on the seven points at level zero. It is a subgroup of the head
`S_r`, so it satisfies (1).

This finite group is perfect. Elementary row operations generate
`GL_3(F_2)`, and every elementary generator is a commutator

```text
x_ij=[x_ik,x_kj]                    for distinct i,j,k.
```

Its marked involution `w=x_13,Q` is nonidentity in the faithful
head action. Conjugates `T^i D T^-i` act on disjoint levels,
so they commute pairwise and remain nontrivial.

The comparison also has a precise finite head-tail splitting. Let
`g_P` fix level zero and act by the same ray permutation `g`
at every level `n>=1`. It belongs to `H`, being the product
of the global ray permutation with the inverse head permutation.
Then `G_Q` and `G_P` embed `G x G`. Define

```text
tau(g)=T g_Q T^-1,          delta(g)=T g_P T^-1.
```

The first acts only at level one, and the second only at levels
at least two. Hence

```text
g_P=tau(g)delta(g),          [tau(G),delta(G)]=1.           (6)
```

These identities persist at every shift. They reproduce the finite
head-tail split and its stable-letter transport, in addition to (1).
They do not supply a `GL_6(F_2)` packet containing the two head
levels with the prescribed natural linear embeddings, nor the
`GL_5(F_2) x GL_3(F_2)` boundary or the Jacobson mixed words.

## 4. Exact finite-dimensional collapse

Here is a short matrix-algebra proof of the collapse. Let
`pi:Gamma->U(d)` be an exact representation and put

```text
A=span_C pi(H) <= M_d(C).
```

This is a finite-dimensional unital algebra. Equation (1) implies

```text
Ad_(pi(T))(A)<=A.
```

Conjugation is an invertible linear map, so the two finite-dimensional
spaces have equal dimension and this inclusion is equality. The head
image centralizes `pi(alpha(H))`, and hence it centralizes
`Ad_(pi(T))(A)=A`. It also lies in `A`, so `pi(D)` lies
in its abelian center. Perfectness of `D` gives

```text
pi(D)={I},                     pi(w)=I.                  (7)
```

Equivalently, one can apply the elementary commuting-head dimension
argument in the Jacobson exact-collapse artifact. The existing
[commuting-conjugate perfect-group bound](../conjugate-commuting-perfect-copies-force-exponential-dimension.md)
records the more general density-dependent version. No new generic
dimension-growth theorem is asserted here.

## 5. MF models survive despite the exact collapse

By Section 2, `Gamma` is countable and amenable. Apply the existing
literature input
[amenable-implies-operator-mf](../amenable-implies-operator-mf.md).
The primary source is Tikuisis--White--Winter,
[*Quasidiagonality of nuclear C-star algebras*, Corollary C](https://annals.math.princeton.edu/wp-content/uploads/annals-v185-n1-p04-p.pdf):
the reduced C-star algebra of a discrete amenable group is
quasidiagonal. Its proof derives the required UCT hypothesis for
countable amenable groups; it is not an extra assumption on the
group constructed here. The consequence that amenable groups are
MF is also stated directly in Schafhauser,
[*Finite dimensional approximations of certain amalgamated free products of groups*, Theorem 2.3](https://arxiv.org/html/2306.02498#S2).

Thus there is an injective homomorphism of `Gamma` into a norm
matrix corona. It retains `w`, even though (7) holds for every
exact finite-dimensional representation. The retained involution has
operator-norm distance exactly two from the identity.

This rules out a uniform norm conclusion derived only from finite
generation, (1), and the head-tail identities (6). It does not rule
out a conclusion using the additional finite linear packets and mixed
relations of `Theta_shift`. Nor does it assert a positive gap
for those relations or provide a countermodel to them.

The previous
[seven-ray two-braid artifact](jacobson-two-braid-seven-ray-countermodel-2026-09-08.md)
constructs a different amenable linear group: its head has the natural
three-dimensional action over `F_2`, and it verifies two particular
Jacobson braid words. The present comparison instead uses a faithful
seven-point permutation head and proves an explicit finitely generated
base, an internal unilateral compression, its bilateral stable-letter
realization, and exact finite-dimensional collapse alongside MF models.
No additional braid identity is inferred from that earlier construction.

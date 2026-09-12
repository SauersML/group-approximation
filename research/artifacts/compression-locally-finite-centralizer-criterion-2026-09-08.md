# Compression and locally finite centralizers

This note records and audits the argument supplied by the user on
2026-09-08. The proof below explicitly assumes property `(T)` for `L`.
It removes any normality or property-`(T)` assumption on the locally
finite subgroup `C`; it is not a property-`(T)`-free proof of non-MF.
No assertion about every locally finite normal subgroup of a compression
defect follows from this criterion.

All Hilbert--Schmidt norms here are **unnormalized**. A norm without
subscript is operator norm. Group commutators mean `aba^-1 b^-1`;
additive matrix commutators are written as `AB-BA`.

## 1. Statement and corona convention

Let `G` be countable, `L<=G` have property `(T)`, and suppose

```text
u L u^-1 <= L,
C <= C_G(L) is locally finite,
[u C u^-1, ell u C u^-1 ell^-1]=1 for some ell in L.       (1)
```

Then every homomorphism

```text
G -> U(Q_d),   Q_d = product_n M_(d_n)(C) / directSum_n M_(d_n)(C)
```

kills `[C,C]`. The direct sum consists of the norm-null sequences.
Equivalently, every operator-norm asymptotic representation
`V_n:G->U(d_n)` satisfies `||V_n(h)-I||->0` for `h in [C,C]`.
Consequently every homomorphism to an MF group kills `[C,C]`; if `C`
is nonabelian, `G` is not MF. If `C` is perfect, all of `C` is killed.

It suffices to require the commuting relation in (1) separately for
each finite `F<=C`, with `ell=ell_F` allowed to depend on `F`.
Neither version assumes that `C` is normal.

To pass from corona homomorphisms to asymptotic representations,
choose one bounded matrix lift for each group element. Each lift of
a unitary is asymptotically unitary in operator norm; its polar part
is unitary and differs by a norm-null sequence for all sufficiently
large indices. Arbitrary unitary choices at the remaining indices
and the choice `V_n(1)=I` give the required maps. Their multiplicative
defects tend to zero for each fixed pair of group elements.

## 2. The finite-dimensional compression lemma

The property-`(T)` hypothesis is used in the following form. There are
a finite `S subset L` and `kappa>0` such that every unitary
representation `pi` of `L` satisfies

```text
sum_(s in S) ||pi(s)eta-eta||^2 >= kappa^2 ||eta||^2
```

on the orthogonal complement of its invariant vectors.

**Lemma.** Suppose `R_n:G->U(H_n)` are operator-norm asymptotic
representations, with each `H_n` finite-dimensional. If unit vectors
`xi_n` are asymptotically fixed by each element of `L`, the vectors
`R_n(u)xi_n` are also asymptotically fixed by each element of `L`.

Put

```text
A_n=sum_(s in S)(R_n(s)-I)^*(R_n(s)-I),
P_n=1_[0,kappa^2/2](A_n).
```

First,

```text
||A_n P_n|| -> 0,
||(R_n(t)-I)P_n|| -> 0 for every fixed t in L.             (2)
```

Here is the compactness justification, including the uniformity on
the whole range of `P_n`. On any offending subsequence take a free
ultrafilter and the Hilbert ultraproduct of the `H_n`. The maps `R_n`
induce an exact unitary representation since their operator-norm
multiplicative errors vanish. Its operator `A` has spectrum in
`{0} union [kappa^2,infinity)`. Failure of the first assertion of (2)
would give eigenvalues of `A_n` in `[epsilon,kappa^2/2]`. After taking
a further subsequence, their eigenvalues converge and their unit
eigenvectors give a forbidden eigenvector of `A` in that interval.
Failure of the second assertion gives unit vectors in `ran(P_n)`
whose ultraproduct is, by the first assertion, in `ker(A)`. The
Kazhdan inequality says `ker(A)` is the `L`-invariant space, contrary
to the fixed positive displacement at `t`.

The spectral definition also gives, for every vector `eta`,

```text
||(I-P_n)eta||^2 <= (2/kappa^2) sum_(s in S)||(R_n(s)-I)eta||^2. (3)
```

Thus `||(I-P_n)xi_n||->0`. For `s in S`, the element `usu^-1`
belongs to `L`. The asymptotic group relations and (2) therefore give
`||(R_n(s)-I)R_n(u)^*P_n||->0`. Apply (3) uniformly to unit vectors
in `ran(P_n)` to obtain

```text
||(I-P_n)R_n(u)^*P_n|| -> 0.                              (4)
```

For a projection `P` and unitary `U` in finite dimension,

```text
||(I-P)UP|| = ||(I-P)U^*P||.                              (5)
```

Indeed, `B=PUP` is a square matrix on `ran(P)`; the squared norms
in (5) are `||I-B^*B||` and `||I-BB^*||`, respectively. The two
positive matrices have identical eigenvalues. The zero-rank case
is immediate. Applying (5) to (4) reverses the approximate inclusion.
Now `R_n(u)xi_n` is asymptotically in `ran(P_n)`, and (2) proves
the lemma. There is no bound on `dim(H_n)`.

This is precisely the step using property `(T)`. The finite-dimensional
identity (5) by itself gives no uniform low-energy projection for a
general infinite subgroup `L`.

## 3. Correction of a fixed finite group in the same dimension

Let `F` be finite, and `a:F->U(d)` satisfy `a(1)=I` and
`max_(s,t)||a(st)-a(s)a(t)||<=delta`. On `ell^2(F) tensor C^d`
let `lambda` be the left regular representation and define the isometry

```text
(T xi)(x)=|F|^(-1/2) a(x)^* xi.
```

The multiplicative defect gives `||lambda(s)T-Ta(s)||<=delta`.
For example the pointwise inequality follows by multiplying
`a(s)a(s^-1 x)-a(x)` by the relevant unitaries. With `P=TT^*`,
the averaged positive contraction

```text
R=|F|^-1 sum_(s in F) lambda(s)P lambda(s)^*
```

commutes with `lambda(F)` and satisfies `||R-P||<=2delta`.
When `2delta<1/2`, the spectrum of `R` is within `2delta` of
`{0,1}`: the resolvent of `P` and a Neumann series prove this
inclusion. Consequently `Q=1_[1/2,1](R)` satisfies
`||Q-R||<=2delta`, hence `||Q-P||<=4delta`.

For `4delta<1`, the projections have equal rank, since each
projection is injective on the other's range. The map

```text
J=QT(T^*QT)^(-1/2)
```

is an isometry onto `ran(Q)` and `||J-T||->0` as `delta->0`, with
a bound independent of `d`. Since `Q` commutes with `lambda(F)`,
`rho(s)=J^*lambda(s)J` is an exact representation on `C^d`, and

```text
||rho(s)-a(s)|| <= 2||J-T||+delta -> 0.
```

Applied to an asymptotic representation of `F`, this corrects all
sufficiently large indices in their original matrix sizes. At the
finitely many remaining indices any exact representation can be used.

## 4. Support-rank proof of the criterion

Fix finite `F<=C` and put `D=[F,F]`. Correct `V_n|F` by Section 3
to exact `rho_n:F->U(d_n)` with `max_c||rho_n(c)-V_n(c)||->0`.
Define

```text
p_n=I-|D|^-1 sum_(h in D)rho_n(h),  r_n=rank(p_n).
```

The average is the orthogonal projection onto the `D`-fixed space.
Normality of `D` in `F` makes `p_n` commute with `rho_n(F)`; no
normality assumption on `F` or `C` in `G` is used. Suppose `r_n>0`
on an infinite subsequence and restrict to it. For `c in F` set
`T_(c,n)=rho_n(c)p_n`. This is a unitary in the corner with identity
`p_n`, has rank `r_n`, and has HS norm `sqrt(r_n)`.

Since `F` centralizes `L`, for each fixed `s in L` we have
`||V_n(s)T_(c,n)-T_(c,n)V_n(s)||->0`. The additive commutator has
rank at most `2r_n`, so

```text
||V_n(s)T_(c,n)V_n(s)^*-T_(c,n)||_HS / sqrt(r_n)
  <= sqrt(2)||V_n(s)T_(c,n)-T_(c,n)V_n(s)|| -> 0.           (6)
```

In particular, the bound does not contain `sqrt(d_n/r_n)`.
Conjugation `R_n(g)(T)=V_n(g)TV_n(g)^*` acts unitarily on the
finite-dimensional Hilbert space `M_(d_n)` with the unnormalized
HS inner product. Its operator-norm multiplicative error on this
Hilbert space is at most twice the corresponding error of `V_n`.
Apply Section 2 to the unit vectors `T_(c,n)/sqrt(r_n)` and set

```text
a_(c,n)=V_n(u)T_(c,n)V_n(u)^*,
b_(c,n)=V_n(ell)a_(c,n)V_n(ell)^*,
e_n=V_n(u)p_n V_n(u)^*.
```

It follows that

```text
||a_(c,n)-b_(c,n)||_HS=o(sqrt(r_n)).                       (7)
```

The commuting-conjugate assumption implies
`||a_(c,n)b_(d,n)-b_(d,n)a_(c,n)||->0`. To justify its use on these
corners, expand `rho_n(c)p_n` as `rho_n(c)` minus the fixed finite
average of `rho_n(ch)`, `h in D`. Up to norm-null errors, their
conjugates are corresponding combinations of the group lifts at
`ucu^-1`, `uchu^-1` and the second conjugate subgroup. All these
group elements commute across the two families.

The actual additive commutator of the corner operators has rank at
most `2r_n`, since each product has rank at most `r_n`. Hence its HS
norm is `o(sqrt(r_n))`. Combining this with (7) and `||a_(c,n)||<=1`
gives

```text
||a_(c,n)a_(d,n)-a_(d,n)a_(c,n)||_HS=o(sqrt(r_n)).          (8)
```

The map `c -> a_(c,n)` is an exact representation of `F` in the
corner `e_n M_(d_n)e_n`. Multiplying (8) by the appropriate corner
unitaries preserves HS norm and gives the same bound for a group
commutator minus `e_n`. Every element of the fixed finite group `D`
is a fixed finite product of these commutators and their inverses.
Telescoping therefore gives

```text
||a_(h,n)-e_n||_HS=o(sqrt(r_n)) for h in D.                 (9)
```

On the other hand, exactly,

```text
|D|^-1 sum_(h in D) a_(h,n)=0.
```

Averaging (9) yields
`sqrt(r_n)=||e_n||_HS<=|D|^-1 sum_h||e_n-a_(h,n)||_HS=o(sqrt(r_n))`,
a contradiction. Thus `p_n=0` eventually and `V_n(h)->I` in norm
for `h in [F,F]`. Each element of `[C,C]` involves finitely many
commutator factors, contained in a single finite subgroup by local
finiteness. This proves Section 1.

## 5. Ordinary finite lamps

Suppose a countable group `H` acts on `X`, the subgroup `L<=H` has
property `(T)` and fixes `x`, and

```text
uLu^-1<=L,   ell u x != u x for some ell in L.
```

For finite `B`, in the ordinary restricted wreath product
`W=B^(X) semidirect H`, the lamp `B_x` centralizes `L`. Its two
conjugates `B_(ux)` and `B_(ell ux)` commute because their supports
are distinct. If `X` is not countable, restrict each corona map to
the countable subgroup `B^(Hx) semidirect H` before applying Section 1.
Section 1 kills `[B,B]_x` and normality of the kernel
kills all its translates. If the action is transitive and `B` is
perfect, every corona homomorphism kills the whole lamp subgroup.

For `X=H/L`, proper inclusion `uLu^-1<L` provides
`ell in L \ uLu^-1`, and then `ell uL != uL`. One may take
`B=A_5`: three-cycles generate it, and for distinct `i,j,k,r,s`,
the commutator of `(ij)(rs)` and `(jk)(rs)` is a three-cycle on
`{i,j,k}`; reversing the factors gives its inverse. Thus it is
nontrivial and perfect, with no classification theorem needed.

If `X` is infinite and transitive, the lamp subgroup has no
nontrivial finite subgroup normal in `W`: the union of supports of
a finite normal subgroup is a finite invariant subset of `X`.
If `H` has no nontrivial finite normal subgroup, projection to `H`
gives the same conclusion for all finite normal subgroups of `W`.

## 6. Conditional sofic family

Suppose `Lambda` is countable, residually finite, and has property
`(T)`, with a proper finite-index injective endomorphism `phi`.
Let `N` be its ascending direct limit and let `H=N semidirect Z`,
with generator `u` satisfying `uLu^-1=phi(L)<L` for the initial
copy `L=Lambda`. Explicitly, if the direct-limit maps satisfy
`j_(n+1) phi=j_n`, the automorphism is
`bar_phi(j_n(g))=j_n(phi(g))`, with inverse `j_n(g)->j_(n+1)(g)`.
For any nontrivial finite perfect `B`, the group

```text
W=B^(H/L) semidirect H
```

is non-MF by Section 5, and is sofic by the following direct proof.
This is a conditional statement: no concrete arithmetic `Lambda`
or literature assertion establishing its property `(T)` is imported.
The group `W` itself fails property `(T)` because it maps onto `Z`:
pulling back the characters `m->exp(i theta m)` for small nonzero
irrational `theta/(2pi)` gives arbitrarily invariant unit vectors
on every finite set but no invariant vector. This fact about `W`
does not remove the use of property `(T)` for `L` in its non-MF proof.

Write `L_j=u^-j L u^j`. Then `N=union_(j>=0)L_j`, and each `L_j`
is residually finite of finite index in the next. Every `L_j`-orbit
in `H/L` is finite. Indeed, for `h=nu^t`, choose `m` large enough
that `L_m` contains `n`, `L_j`, and `u^tLu^-t`. Both subgroups have
finite index in `L_m`, as does the conjugate by `n` of the second;
their intersection is the stabilizer of `hL` in `L_j`.

Consequently `R_j=B^(H/L) semidirect L_j` is residually finite.
An element with nontrivial `L_j` coordinate is separated in a finite
quotient of `L_j`. A nontrivial lamp is separated by restricting to
a finite orbit `O` meeting its support and using the finite group
`B^O semidirect image(L_j->Sym(O))`. Therefore `R=union_j R_j`
is locally residually finite and `W=R semidirect Z`.

For completeness, write `alpha` for the automorphism of `R`. Given
a finite multiplication test set in `R semidirect_alpha Z`, choose
an integer interval `I` of length `N` much larger than all tested
shifts. Collect every `alpha^-t(r)` needed for the test elements and
products, for all `t in I`. This finite collection is contained in
a residually finite subgroup `R_0`. Choose a finite quotient
`theta:R_0->Q` separating all the nonidentity elements in this
collection. On `I x Q`, viewing `I` as representatives for `Z/NZ`,
put

```text
sigma_(r,m)(j,q)=(t,theta(alpha^-t(r))q),
t = the representative of j+m modulo N in I.
```

These are permutations. Away from the wrap points of the tested
shifts, direct multiplication gives

```text
sigma_(r,m) sigma_(s,n)=sigma_(r alpha^m(s),m+n).
```

For example, with intermediate index `j+n` and final index
`t=j+n+m`, one has `alpha^(-j-n)(s)=alpha^-t(alpha^m(s))`.
The exceptional fraction is `O(1/N)`, with constant depending only
on the finite test set. If `m!=0`, a sufficiently large `N` makes
the shift fixed-point-free. If `m=0` and `r!=1`, the chosen quotient
is nontrivial on `alpha^-j(r)` in every fiber, so left translation
is fixed-point-free. Including the identity and the inverse/product
tests supplies asymptotic separation of distinct elements as well.
Exhausting finite test sets proves soficity.

The finite-index hypothesis is used to obtain the finite `L_j`
orbits; this proof makes no claim about arbitrary actions or arbitrary
amenable kernels.

## 7. Conditional exact radical

In the transitive setting of Section 5 with `B` perfect, suppose
additionally that `H` is residually finite. Then

```text
Rad_MF(W)=B^(X).                                          (10)
```

The lower containment is Section 5. For the reverse, residual
finiteness embeds `H` into a norm matrix corona: enumerate its
nonidentity elements and choose finite quotients separating growing
finite lists, represented by permutation matrices. A nonidentity
permutation unitary moves some basis vector, so its distance to `I`
is at least `sqrt(2)`. Compose this corona embedding with `W->H`.

Define explicitly the intrinsic compression defect

```text
D_G(L)=normalClosure_G { [v c v^-1,t] :
   v in G, vLv^-1<=L, c in C_G(L), t in L }.
```

Under the same hypotheses,

```text
D_W(L)=B^(X).                                            (11)
```

In every finite quotient of `H`, the finite images of `L` and its
conjugate `vLv^-1` have equal cardinality, so their inclusion is
equality. The conjugated centralizer therefore centralizes the
image of `L`. Residual finiteness shows `D_H(L)=1`. Projecting the
displayed generators from `W` to `H` gives the upper containment
in (11).

For the lower containment, let `y=ux`, `z=ell y!=y`. The defect
`[b_y,ell]=b_y b_z^-1` lies in `D_W(L)`. Explicitly,
`[a_y,b_y b_z^-1]=[a,b]_y`, since the two lamp factors commute. Perfectness of
`B`, normality of `D_W(L)`, and transitivity give the whole base.
This assertion is conditional on residual finiteness of `H`; it is
not an assertion that every `H` constructed in Section 6 has it.

## 8. Scope and provenance

The user supplied the argument. This repository transcription adds
the corona convention, the explicit definition of the defect in
Section 7, and a few intermediate calculations; it does not claim
independent discovery or literature novelty. The original supplied
note's statements about what its author read are not verification
claims by this repository audit. No external source is needed for
the conditional implications proved here.

The support-rank estimate handles arbitrary `r_n/d_n`, including
ratios tending to zero, without imposing a rate on multiplicative
errors. It does not remove the Kazhdan spectral projection in
Section 2. Nor do normality and `K<=D_G(L)` alone provide the
commuting-conjugate relation used in Section 4. For abelian `C`,
`[C,C]=1`; this proof asserts no collapse of the nontrivial
one-dimensional characters of an abelian lamp.

Replacing `L` by a finite group does not produce a property-`(T)`-free
nonabelian example of this criterion. For finite `L`, the inclusion
`uLu^-1<=L` is equality, so `uCu^-1` centralizes `L`. Its conjugate
by `ell` is then itself, and the commuting-conjugate hypothesis
forces `C` to be abelian. Finite-group averaging alone therefore
makes the non-MF conclusion vacuous in this specialization.

Verification status: written mathematical audit and Cairn dependency
validation are distinct from a kernel-checked formal proof. The
property-`(T)`-free non-MF existence goal remains open.
Two separate mathematical reviews passed Sections 1--4 and Sections
5--7 respectively. The latter review prompted the countability,
direct-limit convention, and commutator-order clarifications above.

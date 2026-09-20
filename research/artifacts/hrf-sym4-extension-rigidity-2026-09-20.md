# No hidden extensions in the characteristic-19 Sym4 sector

20 September 2026. This is a specialized elementary representation-theoretic
input to the pinned PSL2(19) detector attack, not a solution of hyperbolic
residual finiteness. No computation is used in this proof. The cohomology
vanishing is standard low-weight representation theory; no literature
novelty is claimed.

Let K be any field of characteristic 19, let S=PSL2(F19), and put
V=Sym^4(K^2), with the natural finite SL2 action. Since the degree is
even, the action factors through S. Then

    H^1(S,End_K(V))=0.

Consequently every finite-dimensional K[S]-module with all composition
factors isomorphic to V is a direct sum of copies of V. In particular,
extensions of V by itself do not create additional detector families
beyond stable amplifications of V.

## 1. The low-weight decomposition, in the actual characteristic

Write L_r=Sym^r(K^2), for r=0,2,4,6,8. These modules are absolutely
irreducible for S. Indeed choose h=diag(2,2^-1) in SL2(F19).
The element 2 has order 18 in F19*, and its eigenvalues on the monomial
basis x^(r-i)y^i are 2^(r-2i). They are pairwise distinct because a
nonzero difference of the exponents has absolute value at most 16.
An invariant subspace therefore contains a monomial if nonzero.
The upper unipotent substitution y -> y+x, together with the h-weight
projections, yields x^r from that monomial. The lower unipotent
substitution x -> x+y then yields every monomial: the binomial
coefficients of degree r<19 are nonzero. Thus the subspace is all L_r.
The same proof holds after every field extension.

The alternating form on K^2 identifies the natural module with its dual.
Since 4! is invertible, symmetric tensors and symmetric powers agree,
and this form induces a nondegenerate invariant pairing on V. Hence
End(V) is isomorphic to V tensor V as an S-module.

Here is an explicit Clebsch--Gordan decomposition which does not import
a characteristic-zero formula. Realize V tensor V as the polynomials
bihomogeneous of degrees (4,4) in (x,y) and (X,Y). For j=0,...,4, set
r=8-2j and Delta=xY-yX. The map

    F in L_r |-> Delta^j [t^(4-j)] F(tx+X,ty+Y)

is S-equivariant and lands in bidegree (4,4). It is injective: after
dividing by the nonzero polynomial Delta^j, specialize X=x,Y=y. The
result is binom(8-2j,4-j) F(x,y). The five binomial coefficients are
70,20,6,2,1, none zero in characteristic 19.

The five images are pairwise nonisomorphic simple modules. Their sum is
direct: inductively, any intersection of a new simple image with the
previous direct sum would embed that simple module into a sum of
nonisomorphic simples, impossible after projecting onto the summands.
Their dimensions 9+7+5+3+1 add to 25. Therefore

    End(V) = L_0 direct-sum L_2 direct-sum L_4
             direct-sum L_6 direct-sum L_8.                 (1)

## 2. Restriction to the Sylow group detects H1

Let u=[[1,1],[0,1]] and U=<u>, a Sylow subgroup of S of order 19.
Its index is 180, invertible in K. Restriction

    H^1(S,M) -> H^1(U,M)

is injective for every K[S]-module M. One can prove this without a
cohomology transfer formula. A cocycle c defines the affine action
g*v=g v+c(g). If its restriction to U is a coboundary, U fixes some
point v. The points g*v depend only on the coset gU. Their barycenter,
formed with coefficient 1/180, is fixed by S: the affine action
permutes the 180 points and preserves affine combinations whose
coefficients sum to one. An S-fixed point says c is a coboundary.

Furthermore the image of restriction is invariant under the normalizer
action on H^1(U,M). Explicitly, for h normalizing U,

    h c(h^-1 u h) = c(u) + (u-1)c(h),

so the conjugate restricted cocycle differs by a coboundary.

## 3. The normalizer has no fixed cohomology in these weights

For each L_r in (1), u-1 is nilpotent of index at most r+1<=9.
In characteristic 19 its cyclic norm is

    1+u+...+u^18 = (u-1)^18 = 0.

A cocycle on U is determined by its arbitrary value at u; coboundary
values are (u-1)L_r. Thus

    H^1(U,L_r) = L_r/(u-1)L_r.

The quotient is one-dimensional, represented by y^r. To see this
directly, (u-1)(x^(r-i)y^i) has leading term
i x^(r-i+1)y^(i-1); for i=1,...,r these give rank r, since i is
nonzero in K. The image is the span of all monomials other than y^r.

For h(a)=diag(a,a^-1), conjugation satisfies h(a)^-1 u h(a)=u^(a^-2),
where the exponent is read in F19. Modulo (u-1)L_r, the cocycle value
at u^k is k times the value at u. The normalizer action on this
one-dimensional H^1 is therefore multiplication by

    a^-2 * a^-r = a^(-r-2).                            (2)

For a=2 of order 18, none of r+2=2,4,6,8,10 is divisible by 18.
There are no normalizer-fixed classes. The injective restriction from
Section 2 must have zero image. Hence H^1(S,L_r)=0 for each summand,
and additivity in (1) proves H^1(S,End(V))=0.

All even weights and their normalizer characters factor through PSL2:
replacing a by -a changes neither action. No confusion between the
order-18 diagonal torus in SL2 and its order-9 image is involved.

## 4. From cocycles to all single-type modules

For an extension 0 -> V -> E -> V -> 0, choose a K-linear section.
In the resulting block coordinates the action has matrices

    [[rho(g), beta(g)], [0, rho(g)]].

The map c(g)=beta(g)rho(g)^-1 is a cocycle for the conjugation action
on End(V). The vanishing above supplies a change of section killing
all off-diagonal blocks. Thus Ext^1_(K[S])(V,V)=0.

The same reasoning applies to an extension of V by V^m, since its
cocycle space is a direct sum of m copies of End(V). Induction on a
composition series now proves that every finite-dimensional module
whose factors are all V is semisimple, indeed isomorphic to V^m.

## 5. Detector consequence and exact boundary

Consider any nonzero central five-twist of the pinned triangle of three
copies of S. Suppose a finite-dimensional representation over an
algebraically closed field of characteristic 19 has nontrivial scalar
central mark, and every composition factor of each vertex restriction
is V. The preceding result makes all three vertex restrictions
conjugate to V tensor I_m (the common dimension forces the same m).
Therefore a no-detector theorem for all stable V amplifications also
excludes all these possibly nonsemisimple-looking vertex restrictions.

This implication needs that separate amplified detector theorem; the
single five-dimensional scalar certificate is not enough. Mixed simple
constituents, other characteristics, and other representation types are
not controlled by the argument. No persistent central class or non-RF
hyperbolic group is asserted.

## Literature and review boundary

Repository searches found no existing specialized Sym4 extension lemma.
An external check found the standard classification of first cohomology
for finite SL2 in David A. Craven's
[Maximal PSL2 Subgroups of Exceptional Groups of Lie Type](https://pure-oai.bham.ac.uk/ws/portalfiles/portal/58662428/rank1memoir.pdf),
Memoirs of the AMS 276 (2022), no. 1355, DOI 10.1090/memo/1355
(university-repository copy),
Lemma 7.21: for SL2(p), p odd, the only simple module with nonzero H1
has dimension p-2. Its cited extension classification is Andersen,
Jorgensen and Landrock, Corollary 4.5. This corroborates the low-weight
vanishing, but the specialized elementary proof above is complete and
does not require that classification. Do not confuse rational cohomology
of the algebraic group SL2 with cohomology of the finite group used here.

The general hyperbolic problem was rechecked in Cui--Wan,
[Section 1.2](https://arxiv.org/html/2604.04007v1), on 20 September 2026.
This subsidiary representation calculation does not resolve it.

An independent internal review checked the polarization coefficients,
restriction injectivity for nontrivial coefficients, normalizer weight,
and extension induction. It returned PASS on 20 September 2026.
This is written-proof review, not Lean or external human certification.

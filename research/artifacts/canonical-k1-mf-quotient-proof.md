# Canonical K1 and the complete maximal MF quotient theorem

Fix a countable unital purely infinite simple ring R. Write H=R^x,
C=cornerUnitSubgroup(R), N=Rad_MF(H), and

    K1(R) = (colim_n GL_n(R))/E_infinity(R).

All maps to K1 below are the canonical maps from this construction. The
argument proves the countable-ring instance of the AGP identification
internally, then the base-ring maximal MF quotient theorem at every
positive matrix rank. General Morita invariance is not an input.

The prior-art boundary was checked against Ara--Goodearl--Pardo,
[K0 of purely infinite simple regular rings](https://arxiv.org/abs/math/0111066),
on 2026-09-07. The unit-group abelianization identification is their
classical theorem. The contribution here is closing the repository's
canonical Lean proof and integrating it with its MF classification.

## 1. Previously proved inputs

The full-complementary-idempotent theorem kills every homomorphism from
each elementary group used to define C into any MF group. Therefore C<=N.
The countable abelianization of H is MF, so N<=[H,H].

For every n>=2 the existing matrix theorem proves

    EL_n(R) = [GL_n(R),GL_n(R)] = Rad_MF(GL_n(R)).

For n=0 or n=1 there are no off-diagonal elementary generators, so EL_n
is trivial and still lies in the commutator subgroup. The arbitrary-unit
reduction proved in `MFQuotientUnitsReductionProof.lean` gives, for every
u in H, a unit v and nonzero idempotent e such that

    v = e+(1-e)v(1-e),       uv^(-1) in C.

For clarity, that reduction is an actual finite sequence of operations.
Choose two orthogonal unit corners with coordinate witnesses t_i s_j=delta_ij.
A Peirce column operation makes the first corner coefficient a=t_0us_0
nonzero. Choose p,q with paq=1. With b the coefficient in the next column,
right multiplication by the elementary root of coefficient q(1-pb)
makes the new b satisfy pb=1. A left root of coefficient (1-d)p then
makes the second diagonal coefficient d equal to 1. Upper and lower
Peirce operations clear its row and column, producing v that fixes
e=s_1t_1. Every operation belongs to C; its normality handles both left
and right multiplication. The full entry calculations and membership
proofs are in the cited module and its Peirce dependency.

## 2. Extract a finite stabilized commutator witness

Let G_infinity=colim_n GL_n(R), with canonical inclusions j_n and the
transition maps A |-> diag(A,I). Set

    D_n = j_n([GL_n(R),GL_n(R)]).

These subgroups are increasing: transition homomorphisms take commutators
to commutators and commute with the j_n. Consequently their supremum is
their union. Since EL_n(R)<=[GL_n(R),GL_n(R)] at every n,

    E_infinity(R) <= union_n D_n.

If kappa(u)=1, then j_1(u) belongs to E_infinity, hence equals j_n(B)
for some B in [GL_n(R),GL_n(R)]. Equality in this direct limit means
there is m>=n,1 with

    diag(u,I_(m-1)) = diag(B,I_(m-n)).

The right side is a commutator-subgroup element because stabilization is
a homomorphism. Thus the diagonal stabilization of u belongs to the
commutator subgroup at some finite positive rank. No equality at the
original rank is assumed.

This step is `KappaProof.exists_diagonal_mem_commutator`.

## 3. Compress the witness of a supported unit

Suppose v=e+(1-e)v(1-e), with e a nonzero idempotent, and suppose diag(v,I)
is a commutator-subgroup matrix of size m. We construct a homomorphism
GL_m(R)->H sending that diagonal matrix to v.

Every nonzero idempotent is infinite. To derive this from the repository's
right-ideal definition, take an infinite idempotent p in eR. Then ep=p,
the idempotent pe lies below e and is equivalent to p, and is therefore
infinite. Extending its equivalence by the orthogonal identity e-pe shows
that e is infinite as well. Hence write e=f+g with fg=gf=0, g nonzero,
and f equivalent to e. Normalize the equivalence to obtain a,b in eRe with

    ba=e,       ab=f,       ga=0,       bg=0.

Choose x,y with xgy=1. Pure infiniteness also gives any finite number of
orthogonal copies of the unit; normalize them as S_i,T_i with
T_iS_j=delta_ij. At the distinguished diagonal coordinate l set

    s_l=1-e+a,             t_l=1-e+b,
    s_i=gyS_i (i!=l),      t_i=T_i xg (i!=l).

Then t_l s_l=1 by ba=e and the support identities. The two mixed products
vanish because (1-e+b)g=0 and g(1-e+a)=0. For all other i,j,

    t_i s_j = T_i x g^2 y S_j = T_i(xgy)S_j = delta_ij.

Thus P=sum_i s_i t_i is idempotent and

    theta(A)=sum_(i,j) s_i A_ij t_j

is a unital ring homomorphism M_m(R)->PRP. Extending corner units by the
complementary identity gives a group homomorphism

    Phi(A)=1-P+theta(A): GL_m(R)->H.

The inverse is 1-P+theta(A^(-1)); the cross terms vanish because both
theta-values are supported in P.

The supported form of v implies ev=ve=e, hence av=a and vb=b. Expanding
the two distinguished-coordinate products gives

    s_l t_l=1-e+f,       s_l v t_l=v-e+f.

Every other diagonal entry is 1 and cancels with the corresponding part
of P. Therefore

    Phi(diag_l(v))=1-s_l t_l+s_l v t_l=v.

Homomorphisms carry commutator subgroups into commutator subgroups, so
v is in [H,H]. The compression itself does not require countability.
Its Lean theorem is `KappaProof.supported_mem_commutator`.

## 4. Close the canonical unit kernel

Let kappa(u)=1. Reduce u to supported v as in Section 1. Since
uv^(-1) is in C<=[H,H], and K1 is abelian, kappa(uv^(-1))=1. Therefore
kappa(v)=kappa(u)=1. Sections 2 and 3 show v in [H,H]. Multiplying v by
uv^(-1) now shows u in [H,H].

The reverse inclusion holds for every ring because K1 is abelian. Hence

    ker(kappa)=[H,H].

Surjectivity is already proved internally in `AlgebraicK.kappa_surjective`.
Represent a K1 class by A at finite positive rank, and use single-sandwich
Gaussian elimination to write EAF=diag(u,I) with E,F elementary. Their
K1 classes are trivial, so the class of A is kappa(u). The size-zero case
is the identity. This proves the full `AGPUnitKappa` interface, including
the actual canonical map, without an AGP assumption.

## 5. Intrinsic full radical of the kernel, including rank one

Let f:C->M be any homomorphism with M an MF group. Each defining source
phi:EL_n(S)->H has image in C, so it restricts to a homomorphism into C.
The composite with f is trivial by the full-defect theorem. These images
generate C, and therefore f is trivial. Thus Rad_MF(C)=C as a statement
about homomorphisms defined on C itself.

We already know C<=[H,H]. For the reverse inclusion take u in [H,H] and
reduce it to supported v modulo C. Then v is a commutator because u and
uv^(-1) are. The proved supported-unit step puts v in C; hence u in C.
So C=[H,H] and this group has full MF radical intrinsically. In particular
the result does not rely on extending an arbitrary representation of the
kernel to the ambient unit group.

The Lean theorems are `cornerUnitSubgroup_full_mf_radical`,
`cornerUnitSubgroup_eq_commutator`, and `unit_commutator_full_mf_radical`.

## 6. The canonical map at every positive rank

Let kappa_n:GL_n(R)->K1(R) be the canonical map from the stable construction,
where n>=1. The diagonal identity gives kappa_n(diag(u,I))=kappa(u), so
kappa_n is surjective.

If kappa_n(A)=1, use Gaussian elimination EAF=diag(u,I). Elementary
matrices have trivial K1 class, so kappa(u)=1 and u in [H,H]. The diagonal
homomorphism carries u to a commutator-subgroup matrix. Also E,F lie in
[GL_n(R),GL_n(R)], by Section 1 even when n=1. Therefore

    A=E^(-1) diag(u,I) F^(-1) in [GL_n(R),GL_n(R)].

The reverse inclusion follows from abelianness of K1. Combining with the
already proved all-rank MF kernel equality yields

    ker(kappa_n)=[GL_n(R),GL_n(R)]=Rad_MF(GL_n(R)).

Matrix rings over R are countable purely infinite simple. Applying
Section 5 to M_n(R) shows that this kernel has full MF radical itself,
including at n=1.

Since K1(R) is countable and abelian, it is MF. Any homomorphism
f:GL_n(R)->M to an MF group kills the exact MF kernel, hence factors
through the quotient by ker(kappa_n). The first isomorphism theorem
identifies this quotient with K1(R) through the actual kappa_n. Its
surjectivity makes the factorization unique. The induced isomorphism
sends the class of A to kappa_n(A), as explicitly proved by
`matrixMFQuotientEquiv_mk`.

The closed endpoint `manuscriptCanonicalKOne` packages surjectivity,
the two kernel equalities, intrinsic full radical, MF of K1, and unique
factorization. `manuscriptMFQuotientUnitsKOneAtBaseRing` discharges the
existing printed base-ring interface. The proof does not replace K1(R)
by an unnamed abelian group or by K1(M_n(R)).

## Verification scope

The source files contain ordinary proofs and transitive axiom audits;
the closed manuscript interfaces also reject leading proof inputs.
All three new proof files and their imports passed the targeted Lean run
34169142693, including the closed endpoint and transitive axiom audits.
The root-import check also passed. Exact source hashes, checked commit,
and verification scope are recorded in
[the validation record](canonical-k1-mf-proof-validation.json).
Cairn compilation checks graph integrity; it is not a substitute for that
Lean verification or evidence for the uncountable AGP theorem.

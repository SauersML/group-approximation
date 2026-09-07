# Kaplansky: audit of the missing full-proof implication

Checked 2026-09-07. **No full proof or counterexample was obtained.** This
note checks attempts to close the finite-precision trace argument. It proves
an exact standard reformulation and elementary limitations, without asserting
that the unresolved reformulation holds for arbitrary group algebras.

The [finite-precision artifact](../research/artifacts/kaplansky-finite-precision-trace-2026-09-07.md)
constructs compatible homomorphisms

\[
t_{p,k}:K_0(\mathbb F_p[G])\longrightarrow\mathbb Z/p^k\mathbb Z,
\qquad t_p=\varprojlim_k t_{p,k}.
\]

Every inverse defect has zero value under every one of these maps. Their
construction alone gives no converse. The elementary arguments below are
included in full; no novelty or Lean verification is claimed.

## 1. The exact cancellation assertion

Let R be a unital ring. Let V(R) be the commutative monoid of isomorphism
classes of finitely generated projective right R-modules, with direct sum as
addition. Its Grothendieck group is K_0(R). The following are equivalent:

1. R is stably finite: AB=I_n implies BA=I_n in M_n(R), for every n>=1.
2. For every finitely generated projective right R-module P, [P]=0 in
   K_0(R) implies P=0.
3. For every such P and every n>=1, R^n direct-sum P isomorphic to R^n
   implies P=0.

**Proof that (1) implies (2).** By the defining equivalence relation in
the group completion of a commutative monoid, [P]=0 means that some finitely
generated projective Q satisfies P direct-sum Q isomorphic to Q. Choose a
projective complement Q' with Q direct-sum Q' isomorphic to R^n. Add a free
summand if necessary to arrange n>=1. Adding Q' gives an isomorphism

\[
F:R^n\oplus P\longrightarrow R^n.
\]

Let i:R^n -> R^n direct-sum P be inclusion in the first summand and let
pi be the projection onto that summand. On right-module column vectors put

\[
B=Fi,\qquad A=\pi F^{-1}\quad\text{in }\operatorname{End}_R(R^n)=M_n(R).
\]

Then AB=I_n and BA=F i pi F^{-1}. Stable finiteness gives BA=I_n. Conjugate
by F to get i pi equal to the identity of R^n direct-sum P. On (0,v) with
v in P, this identity says (0,0)=(0,v). Thus P=0.

**Proof that (2) implies (3).** Taking K_0 classes of the given isomorphism
and subtracting [R^n] gives [P]=0, so (2) applies.

**Proof that (3) implies (1).** Suppose AB=I_n and put d=I_n-BA. Direct
multiplication gives d^2=d and dB=0. The explicit mutually inverse maps

\[
R^n\oplus dR^n\longrightarrow R^n,\quad (u,v)\longmapsto Bu+v,
\]
\[
R^n\longrightarrow R^n\oplus dR^n,\quad z\longmapsto (Az,dz)
\]

are inverse because Ad=0, dB=0, AB=I_n, and BA+d=I_n. Thus (3) gives
dR^n=0. The endomorphism d has zero image, hence d=0 and BA=I_n. This
finishes the equivalence.

Consequently the assertion

\[
\forall p\text{ prime},\ \forall G,\ \forall P\in V(\mathbb F_p[G]),
\qquad [P]=0\ \Longrightarrow\ P=0                                      \tag{*}
\]

is exactly stable finiteness over all prime-field group algebras. Together
with the known characteristic-zero theorem, prime-field transfer, and the
global direct/stable equivalence, it is equivalent to the full conjecture.
Those coefficient reductions are [Bradford--Fournier-Facio, Theorem 3.3,
Theorem 3.4 and Corollaries 3.15--3.16](https://link.springer.com/article/10.1007/s00209-024-03589-3).
The repository records the coefficient transfer in
`stable-finiteness-reduces-to-prime-field`.

The proof above proves the **equivalence**, not (*). For a fixed general
ring it addresses stable finiteness, not merely its scalar version. The
global group-algebra equivalence uses the cited additional result.

## 2. All additive projective invariants face the same missing step

For an inverse defect d, the last pair of maps shows

\[
[dR^n]=0\quad\text{in }K_0(R).
\]

Every isomorphism-invariant additive function from finitely generated
projectives to an abelian group factors through K_0(R), by the definition
of group completion. It therefore vanishes on every inverse defect.
Collecting more such invariants does not by itself prove that the defect
module vanishes. One needs a theorem saying that their joint zero value
cannot occur for a nonzero actual projective, or a different argument.

The stronger proposal that the lifted trace is injective on all of K_0 is
false even for a finite group. Set R=F_3[C_2], with generator g. Evaluation
at g=1 and g=-1 gives an isomorphism

\[
R\cong\mathbb F_3\times\mathbb F_3.
\]

Indeed every element is a+bg, and (a+b,a-b) determines a,b since 2 is
invertible. The orthogonal idempotents e_+=(1+g)/2 and e_-=(1-g)/2 map to
(1,0) and (0,1), respectively. A projective module over this product is a
pair of finite-dimensional vector spaces, so V(R)=N^2 and K_0(R)=Z^2.
The class [e_+R]-[e_-R]=(1,-1) is nonzero. But the same formulas lift
e_+ and e_- to idempotents over Z_3[C_2], both with identity coefficient
1/2. Therefore

\[
t_3([e_+R])=t_3([e_-R])=\tfrac12,
\qquad t_3([e_+R]-[e_-R])=0.
\]

This equality holds at every precision, not just in a bounded computation.
It does **not** produce a nonzero actual projective of zero trace: a
nonzero actual projective has dimension pair (a,b) in N^2 and trace
(a+b)/2, a nonzero rational number in Z_3. The virtual difference (1,-1)
must not be confused with an actual projective or an inverse defect.

## 3. A general ring argument cannot supply (*)

For any field k consider T=k<x,y>/(xy-1). On the vector space with basis
v_0,v_1,... let Yv_j=v_(j+1), Xv_0=0 and Xv_(j+1)=v_j. Then XY=I, so
these operators define a representation of T. But (I-YX)v_0=v_0. Thus
d=1-yx is a nonzero idempotent in T, while xy=1.

Section 1 gives a nonzero finitely generated projective dT with [dT]=0
in K_0(T). This is a counterexample to (*) with unrestricted unital rings
in place of group algebras. It is not a group-algebra counterexample.
Any proof of (*) must use a further property of group algebras that
excludes this behavior. Nilpotent lifting and the abstract definition of
K_0 do not provide that property.

## 4. The finite-support and completion attempts

The finite-subgroup detection theorem assumes that all entries of an
idempotent are supported in one **finite subgroup**. Finite support alone
only supplies a finitely generated subgroup, which may be infinite: a
single generator can generate an infinite cyclic group. Consequently that
theorem cannot be applied to every finite-support inverse defect without
a new argument. The sharp cyclic family in the finite-precision artifact
also proves that no single fixed modulus detects all nonzero idempotents.

Polynomial lifting at every modulus gives an idempotent in the inverse
limit of (Z/p^k)[G]. For infinite G, this completion can contain infinite
support. The characteristic-zero theorem for the ordinary group algebra
Q_p[G] does not automatically apply to it. Farrell--Linnell explicitly
identify this support issue in [Section 5, pp. 17--18](https://arxiv.org/pdf/math/0301205).
The repository's `padic-c0-direct-finiteness-equivalence` shows that direct
finiteness of this completion is itself equivalent to the modular question.

Nor does p-adic convergence imply convergence in a complex operator norm.
Already the rational scalars a_N=1/(1+p^N) tend to 1 p-adically, since
v_p(a_N-1)=N, but tend to 0 in the usual real absolute value. A proposed
passage from the p-adic lift to a positive complex trace therefore needs a
separate construction with the required convergence and faithfulness.

## 5. Source and research-state record

The current source search located no general proof. The [February 2026
Kochloukova paper](https://arxiv.org/pdf/2602.19235) still describes the
positive-characteristic problem as open. The [August 2026 Leavitt-unit-group
preprint](https://zenodo.org/records/21840947) reports bounded searches with
no counterexample. Its nonsoficity assertion is not used in any proof here.
The Kourovka problem 21.22 search result was also consulted, but its page
could not be opened; this note does not rely on it for a theorem.

The finite-precision artifact's citation has been corrected to **Daniel
R. Farkas and Zbigniew S. Marciniak**, *Lifting idempotents in group rings*,
J. Pure Appl. Algebra 25(1) (1982), 25--32,
[DOI](https://doi.org/10.1016/0022-4049(82)90093-7).
The author list and pages are confirmed by Farrell--Linnell's bibliography,
reference [13].

This audit is attached to the existing open Leavitt target as context.
No unconditional route to the full conjecture is added. Cairn's graph
validation checks dependency integrity, not the truth of a prose proof.
The missing result remains (*), or another argument that excludes all
nonzero inverse defects in arbitrary positive-characteristic group algebras.

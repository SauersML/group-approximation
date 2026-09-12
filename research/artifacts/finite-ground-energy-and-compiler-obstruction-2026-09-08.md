# Finite zero-energy phases: a stronger surjectivity criterion and an exact compiler obstruction

Date: 2026-09-08. Handwritten mathematical proof; no local code or
computational experiment was run. The positive result imports the
established relative-equality collision theorem and the classical
amenable Myhill theorem. The negative result is a direct calculation.
Neither result settles the unrestricted Gottschalk conjecture, and no
external novelty certificate is asserted.

## 1. Conventions

The alphabet A is finite with vacuum 0. Configurations carry the left
action (h.x)(g)=x(h^(-1)g). A CA tau has finite right memory M,
which we enlarge to contain 1. It fixes 0^G and is injective on the
finite configurations relative to that vacuum.

For a finite P containing 1 and nonnegative e:A^P->R with e(0)=0,
write

    e_g(x)=e((x(gp))_(p in P)),
    B(x)={g:e_g(x)>0},       E(x)=sum_g e_g(x),
    Z_e={x:e_g(x)=0 for every g}.

For finite x, B(x) is contained in supp(x)P^(-1), so E is finite.
When e has a positive value, let delta be its least positive value.

## 2. A support estimate replaces a uniform detection radius

We first prove a useful extension of the earlier token argument.
Suppose, for some finite C and every finite x,

    |supp(x)| <= C E(x),
    E(tau(x)) <= E(x).                               (1)

Then tau conserves E, maps every finite energy sector onto itself,
and is onto A^G. A one-symbol alphabet is immediate; otherwise (1)
ensures that e has a positive value. Equation (1) also makes the
finite zero-energy sector exactly the vacuum.

Fix q>0 and let K=max(1,ceil(Cq)). Every x with E(x)<=q has support
size at most K. Put J_0=P^(-1)P, a finite symmetric set containing 1.
Decompose supp(x) into J_0-connected components C_i. A translated
P-pattern meets at most one component, so

    E(x)=sum_i E(x_(C_i)),

where x_(C_i) is its restriction, with vacuum elsewhere. Each
nonempty x_(C_i) has positive energy by (1). Choose a charged center
b for that restricted configuration and an occupied s in bP. This
center is also charged for x, since its P-pattern cannot meet another
component. Every point of C_i is reachable from s by at most K-1
J_0-steps. Consequently

    supp(x) subset B(x) D_q,
    D_q=P J_0^(K-1)                                  (2)

for every finite x with E(x)<=q. Enlarge D_q symmetrically and include
1 if convenient. Its dependence on q is allowed.

Here is the full interface to the proof in
[pattern-energy-collision-proof-2026-09-08.md](pattern-energy-collision-proof-2026-09-08.md).
List the positive pattern weights w. Choose positive integers v
annihilating every integer relation annihilated by w, by taking a
rational point in the rational annihilator containing w and scaling.
Thus equal real energies imply equal packet counts. The possible
real energies are locally finite, and each q has a well-defined
integer token count N(q).

Induct over these energy levels. The zero sector is fixed. Filled
lower sectors and finite injectivity prohibit an energy drop from q,
so energy is conserved through level q. At this step use the single
radius R=D_q union P for all configurations of energy at most q.
Give each positive-energy center its complete integer packet and its
R-pattern. Equation (2) makes this token encoding injective.

Ordered lists of N(q) such tokens form a finite-control relative-
equality domain: check complete packets and patch consistency, decode
the finite configuration, recompute all charged centers in the
finite list of named positions, and require exact agreement with the
input list. Every positional comparison is g_i^(-1)g_j=s. These are
finite tests because q, N(q), P, and R have been fixed.

Set U=R union RM and J=U^(-1)U. Components of supp(x) for this larger
adjacency have at most K sites, hence finitely many translated types.
Every input R-pattern and output R-pattern sees only one component;
the latter depends on an input RM-pattern. The input and output
token sets therefore decompose componentwise. Each component has
energy at most q, and the conservation already proved through q
gives equal input/output token counts for it.

The finite translation stabilizer of a nonempty component acts
freely on both finite token sets. Equal cardinalities therefore give
an equivariant bijection, chosen once per translated component type.
This supplies finitely many displacement instructions. On ordered
tokens the resulting map is a finite relative-equality program and
is injective: the output list determines tau(x), finite injectivity
determines x, and its chosen token bijection determines the ordering.
The established claim
`relative-equality-piecewise-injections-are-surjective` makes the map
onto. Thus the q sector is filled and the induction continues.

Every finite configuration is attained. Finite configurations are
dense, while the continuous CA image is compact and closed, proving
full surjectivity. The proof needs no common decoration radius for
different q and no unsupported matching assumption for truncated
overlapping pattern energies.

## 3. Nonamenable ground periods imply the support estimate

Suppose there is a nonamenable subgroup H<=G such that

    z(gh)=z(g) for all z in Z_e, g in G, h in H.       (3)

By the finite-set characterization of nonamenability, there are a
finite symmetric S in H and c>0 such that

    |F S minus F| >= c |F|                           (4)

for every finite F in H. We can include 1 in S. The same estimate
holds for finite F in G by decomposing F over left H-cosets and
summing (4).

For s in S the compact cylinder {x:x(1)!=x(s)} is disjoint from Z_e.
The open sets {x:e_d(x)>0}, d in G, cover it. A finite subcover gives
D_s with

    x(1)!=x(s) => e_d(x)>0 for some d in D_s.

After translation, a disagreement x(g)!=x(gs) implies gd in B(x)
for some d in D_s. Therefore

    |{g:x(g)!=x(gs)}| <= |D_s| |B(x)|.                (5)

Put F=supp(x). For each point in FS minus F choose g in F and s in S
with gs that point. Since x(g)!=0=x(gs), it is an s-disagreement.
Consequently (4) and (5) give

    c |supp(x)| <= |FS minus F|
       <= sum_(s in S) |{g:x(g)!=x(gs)}|
       <= (sum_(s in S) |D_s|) |B(x)|
       <= delta^(-1) (sum_(s in S) |D_s|) E(x).       (6)

This is (1)'s required support estimate. For a nontrivial alphabet
the hypotheses force e to have a positive value; otherwise every
configuration would satisfy (3), which fails for an isolated symbol
and a nonidentity element of the nonamenable H. Thus delta is defined.
Combining (6) with energy nonincrease proves the stronger finite-
sector conclusion of Section 2 even when Z_e is infinite.

## 4. Finitely many zero-energy configurations suffice

Assume Z_e is finite. It is invariant under the left G-action.
Let H be the kernel of the permutation action G->Sym(Z_e). Then H
is normal of finite index. If G is nonamenable, H is nonamenable:
amenability passes from a subgroup of finite index to its group.
Every z in Z_e is left H-invariant. Normality gives right H-
invariance as well, because gh=(ghg^(-1))g and ghg^(-1) lies in H.
This proves (3), and Section 3 applies.

If G is amenable, finite-configuration injectivity implies
preinjectivity on A^G. To see this, suppose x and y differ only on
a finite F and tau(x)=tau(y). With memory M, image differences can
occur only on F M^(-1). Copy x and y on the finite set
F M^(-1) M, and set both to zero elsewhere, obtaining finite x',y'.
For output sites in F M^(-1), their entire memories have been copied,
so the two images agree there. Outside F M^(-1), the two input
memories agree because the inputs differ only inside F. Thus
tau(x')=tau(y'). Finite injectivity gives x'=y', and hence x=y.

The Myhill theorem now implies surjectivity. A primary source that
includes this group case without finite-generation restrictions is
Ceccherini-Silberstein and Coornaert,
[The Myhill property for cellular automata on amenable semigroups](https://arxiv.org/abs/1302.5965),
whose main result applies to every cancellative left-amenable
semigroup and finite alphabet. Groups meet its cancellation
hypothesis. We use only preinjectivity implies surjectivity here;
no assertion about finite preimages or energy-sector permutations
in the amenable case is being inserted.

## 5. The finite-phase extension includes an excluded reversible rule

On F_2^2 over Z let s denote (sx)_i=x_(i+1), and set

    tau(a,b)=(a+b,sb),
    c=(1+s)a+b,
    e_i(a,b)=1_(c_i!=0)+1_(b_i!=0).

The inverse of tau is (a,b)->(a+s^(-1)b,s^(-1)b). Moreover

    c(tau(a,b))=(1+s)(a+b)+sb=(1+s)a+b=c(a,b),

while b is shifted. Hence the sum of e_i is conserved on finite
inputs. All e_i vanish exactly when b=0 and a_i=a_(i+1) for all i.
There are precisely two such configurations.

Start with b_0=1 and all other bits zero. At time n, b is occupied
at -n and a is occupied at 0,-1,...,-(n-1). Thus support size is n+1.
Any nonnegative local density with unique simultaneous zero vacuum
would, by compactness and its least positive value, bound support
by constant times its total energy. Nonincrease would make this
orbit's support bounded. Therefore no such singleton-ground density
exists for tau, at any finite range. The finite-ground extension is
strict even when existence of some density, rather than the choice
of one particular density, is considered.

## 6. A different reversible rule defeats every finite-phase energy

Define

    T(a,b)_i=(b_i,a_i+b_i+b_(i+1)).

Its displayed local inverse is

    T^(-1)(c,d)_i=(d_i+c_i+c_(i+1),c_i),

as direct substitution verifies in both orders. It fixes zero.
For a finite track encode x as sum_i x_i z^(-i), so s is
multiplication by z. The matrix of T is

    L=[[0,1],[1,u]],          u=1+z.

Define F_0=0, F_1=1, F_(m+1)=u F_m+F_(m-1) in F_2[u]. Induction
gives, for m>=1,

    L^m=[[F_(m-1),F_m],[F_m,F_(m+1)]].               (7)

Squaring (7), using characteristic two, yields

    F_(2m)=u F_m^2,
    F_(2m-1)=F_m^2+F_(m-1)^2.                       (8)

The first identity implies F_(2^j)=u^(2^j-1). Applying the second
repeatedly gives, for N=2^k with k>=1,

    F_(N-1)(u)=sum_(j=1)^k u^(N-2^j).               (9)

Indeed its first term is F_(N/2)^2=u^(N-2), and the remaining
terms are obtained by squaring the formula at N/2.

Substitute u=1+z. The Frobenius identity gives

    (1+z)^(N-2^j)
       = sum_(l=0)^(2^(k-j)-1) z^(2^j l).           (10)

For 0<r<N, its coefficient is one exactly when 2^j divides r.
Consequently the coefficient f_k(r) of z^r in (9) is

    f_k(r)=v_2(r) mod 2,               0<r<N.        (11)

The coefficient at r=0 is k mod 2 and is not used below.

For any fixed p>=1 write p=2^a q with q odd. If

    r == 2^(a+1) mod 2^(a+2),       0<r< N-p,

then v_2(r)=a+1 and v_2(r+p)=a. Equation (11) shows
f_k(r)!=f_k(r+p). The number of these r is at least

    (N-p)/2^(a+2)-1,                                (12)

which tends to infinity as k grows.

Let x have a=0 and b the delta function at zero. At time n its
second track is F_(n+1)(1+z). Take n=2^k-2. Equations (11)-(12)
then prove that the number of sites where T^n x differs from its
spatial p-shift is unbounded for every p>=1. A second-track
disagreement is already a disagreement of the full two-track symbol.

Suppose a nonnegative finite-range density e with e(0)=0 had finite
Z_e and were nonincreasing for T on finite configurations. The
spatial shift permutes finite Z_e, so some p>=1 fixes every member.
The compact cylinder {y:y_0!=y_(-p)} is disjoint from Z_e. A finite
subcover by positive-energy tests gives a finite D such that

    |{i:y_i!=y_(i-p)}| <= |D| |B(y)|
                           <= |D| E(y)/delta         (13)

for every finite y. Here delta exists because a zero density would
have the infinite full shift as Z_e. Nonincrease makes the right
side at y=T^n x bounded by |D|E(x)/delta. This contradicts (12).
Thus no such density exists at any finite range.

## 7. Exact simulation obstruction and its scope

Let eta:B^Z->B^Z fix its vacuum and have a nonnegative finite-range
density with finite zero set, nonincreasing on all finite inputs.
Suppose iota:(F_2^2)^Z->B^Z is a local, shift-equivariant injective
encoding with iota(0)=0 and

    iota T = eta^k iota,              k>=1.

Pull the target local density back along iota. This is a nonnegative
finite-range source density, vanishing at zero. Its simultaneous
zero locus is iota^(-1)(Z_e), hence finite by injectivity. Locality
and the vacuum condition send finite configurations to finite
configurations, and the intertwining relation makes the pulled-back
total energy nonincreasing. Section 6 rules it out.

The same argument permits a fixed spatial shift composed with eta^k,
since total energy is translation invariant. It also permits fixed
block packing: on block alphabet B^m use the sum of the m original
densities at the positions in one block. This is local and
nonnegative; summing over all blocks is the original total energy,
and its zero locus is the packed original zero locus. Thus packing
does not evade the proof. A local left inverse for iota is sufficient
for injectivity but was never needed separately.

Taking iota(x)=(x,0) excludes stabilization by any fixed finite
collection of passive vacuum tracks. Taking an invertible local
iota excludes vacuum-preserving local conjugacies. No injectivity
of eta on its whole full shift was assumed in this obstruction.

This does not refute conservative universality. In Moreira,
[Universality and Decidability of Number-Conserving Cellular Automata](https://arxiv.org/html/nlin/0306032),
Theorem 4 uses the block code a->(a,-a) and then shifts the numerical
alphabet by q. Each encoded block then has total charge 2q, including
the simulated vacuum block. The simulated vacuum therefore becomes
an infinite positive-charge background. It does not meet the
vacuum-preserving finite-configuration hypothesis above. Subtracting
that background creates signed local charge, so it also does not
supply the nonnegative density asserted impossible here. This is a
precise limitation of that possible reduction, not a denial of its
stated simulation theorem.

## 8. Integration, literature, and endpoint status

Repository searches before writing found the singleton-ground token
theorem, positive on-site charge theorems, and the earlier XOR
observable-rank calculation. They do not prove the finite-ground
extension, the support estimate from common nonamenable periods, or
the all-period wall obstruction of Sections 6-7. The original XOR
rule is reused only for the strictly larger hypothesis class in
Section 5; the obstruction rule T is different.

Focused primary-source searches on 2026-09-08 compared finite ground
phases, local conserved energies, reversibility, and conservative
simulation. Moreira's exact code and the amenable Myhill theorem
were checked directly. The earlier local-energy artifact records
the distinct scope of Pivato, Taati, and Kari--Taati: in particular,
their variational notion of ground configuration must not be
identified without proof with the simultaneous zero locus used here.
This bounded search is not an exhaustive novelty audit.

Phung's March 2026 primary preprint,
[Around Gromov's injectivity lemma and applications to post-injunctive groups](https://arxiv.org/abs/2603.18183),
was checked on 2026-09-08 for current problem context. It concerns
injectivity lemmas and post-surjectivity, and supplies no unrestricted
Gottschalk endpoint for the two statements above.

The positive theorem removes the singleton-ground hypothesis. The
explicit reversible counterexample shows that even this enlarged
finite-phase energy method cannot be manufactured universally by
the local vacuum-preserving simulations specified in Section 7.
No route to the unrestricted root is added. The proof still depends
on an independently justified nonincreasing energy, or on a different
argument outside this energy method.

# Full complementary idempotents: conditional full hyperlinear radical

2026-09-20. Independent algebraic cross-review of the proposed upgrade of
`non_mf_groups_exist.tex`, Theorem `thm:full-defect-ring`. The supplied
`CAIRN_NONHYPERLINEAR_COMPARISON.md`, Sections 2–3, was used as a lead, not
as a proof authority. The matrix identities and normal-generation steps
below were checked directly against the manuscript and ring relations.

## Attribution, inputs, and verdict

**Conditional PASS.** Assuming
`kazhdan-compression-pairs-normalize-all-tracial-models` and the
Ershov–Jaikin-Zapirain property-(T) theorem for elementary groups over
finitely generated associative rings, the full-defect theorem upgrades
from MF targets to hyperlinear targets, in every rank n>=2.

The analytic contribution is **Jihao Liu**, [*Nonhyperlinear groups
exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorems 1.2/6.7 and 1.3/7.4. **Andreas Thom** has priority
for the conditional internality-to-normalization implication; see
[*A conditional construction of a nonhyperlinear group and the
centralizer problem*](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
Theorem 1.2, and Liu's explicit attribution. The elementary compression
cell, fullness-to-two-copies lemma, and rank-two descent are earlier
Cairn/OpenAI manuscript algebra. Their hyperlinear application here is
a conditional synthesis, not a theorem claimed to appear in Liu's paper
and not a replacement proof of his analytic result.

No operator-norm-to-2-norm substitution in the old MF proof is used.
No GL=EL theorem, Leavitt simplicity, completeness relation, field
hypothesis, characteristic restriction, or property (T) of EL_2 is used.

## 1. The universal ring and elementary membership

Let

```
C=Z<s,a,t,b | ts=ba=1, ta=bs=0>,
e=1-st,   G=EL_4(C),   L=diag(EL_3(C),1).
```

This is the two-copy Cohn ring, with NO relation st+ab=1. It is nonzero:
creation and deletion of a leading binary letter act on the free
abelian group on finite binary words and satisfy its relations. It is
finitely generated as a unital associative ring. The EJZ input gives
property (T) for G and L; as discrete property-(T) groups they are
finitely generated. Only these universal groups need property (T).

The relations give e^2=e, es=te=0, ea=a, be=b, and bea=1. In
particular e is full in C, even though e need not equal ab.
Write x_ij(r)=I+r E_ij and [g,h]=ghg^-1h^-1. Define

```
u_i=x_4i(t-1) x_i4(1) x_4i(s-1) x_i4(-t),
u=u_3 u_2 u_1.
```

Multiplication of the two-by-two (i,4) block gives [[s,e],[0,t]]. Thus

```
u = [ s 0 0 e   ]       u^-1 = [ t  0  0   0   ]
    [ 0 s 0 et  ]              [ 0  t  0   0   ]
    [ 0 0 s et^2]              [ 0  0  t   0   ]
    [ 0 0 0 t^3 ]              [ e se s^2e s^3 ].
```

These formulas use only ts=1; the inverse identity telescopes using
`e+set+s^2et^2+s^3t^3=1`. Crucially u is already a product of twelve
elementary matrices over C, not merely an invertible matrix.
For i!=j<=3 and every r in C,
`u x_ij(r)u^-1=x_ij(srt)`, so uLu^-1<=L.

The auxiliary elements are elementary as well:

```
k_+=diag(I_3,1+a t^3)=[x_41(a),x_14(t^3)],
k_-=diag(I_3,1+s^3 b)=[x_41(s^3),x_14(b)],
c  =diag(I_3,1+e t) =[x_41(e),x_14(t)].
```

For example, if yx=0, then
`[x_41(x),x_14(y)]=diag(I_3,1+xy)`. Here t^3a=bs^3=te=0.
All three elements centralize L. Their inverses use 1-minus the
nilpotent term, with no characteristic-two assumption.

## 2. Ambient generation, checked without completeness

The preceding matrices give

```
u k_+ u^-1=x_14(a),
u k_- u^-1=x_41(b),
u c u^-1=x_12(e).
```

For the first identity, the last column of u multiplied by a has only
its first entry nonzero, equal to a, while t^3 times the last row of
u^-1 is (0,0,0,1). For the second, that column multiplied by s^3 is
(0,0,0,1)^T, and b times the last row of u^-1 is (b,0,0,0).
The third is the manuscript's rank-four compression cell: both uc and
x_12(e)u equal u+et E_14. None of these uses e=ab.

Let J=<L,u,k_+,k_->. For EVERY r in C,

```
[x_21(rb),x_14(a)]=x_24(r),
[x_41(b),x_12(ar)]=x_42(r).
```

Commuting these with x_12(1), x_32(1), x_21(1), and x_23(1) gives
all x_i4(r), x_4i(r) for i=1,2,3. Together with the roots already in
L these generate EL_4(C). Therefore G=J. The three extra generators
u,k_+,k_- all conjugate L into itself, so the exact finite-compressor
generation hypothesis of the normalization premise is satisfied.

Merely exhibiting uLu^-1<=L would not establish this hypothesis.

## 3. A killed defect normally generates the universal group

For any homomorphism rho:G->U(M) into any specified tracial matrix
ultraproduct, let D=rho(L)' cap M. The normalization premise says
rho(G) normalizes D. Since c centralizes L, rho(c) belongs to D;
hence rho(ucu^-1) belongs to D and commutes with rho(x_23(1)). Thus

```
rho(d)=1,   d=[ucu^-1,x_23(1)]=x_13(e).
```

Let N be the normal closure of d. Steinberg commutators yield

```
[x_41(b),x_13(e)]=x_43(be) in N,
[x_43(be),x_32(a)]=x_42(bea)=x_42(1) in N.
```

Elementary signed permutations move this unit-coefficient root to
every off-diagonal position, up to sign. Inversion removes the sign.
For distinct i,j,k and arbitrary r, the identity
`[x_ij(1),x_jk(r)]=x_ik(r)` puts every elementary generator in N.
Hence N=G and rho is trivial.

Every homomorphism from G to a hyperlinear target is therefore trivial:
its countable image embeds in a tracial matrix ultraproduct, and the
composite is trivial. Conversely, countable subgroups of such unitary
ultraproducts are hyperlinear, so the two formulations agree here.
The universal group is nontrivial, since C is nonzero, and consequently
is nonhyperlinear. This argument proves a full radical, not merely a
single nondetectable element or a failure of canonical-trace models.

## 4. Fullness supplies the universal map

Let R be a countable nonzero unital associative ring, ts=1, e=1-st,
and `1=sum_(j=0)^(m-1) alpha_j e beta_j`. Since R is nonzero m>=1.
Set

```
v_0=s^m,             w_0=t^m,
v_1=sum_j s^j e beta_j,
w_1=sum_j alpha_j e t^j.
```

The elementary identity `e t^i s^j e=delta_ij e` proves
`w_i v_j=delta_ij`. Indeed the unequal exponents leave a positive
power of s adjacent to e on the left, or of t adjacent to e on the
right, which vanishes. The cross terms w_0v_1 and w_1v_0 vanish since
j<m. Thus there is a unital ring homomorphism C->R sending the two
creation/deletion pairs to these four elements. Injectivity is neither
asserted nor required. No equality v_0w_0+v_1w_1=1 is asserted.

This reuses `full-idempotent-ring-has-properly-infinite-unit`.

## 5. Rank-two transfer and its normal generator

Choose four pairs of length-two words

```
(S_1,S_2,S_3,S_4)=(v_0v_0,v_0v_1,v_1v_0,v_1v_1),
(T_1,T_2,T_3,T_4)=(w_0w_0,w_1w_0,w_0w_1,w_1w_1).
```

Then T_iS_j=delta_ij. With p=sum S_iT_i define
`j(A)=1-p+sum_(i,j) S_i A_ij T_j`. Direct multiplication gives
j(AB)=j(A)j(B), j(I)=1, and injectivity follows from
`T_i j(A) S_j=A_ij`. Thus j embeds GL_4(R) into R^x. Moreover

```
Psi(A)=diag(j(A),1),
Psi(x_ij(r))=diag(1+S_i r T_j,1)
           =[x_12(S_i r),x_21(T_j)]  (i!=j),
```

so Psi restricts to an embedding EL_4(R)->EL_2(R).
The composite EL_4(C)->EL_4(R)->EL_2(R) contains
`D_*=Psi(x_12(1))=diag(1+S_1T_2,1)` in its image. Every homomorphism
from EL_2(R) to a hyperlinear group kills this element by Section 3.

For completeness, its normal-generation proof is target-independent.
Whenever wv=ba=1 and bv=0, put D=diag(1+vb,1). Its normal closure
contains `[D,x_12(ar)]=x_12(vr)` for all r. Set f=1-vw and

```
z=vf+fw+1-f-vfw.
```

The identities fv=wf=0 give z^2=1 and zf=vf. The diagonal matrix
h=diag(z,z) is elementary, by the usual six-transvection identity
for diag(z,z^-1). Since
`h x_12(fr) h^-1=x_12(vfrz)`, the normal closure also contains
x_12(fR). The decomposition `r=vwr+fr` supplies all x_12(r), and an
elementary Weyl matrix supplies all x_21(r). Thus D normally generates
EL_2(R). Apply this with (v,w,a,b)=(S_1,T_1,S_2,T_2).

This is exactly the algebraic content of
`elementary-rank-descent-to-two` and
`properly-infinite-unit-rank-two-normal-generator`, not a new analytic
rank-two assumption. Therefore every hyperlinear image of EL_2(R) is
trivial. For n>=3 every elementary root lies in a two-coordinate
EL_2(R), so every hyperlinear image of EL_n(R) is trivial as well.

## 6. Consequences, exclusions, and verification scope

The theorem applies to every countable simple unital ring which is not
directly finite, since the nonzero defect is then full, and to every
L_k(1,m) with countable field k and m>=2, since a second pair gives
`t_2(1-s_1t_1)s_2=1`. It also makes R^x nonhyperlinear: j embeds the
nontrivial nonhyperlinear EL_4(R) into it. It does NOT say all maps
from R^x are trivial; an arbitrary unit group can have additional
quotients not generated by its elementary subgroup.

Fullness cannot be dropped in this proof. A non-full corner can supply
a nonhyperlinear subgroup without forcing every image of the ambient
elementary group to vanish. Neither a matrix-ring isomorphism M_4(R)=R
nor a completeness relation for the two copies was used.

The warning in `notes/NON_MF_TO_HYPERLINEAR_DIFFERENTIAL_AUDIT.md` remains
valid: the old literal Clifford marked word has a Connes-embeddable
detector. This proof does not claim that every MF-invisible mark is
hyperlinear-invisible, or that arbitrary compressor configurations
normalize commutants. It proves the Kazhdan property and exact
finite-compressor generation for THIS universal Cohn pair before
applying the stronger all-trace normalization premise. The old
operator-norm proof is not being transferred wholesale.

The printed matrix calculations and rank-two lemma were checked here
in ordinary algebra. Existing Lean source interfaces in
`RankFourCompressionCellPrinted.lean` and `RankDescentPrintedLemmas.lean`
were inspected, but no fresh Lean build or transitive axiom audit was
performed for this new hyperlinear statement. This artifact accepts
the conditional algebraic application, not all analytic premises or
every theorem in the supplied comparison report.

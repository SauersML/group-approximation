# Direct internality proof and the strongest Leavitt consequence

2026-09-20. Written downstream proof and structural dependency audit. No Lean
build was run. The validity of Liu's universal internality theorem remains an
explicit hypothesis, and no upstream analytic status is promoted here.

## Attribution and result

The proposed analytic input belongs to **Jihao Liu**,
[*Nonhyperlinear groups exist* (2026-09-20)](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorems 1.2/6.7. His Proposition 3.1 supplies a related uniform expectation
criterion. The alternative normalization argument below uses Liu's Theorem
7.4; Liu credits **Andreas Thom** with priority for the conditional universal
internality-to-normalization argument. Nothing here claims these analytic
results for Cairn.

The Leavitt conclusion is a conditional application of Liu's theorem, not a
theorem stated in his paper. The native finite central-height and generation
arguments are the earlier September 8 Cairn arguments. The new simplification
here is a direct bounded Poincare selection proof and direct expectation
comparison, replacing their intervening heat machinery.

Conditional on Theorem 6.7, the explicit group

```
H = L_(F_2)(1,2)^x
```

is nonhyperlinear. It is the **same** group already known in the repository
to be infinite, simple, and Kazhdan. Adding the separate Khanh finite-
presentation import makes this one finitely presented infinite simple
Kazhdan nonhyperlinear group. No generic simple envelope or finitely
presented envelope is required, and no assertion is made that two different
envelope constructions produce one common witness.

The new direct proof needs neither heat, a group-algebra SOS certificate,
an admissible-time choice, ordinary-sequence rounding, Liu's Proposition
3.1, Liu's normalization theorem, nor the wreath construction. It does need
the full internal commutant, property (T), canonical trace, and the native
finite-algebra central-height argument. Sections 1-3 give the proof.

## 1. Internal canonical ICC Kazhdan models admit scalar-commutant models

**Proposition.** Let G be countable, finitely generated, ICC and Kazhdan.
Suppose pi:G->U(M), for a specified tracial matrix ultraproduct
M=prod_omega(M_(d_n),tr_(d_n)), has regular trace. If

```
C = pi(G)' cap M = [B_n]_omega
```

with unital finite-dimensional star-subalgebras B_n in M_(d_n), then G has
another regular-trace embedding into a tracial matrix ultraproduct whose
full commutant is C1. The ultrafilter can be kept fixed. No exact
finite-dimensional representations are constructed.

Fix a finite generating list s_1,...,s_m and unitary lifts V_(n,s).
Property (T) for conjugation on L2(M) gives a constant c>0 with

```
||x-E_C(x)||_2^2 <= c^(-1) sum_s ||[pi(s),x]||_2^2.       (1)
```

The fixed vectors are L2(C). One way to see this is to apply bounded
functional-calculus truncations to the affiliated operator represented by
an invariant L2 vector: all its bounded truncations commute with pi(G).
Equivalently, the usual mean-ergodic argument for symmetric conjugation
averages identifies this fixed space and its orthogonal projection.

Coordinate expectations onto B_n induce E_C. Indeed their outputs lie in
C, and x_n-E_(B_n)(x_n) is orthogonal to every bounded B_n sequence. They
contract operator norm and L2, so they define the L2 orthogonal projection
in the quotient.

Define the coordinate slack

```
delta_n = sup_(||x||op<=1)
  ( ||x-E_(B_n)x||_2^2 - c^(-1)sum_s||[V_(n,s),x]||_2^2 )_+.
```

Then delta_n ->_omega 0. Otherwise choose contraction witnesses at every
bad coordinate; their class contradicts (1). This is a uniform estimate
over all bounded coordinate matrices, with no claim about arbitrary
L2-normalized vectors whose operator norms diverge.

Also
`sup_(b in U(B_n)) ||[V_(n,s),b]||_2 ->_omega 0` for each s: a sequence
of unitary witnesses would give an element of C not commuting with pi(s).
Haar averaging over U(B_n) and polar completion inside B_n' therefore
produce W_(n,s) in U(B_n') such that

```
gamma_n = max_s ||W_(n,s)-V_(n,s)||_2 ->_omega 0.
```

These corrected tuples retain every full relation and canonical trace by
fixed-word telescoping. For a contraction x, both commutator norms are
at most 2 and their difference is at most 2 gamma_n, so the difference
of their squares is at most 8 gamma_n. Consequently

```
||x-E_(B_n)x||_2^2
 <= c^(-1) sum_s ||[W_(n,s),x]||_2^2 + eta_n,
eta_n = delta_n + 8m c^(-1) gamma_n ->_omega 0.             (2)
```

Represent

```
B_n = direct_sum_i (M_(a_(n,i)) tensor I_(b_(n,i))),
W_(n,s) = direct_sum_i (I_(a_(n,i)) tensor W_(n,i,s)),
lambda_(n,i) = a_(n,i)b_(n,i)/d_n.
```

For each component define

```
Delta_(n,i) = sup_(||x||op<=1)
  ( ||x-tr_(b_(n,i))(x)I||_2^2
       - c^(-1) sum_s ||[W_(n,i,s),x]||_2^2 ).             (3)
```

These suprema are attained and nonnegative because x=0 is allowed. Choose
maximizers independently and put them into the block-diagonal contraction
`direct_sum_i I_(a_i) tensor x_i`. Its expectation onto B_n is blockwise
scalar on the second factor. Equation (2) gives

```
sum_i lambda_(n,i) Delta_(n,i) <= eta_n.                   (4)
```

Every relation's squared defect also averages with lambda_(n,i).
Canonical traces concentrate in the same physical weighting. For g!=1,
choose M distinct conjugates h_j g h_j^-1, possible by ICC, and form
the literal matrix average

```
Z_n = M^(-1) sum_j W_(n,h_j) W_(n,g) W_(n,h_j)^*.
```

Its trace in each component is exactly tr(W_(n,i,g)). Cauchy-Schwarz and
the canonical global trace give

```
lim_omega sum_i lambda_(n,i)|tr(W_(n,i,g))|^2
 <= lim_omega ||Z_n||_2^2 = 1/M.
```

Let M tend to infinity. Enumerate all relation words and all nonidentity
group elements. By countable diagonalization along omega, choose increasing
prefixes J_n,K_n whose lengths tend to infinity along omega and for which
the weighted sum of all corresponding squared relation and trace errors
tends to zero. Together with (4), the weighted mean of

```
Delta_(n,i)
 + sum_(r in J_n)||W_(n,i,r)-I||_2^2
 + sum_(g in K_n)|tr(W_(n,i,g))|^2                         (5)
```

tends to zero. Select a component i_n with cost at most this mean.
Its tuples define a full regular-trace embedding pi_* of G.

For any contraction representative x_n of an element of the full
pi_*(G)-commutant, all commutators in (3) tend to zero along omega and
Delta_(n,i_n)->_omega0. Thus
`||x_n-tr(x_n)I||_2 ->_omega0`. The full commutant is scalar.

Unlike heat selection, (5) needs no squared-time relation penalty. The
uniform bounded Poincare slack itself detects every bounded asymptotic
commutant sequence. The argument does not assert a uniform finite-coordinate
gap on all L2 vectors and therefore does not close the stronger original
`hs-one-level-expander-block-decomposition` claim.

## 2. Native internality gives the central height directly

Use R=L_(F_2)(1,2), H=GL_4(R)=EL_4(R), L=diag(GL_3(R),1),
K=diag(I_3,R^x), and the native compressor u. The earlier audit writes and
checks the actual matrices and their inverses. They satisfy

```
uLu^-1 <= L,
k=diag(I_3,1+et) in K,
y=uku^-1=x_12(e) in L,  y!=1,
H=<L,uKu^-1>,
[y,x_23(1)]=x_13(e)!=1.                                 (6)
```

Let pi be any regular-trace model of H and suppose the native commutant
D=pi(L)' cap M is internal, D=[A_n]_omega. Lift pi(u) by unitaries U_n.
Let E_n=E_(A_n) and F_n=Ad(U_n) E_n Ad(U_n*), inducing E_D and
E_(pi(u)Dpi(u)*), respectively.

The subgroup inclusion in (6) reverses on commutants:

```
D <= pi(u)Dpi(u)*.
```

Hence F E=E in the quotient. Both coordinate compositions are uniformly
bounded in operator norm and L2. Contraction witnesses give directly

```
delta_n=||F_n E_n-E_n||_(infinity->2) ->_omega0.            (7)
```

On the other hand pi(k) belongs to D, so pi(y) belongs to pi(u)Dpi(u)*.
Since pi(y) belongs to the canonical factor pi(L)'' and has trace zero,
E_D(pi(y))=0. To justify the orthogonality, for z in D its expectation
onto pi(L)'' is central and hence scalar. Therefore tau(z* pi(y))=0.
The reverse quotient map (E F-F) sends pi(y) to -pi(y), so coordinate
norm witnesses and contractivity give

```
rho_n=||E_n F_n-F_n||_(infinity->2) ->_omega1.              (8)
```

Equations (7)-(8) meet the finite central-height lemma without introducing
heat. That lemma, proved in the September 8
[central-height artifact](leavitt-central-height-and-coordinate-swap-gap-2026-09-08.md),
uses physical central weights, simple block degrees and balanced overlap
flow. It gives, on an omega-large set, z_n in Z(A_n) with

```
tr(z_n)=0, ||z_n||op<=1, ||z_n||_2>=1/8,
||[U_n,z_n]||_2^2 <= 2 delta_n^2/(1-exp(-1/16)).           (9)
```

The earlier audit rechecked the Haar covariance/support estimates, the
median's positive variance, and stationarity's conversion of absolute
ramp flow to upward flow. All dimensions and multiplicities are allowed.

Let z=[z_n]. Since D=[A_n]_omega, coordinate centrality gives z in Z(D).
It commutes with pi(u) by (9) and with pi(K) because pi(K)<=D. The
generation identity in (6) puts z in C=pi(H)' cap M; C<=D also gives
z in Z(C). Thus an internal native commutant forces a nontrivial center
of the full global commutant.

## 3. Minimal analytic input and the contradiction

The following strictly restricted statement suffices:

```
(I_H) Every regular-trace embedding of H into every specified tracial
      matrix ultraproduct has an internal full commutant in its original
      coordinate dimensions.
```

Assume H hyperlinear. Its canonical model has internal global commutant
by (I_H). H is ICC and Kazhdan, so Section 1 produces a canonical model
with scalar full global commutant. The native subgroup L is isomorphic
to H. Precomposing this selected model with that isomorphism and applying
(I_H) again makes its native L-commutant internal. Section 2 contradicts
scalarity. Hence (I_H) implies H nonhyperlinear.

Liu's Theorem 6.7 implies (I_H), and is stronger: it covers every finitely
generated Kazhdan group and every homomorphism, with no regular-trace
assumption. This restricted hypothesis is not a replacement proof of Liu's
theorem. It identifies exactly how little of its conclusion this application
uses and isolates the remaining analytic work.

The direct proof bypasses the heat interface and Liu Proposition 3.1 as
separate inputs, all heat time schedules and SOS error lists, the
ultrafilter-to-ordinary-sequence conversion, Liu Section 7 normalization,
and the Section 8 wreath construction. It does not bypass Liu's Sections
3-6 proof of internality if that is how (I_H) is to be established.

## 4. A second short proof if normalization is also assumed

The root's proposed shortcut through normalization is valid for this exact
native group. Since K is isomorphic to H, it is finitely generated. Take
finite generators k_1,...,k_r of K. Each centralizes L and thus satisfies
`k_i L k_i^-1=L`; u satisfies the one-sided inclusion in (6). Moreover

```
H=<L,uKu^-1> <= <L,u,k_1,...,k_r> <= H.
```

So H and L form a finitely generated Kazhdan compression pair. The
all-trace normalization claim makes every pi(H) normalize D=pi(L)' cap M.
Since pi(k) is in D, pi(y)=pi(u)pi(k)pi(u)* is in D and commutes with
pi(x_23(1)). Equation (6) forces

```
pi(x_13(e))=1.
```

The nonidentity root x_13(e) is therefore killed in every tracial matrix
ultraproduct homomorphism. No canonical trace, simplicity, component
selection, or central-height lemma is needed for this obstruction. With
the separate simplicity theorem it follows that every such homomorphism
of H is trivial.

This route is shorter on the group side but asks for the additional
normalization theorem. It is an application of Jihao Liu's Theorems 6.7
and 7.4, with Andreas Thom credited for the conditional normalization
mechanism. It is not a proof of normalization from internality here.

## 5. Structural audit: same witness, separate confidence levels

| Needed fact | Exact role | What was checked here |
|---|---|---|
| GL_n(R)=EL_n(R), n>=2 | Identifies H and native L and K; transports (T) | Read `AllRanksElementaryCore.lean` and the rank-two theorem signature in `RefineLoopDischarge.lean`; the transport is explicit, with no residual mathematical hypothesis beyond the actual Leavitt algebra. No full dependency build was run. |
| M_m(R) isomorphic to R | Identifies ranks 1,3,4 and complementary copy | Explicit complete-prefix-code matrix units; the algebraic inverse formulas are checked in the earlier audit. |
| Infinite simplicity of H | Gives ICC for direct selection and later triviality of all representations | Read `RootDetectionBinary.lean`, including final theorem with all hypotheses discharged, and its root-detection description. No `sorry` or `axiom` occurs in the checked simplicity files. This is source inspection, not a transitive axiom audit or a fresh Lean build. |
| Property (T) | Gives the fixed global Poincare constant | Imported Ershov--Jaikin-Zapirain theorem for EL_n of a finitely generated unital ring, n>=3. The concrete ring has four generators; matrix elementary generation and rank hypotheses match. The imported theorem was not reproved here. |
| Native identities (6) | Produces reverse defect and generates the missing roots | Actual 4-by-4 compressor, Leavitt relations and Steinberg commutators checked directly, as recorded in the earlier audit. |
| Finite central-height lemma | Contradicts scalar global commutant | Finite overlap/variance proof rederived in the earlier audit; no representation-repair or finite-dimensional group hypothesis. |
| H finitely presented | Adds finite presentation to the same explicit witness | Separate Khanh preprint, Theorem 6.1. Read the recorded full-source audit; this turn does not certify its spectral-sequence/frame-complex proof or its imported theorems. |

No unsupported established structural node was found in the inspected
interfaces. That does not certify the entire existing proof graph. In
particular the local Lean compiled objects were absent, so theorem
signatures and source inspection must not be reported as a successful
fresh machine check. The finite-presentation import remains an additional
unrefereed-preprint trust input, even though its graph status is established.

The source for finite presentation is Huynh Viet Khanh,
[*General linear and Steinberg groups over the Leavitt algebra L_(F_2)(1,2)*](https://arxiv.org/abs/2609.08428),
Theorem 6.1. Its recorded proof passes through a Steinberg comparison and
Krstic--McCool. Taking rank four, as the recorded audit explains, can avoid
the additional all-ranks refinement input; it does not remove the comparison
proof itself. The small explicit Cairn presentations also use that comparison,
so they are not independent evidence for finite presentation.

## 6. Consequences and honest graph reporting

The highest-impact economical conclusion is this same H with all four
properties: finitely presented, infinite simple, Kazhdan, nonhyperlinear.
Only the last property depends on Liu's analytic input; finite presentation
adds Khanh. Conditional negative approximation claims should not absorb
those extra assumptions into a generic existence statement silently.

Further direct consequences are strict normalized-HS stability through the
existing equivalence, characteristic-two boundary examples through actual
subgroup embeddings, and nonhyperlinearity of any overgroup containing H.
Finite presentation and simplicity of a general tensor host require their
own conditions. Nonhyperlinearity of H does not pass to its subgroup
Thompson V or to an arbitrary quotient of an unrelated containing group.

Cairn's computed ESTABLISHED status means that a graph derivation reaches
empty-premise accepted routes. It is not a confidence score, fresh Lean
build certificate, or external referee judgment. The current schema has no
separate acceptance-confidence axis, and no unrecognized frontmatter keys
should be invented. Until such an axis is deliberately implemented, each
import and audit should state, in ordinary prose: exact cited theorem;
which proof steps were independently rederived; formal-source versus fresh
build status; and remaining external trust inputs. Leave unresolved analytic
claims OPEN, while recording the now-proved conditional implications.

The new direct route and the heat route are alternatives with different
proof burdens. Keeping both makes the simplification reviewable: the direct
route visibly omits heat/SOS premises instead of merely claiming to shorten
the earlier narrative. Counterfactual graph activation remains a dependency
test and must not be described as mathematical verification.

## 7. The normalization proof extends to every coefficient field

The root's proposed extension passes the algebraic audit and is stronger
than merely repeating the characteristic-two boundary corollary. Conditional
on the fully credited Liu/Thom normalization premise, the unit group of
L_k(1,2) is nonhyperlinear for **every field k**. A finitely generated
nonhyperlinear subgroup is already present, even when k is infinite or
uncountable. The following proof explains why finite generation of the
entire coefficient ring is unnecessary.

Write R=L_k(1,2) and use s,t,a,b with ts=ba=1, ta=bs=0, st+ab=1.
The native u and its displayed inverse work over every characteristic.
Likewise k_+=diag(I_3,1+at^3) and k_-=diag(I_3,1+s^3b) are units:
their added terms square to zero, so their inverses are 1 minus those
terms. In characteristic two they are involutions, but involutivity is
not used here.

The accepted all-fields `leavitt-gl-equals-el-and-perfect-unit-group`
theorem gives finite elementary factorizations of u,k_+,k_- in EL_4(R).
Let S be the unital subring of R generated by s,t,a,b and the finitely
many coefficients in these factorizations. It is finitely generated as
a ring, and u,k_+,k_- belong to H_0=EL_4(S). Put L_0=diag(EL_3(S),1).
Ershov--Jaikin-Zapirain gives property (T) for H_0 and L_0. Ring inclusion
embeds H_0 in EL_4(R), hence in R^x through prefix self-similarity.

For every r in S, direct conjugation gives
`u x_ij(r)u^-1=x_ij(srt)` for i,j<=3, so u compresses L_0.
The k_+,k_- centralize L_0. The identities

```
u k_+ u^-1=x_14(a),    u k_- u^-1=x_41(b),
[x_21(rb),x_14(a)]=x_24(r),
[x_41(b),x_12(ar)]=x_42(r)
```

and further elementary commutators give every root of EL_4(S). Therefore
`H_0=<L_0,u,k_+,k_->`, exactly the finite-compressor hypothesis.

Now use k_+ itself as the commuting witness. Normalization of
D=pi(L_0)' cap M puts `pi(x_14(a))=pi(u k_+ u^-1)` in D. It must commute
with pi(x_21(1)). Thus every tracial matrix-ultraproduct homomorphism of
H_0 kills

```
[x_21(1),x_14(a)] = x_24(a) != 1,
```

where nontriviality follows from ba=1. This proves H_0 nonhyperlinear,
and consequently R^x nonhyperlinear.

This choice of witness removes a possible hidden hypothesis in a naive
finite-subring reduction. If one instead retains
k=diag(I_3,1+et), its membership in EL_4(S) is not automatic merely from
GL_4(R)=EL_4(R); its factorization coefficients must also be added to S.
Using k_+ avoids that extra step entirely.

The killed root is off-diagonal and noncentral. Its image in the quotient
of EL_4(R) by its center is nonidentity: it fails to commute with x_12(1),
since the resulting root x_14(a) is nonidentity. Consequently the same
normalization obstruction also rules out an injective matrix-ultraproduct
model of that projective quotient, by composing with H_0. No assertion
that all homomorphisms of the entire R^x are trivial is needed or made.
Other ranks and boundary groups require their actual rank-transport and
corner-embedding maps; they should be wired with those premises explicitly.

Credit remains Jihao Liu's proposed analytic internality/normalization
theorems and Andreas Thom's conditional normalization mechanism. The
all-fields deduction is a Cairn conditional application of those results
and the existing native Leavitt matrices. It is not asserted to appear
as a theorem in Liu's paper. This extension uses normalization and therefore
does not reduce the assumptions of the internality-only characteristic-two
route in Sections 1-3.

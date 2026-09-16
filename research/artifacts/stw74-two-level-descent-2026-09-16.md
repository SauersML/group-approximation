# STW LXXIV: level-two descent, the full-spectrum sphere, and separable subcounterexamples (2026-09-16)

This artifact carries the complete proofs for

- `stw74-lxxiv-hinge-is-two-level-descent` (Theorem A),
- `stw74-two-level-failure-has-full-spectrum-sphere` (Theorem B),
- `stw74-counterexamples-have-separable-subcounterexamples` (Theorem C),

and the justification of the two routes between the open hole
`stw74-hypothesis-forces-property-sp` and the new open hole
`stw74-separable-two-level-projection-descent` (Section 5).

Everything below is elementary C\*-algebra theory.  The only graph inputs are
the established claims `stw74-simple-infinite-projections-are-properly-infinite`,
`stw74-all-stabilized-projections-are-properly-infinite` and (for one
corollary only) `stw74-property-sp-is-the-exact-missing-condition`.

## 0. Conventions

`A` is a unital C\*-algebra.  Projections `p,q` are Murray--von Neumann
equivalent, `p ~ q`, if `p=v*v` and `q=vv*` for some `v`.  A projection `p`
is *infinite* if `p ~ q` for a projection `q<=p`, `q!=p`; it is *properly
infinite* if there are orthogonal projections `e,f<=p` with `e ~ p ~ f`.

A C\*-subalgebra `H` of `A` is *hereditary* if `HAH subset H`.  For
`a in A_+` put

```text
Her(a) = closure(aAa).
```

This is a C\*-subalgebra (`(aXa)(aYa)=a(XaaY)a`, `(aXa)*=aX*a`), it is
hereditary (`(aXa)Z(aYa)=a(XaZaY)a`), and it contains `a^2`, so it is nonzero
when `a!=0`.  If `D` is a hereditary C\*-subalgebra and `0!=d in D_+`, then
`Her(d) subset D` because `dAd subset DAD subset D` and `D` is closed.
Property **(SP)**: every nonzero hereditary C\*-subalgebra contains a
nonzero projection.  By the previous sentence, `A` has (SP) iff `Her(a)`
contains a nonzero projection for every `0!=a in A_+`.

If `H subset A` is hereditary then `M_k(H)` is hereditary in `M_k(A)`,
because every entry of a product `XYZ` with `X,Z in M_k(H)`, `Y in M_k(A)`
is a sum of terms `h y h'` with `h,h' in H`.

An **LXXIV algebra** is a unital simple C\*-algebra in which every nonzero
projection is infinite.

Two standard spectral facts are used without further comment:
`sigma(zw) union {0} = sigma(wz) union {0}` for all `z,w` (for `lambda!=0`,
`(lambda-zw)^(-1)=lambda^(-1)(1+z(lambda-wz)^(-1)w)`), and if
`pi` is a \*-homomorphism and `f` is continuous with `f(0)=0`, then
`pi(f(c))=f(pi(c))` for self-adjoint `c` (true for polynomials without
constant term, hence by uniform approximation on the spectrum).

## 1. Four lemmas

**Lemma 1 (fullness normal form).**  Let `D` be a unital simple C\*-algebra
and `0!=a in D_+`.  There are `k>=1` and `y_1,...,y_k in D` with

```text
sum_i y_i* a^2 y_i = 1_D.
```

Consequently the column `v=(a y_1,...,a y_k)^T in M_(k,1)(D)` satisfies
`v*v=1_D`, and `vv*` is a nonzero projection in `M_k(aDa) subset M_k(Her(a))`.

*Proof.*  `J_0=span{c a d : c,d in D}` is a two-sided ideal whose closure is
a nonzero closed ideal, hence equals `D`.  So some `g in J_0` has
`||1-g||<1`; `g` is invertible and `1=g g^(-1) in J_0`.  Write
`1=sum_(i<=k) c_i a d_i`, i.e. `1=C(a tensor 1_k)Dcol` with row
`C=(c_1,...,c_k)` and column `Dcol=(d_1,...,d_k)^T`.  Then

```text
1 = (C(a tensor 1_k)Dcol)*(C(a tensor 1_k)Dcol)
  = Dcol*(a tensor 1_k)C*C(a tensor 1_k)Dcol
 <= ||C||^2 Dcol*(a^2 tensor 1_k)Dcol = ||C||^2 sum_i d_i* a^2 d_i =: g_1,
```

using `C*C<=||C||^2 1_k` in `M_k(D)` and `X*PX<=X*QX` for `P<=Q`.  Thus
`g_1>=1` is invertible, and `y_i=||C|| d_i g_1^(-1/2)` gives
`sum y_i* a^2 y_i = g_1^(-1/2) g_1 g_1^(-1/2) = 1`.  For `v` as displayed,
`v*v=1`, so `vv*` is a projection and `vv* v=v!=0`; its entries
`a y_i y_j* a` lie in `aDa`.  QED

**Lemma 2 (orthogonal isometries).**  Let `q` be a properly infinite
projection in a C\*-algebra `D`.  For every `n>=1` there are
`t_1,...,t_n in qDq` with `t_i* t_j = delta_ij q`.

*Proof.*  Choose orthogonal `e,f<=q` and `s_1,s_2` with `s_1*s_1=s_2*s_2=q`,
`s_1s_1*=e`, `s_2s_2*=f`.  Then `s_1=e s_1 q`, `s_2=f s_2 q` lie in `qDq`
and `s_1*s_2=s_1* e f s_2=0`.  Put `t_i=s_2^(i-1)s_1` (with `s_2^0=q`).  For
`i<=j`, `t_i*t_j=s_1*(s_2*)^(i-1)s_2^(j-1)s_1=s_1* s_2^(j-i) s_1`, which is
`s_1*s_1=q` if `i=j` and `(s_1*s_2)s_2^(j-i-1)s_1=0` if `i<j`; the case
`i>j` follows by taking adjoints.  QED

**Lemma 3 (corner isomorphism).**  Let `t_1,...,t_n in A` satisfy
`t_i*t_j=delta_ij 1` and put `P=sum t_it_i*`.  Then

```text
Phi: M_n(A) -> PAP,     Phi([c_ij]) = sum_(i,j) t_i c_ij t_j*
```

is a \*-isomorphism, and for every `a in A_+`

```text
Phi(M_n(Her(a))) = Her(b),        b = Phi(a tensor 1_n) = sum_i t_i a t_i*.
```

Applying `Phi` entrywise gives an injective \*-homomorphism
`M_2(M_n(A)) -> M_2(A)` carrying `M_2(M_n(Her(a)))` onto `M_2(Her(b))`.

*Proof.*  `Phi(C)Phi(E)=sum t_i c_ij (t_j* t_l) e_lr t_r* = Phi(CE)` and
`Phi(C)*=Phi(C*)`.  Since `t_k*Phi(C)t_l=c_kl`, `Phi` is injective.  If
`X in PAP` then `X=PXP=sum t_i(t_i*Xt_j)t_j*=Phi([t_i*Xt_j])`, so `Phi` is
onto.  Now `(a tensor 1_n)[c_ij](a tensor 1_n)=[a c_ij a]`, so
`(a tensor 1_n)M_n(A)(a tensor 1_n)=M_n(aAa)`, whose closure is
`M_n(Her(a))`.  Its image is `b PAP b = bAb` (as `Pb=b=bP`), and since an
injective \*-homomorphism is isometric, `Phi(M_n(Her(a)))=closure(bAb)=Her(b)`.
The entrywise statement follows.  QED

**Lemma 4 (a properly infinite projection contains the unit).**  Let `D`
be unital and simple and let `q in D` be a nonzero properly infinite
projection.  There is `w in D` with `w*w=1_D` and `ww* <= q`, `ww* in qDq`.

*Proof.*  Lemma 1 for `a=q` gives `y_1,...,y_k` with `sum y_i* q y_i=1`.
Lemma 2 gives `r_1,...,r_k in qDq` with `r_i*r_j=delta_ij q`.  Put
`w=sum_i r_i q y_i`.  Then `w*w=sum_(i,j) y_i* q r_i* r_j q y_j
=sum_i y_i* q y_i=1`, and `ww*=sum r_i q y_i y_j* q r_j*` lies in `qDq`.
Being a projection in the corner `qDq`, `ww*<=q`.  QED

**Lemma K (left-invertible witnesses are projections).**  Let `H` be a
hereditary C\*-subalgebra of `A` and `z in A` with `zz* in H` and `z*z`
invertible.  Then `q=z(z*z)^(-1)z*` is a nonzero projection in `H`.

*Proof.*  Put `e=z*z` and `h=zz*`.  Clearly `q=q*`, `q^2=z e^(-1) e e^(-1)
z*=q`, and `qz=z!=0`.  With `X=z e^(-2) z*`,

```text
X h = z e^(-2) e z* = q,          h X = z e e^(-2) z* = q,
```

hence `q=q^2=(hX)(Xh)=h X^2 h in HAH subset H`.  QED

**Lemma R (right support).**  Let `H` be hereditary and `z in A` with
`zz* in H`.  Then `zXz* in H` for every `X in A`.

*Proof.*  Put `h=zz*` and `h_n=h(1/n+h)^(-1) in C*(h) subset H`.  Then
`||z-h_n z||^2=||(1-h_n)h(1-h_n)||=sup_(t in sigma(h)) t n^(-2)(1/n+t)^(-2)
<= 1/(4n)`, since `4t/n<=(1/n+t)^2`.  Hence
`zXz*=lim h_n zXz* h_n in closure(HAH) subset H`.  QED

## 2. Theorem A: the hinge is level-two descent

**Theorem A.**  Let `A` be an LXXIV algebra.  The following are equivalent.

1. `A` has (SP).
2. For every hereditary C\*-subalgebra `H` of `A`: if `M_2(H)` contains a
   nonzero projection, then `H` contains a nonzero projection.
3. For every `a in A_+` and all `t_1,t_2 in A` with `t_i*t_j=delta_ij 1`:
   if `Her(t_1 a t_1* + t_2 a t_2*)` contains a nonzero projection, then
   `Her(a)` contains a nonzero projection.
3'. There exist `t_1,t_2 in A` with `t_i*t_j=delta_ij 1` for which the
   implication in (3) holds for every `a in A_+`.

Moreover, if `A` fails (SP), then for **every** pair `t_1,t_2` as in (3)
there is `0!=b in A_+` such that `Her(b)` contains no nonzero projection
while `M_2(Her(b))` does (explicitly, `b=sum_(i<m) w_i a w_i*` below).

*Proof.*

(1)=>(2).  If `M_2(H)` contains a nonzero projection then `H!=0`, and (SP)
gives a nonzero projection in `H`.

(2)=>(3).  Put `b=t_1at_1*+t_2at_2*`.  By Lemma 3 (with `n=2`), `Phi` maps
`M_2(Her(a))` \*-isomorphically onto `Her(b)`.  If `p in Her(b)` is a nonzero
projection, `Phi^(-1)(p)` is a nonzero projection in `M_2(Her(a))`, and
`Her(a)`, a hereditary C\*-subalgebra, contains a nonzero projection by (2).

(3)=>(3').  We need one pair `t_1,t_2`.  `A` is simple, hence nonzero, so `1`
is a nonzero, hence infinite, projection; by the established claim
`stw74-simple-infinite-projections-are-properly-infinite` it is properly
infinite, and Lemma 2 (with `D=A`, `q=1`, `n=2`) produces the pair.

(3')=>(1).  Fix `t_1,t_2` as in (3') and suppose `A` fails (SP).  Choose
`0!=a in A_+` with `Her(a)` projectionless.  By Lemma 1 (with `D=A`) some
`M_k(Her(a))` contains a nonzero projection; let `m` be the least such `k`.
Then `m>=2`.  Put `n=m-1>=1` and `w_i=t_2^(i-1)t_1` for `1<=i<=n`
(`t_2^0=1`).  The computation in the proof of Lemma 2 (with `q=1`, `s_1=t_1`,
`s_2=t_2`; it uses only `s_1*s_1=s_2*s_2=1` and `s_1*s_2=0`) gives
`w_i*w_j=delta_ij 1`.  Let `Phi_n` be the isomorphism of Lemma 3 for
`w_1,...,w_n` and put

```text
b = sum_(i<=n) w_i a w_i*.
```

* `b!=0`, since `w_1* b w_1 = a`.
* `Her(b)` is projectionless: `Phi_n^(-1)` carries a nonzero projection of
  `Her(b)` to a nonzero projection of `M_n(Her(a))`, contradicting `n<m`.
* `M_2(Her(b))` contains a nonzero projection: by the entrywise part of
  Lemma 3, `M_2(Her(b))` is the image of `M_2(M_n(Her(a)))` under an injective
  \*-homomorphism, and `M_2(M_n(Her(a)))` is (block decomposition)
  `M_(2n)(Her(a))`.  Since `2n=2m-2>=m`, the upper-left embedding
  `X -> X (+) 0_(2n-m)` carries a nonzero projection of `M_m(Her(a))` to a
  nonzero projection of `M_(2n)(Her(a))`.

Now let `c=t_1bt_1*+t_2bt_2*`.  By Lemma 3 for the pair `t_1,t_2`,
`Her(c)=Phi_2(M_2(Her(b)))` contains a nonzero projection, so (3') forces a
nonzero projection in `Her(b)`, a contradiction.  Hence `A` has (SP).

The "moreover" statement is the second and third bullet, which used only
that `t_1,t_2` have orthogonal ranges.  QED

*Remarks.*  (i) The stationary-threshold claims already in the graph find
*some* matrix level at which a projectionless corner acquires a projection.
Theorem A shows that one can always re-choose the corner, inside the same
algebra `A`, so that the level is exactly `2`; so the full LXXIV hinge is the
single implication "`M_2(H)` has a projection => `H` has one".
(ii) (Not used below.)  If `M_2(Her(a))` contains a nonzero projection `p`,
then `p` is properly infinite (Section 3(a)), so Lemma 4 in `M_2(A)` gives
`1_A tensor e_11 <~ p <~ a (+) a`; in Cuntz-semigroup notation the hypothesis
of (2) for `H=Her(a)` forces `[1] <= 2[a]`, and the conclusion wanted is a
projection in `Her(a)`.

## 3. Theorem B: a level-two failure carries a full-spectrum sphere

**Theorem B.**  Let `A` be an LXXIV algebra, let `H` be a hereditary
C\*-subalgebra of `A` containing no nonzero projection, and suppose `M_2(H)`
contains a nonzero projection `p`.

(a) There are `x,y in A` with `x*x+y*y=1` and `xx*, xy*, yx*, yy* in H`.

(b) For a unit vector `xi=(xi_1,xi_2) in C^2` put
`z_xi = conj(xi_1) x + conj(xi_2) y`, `b_xi=z_xi z_xi*` and
`e_xi=z_xi* z_xi`.  Then `b_xi in H`, `e_xi+e_eta=1` whenever `xi,eta` are
orthonormal, and `sigma(e_xi)=sigma(b_xi)=[0,1]`; in particular
`||b_xi||=1`.

(c) For every unit vector `xi`, `Her_A(e_xi)` contains no nonzero
projection.  In particular `Her(e)` and `Her(1-e)` are both projectionless
for `e=e_(1,0)=x*x`.

**Corollary B' (unit-splitting dichotomy).**  An LXXIV algebra `A` has (SP)
if and only if for every positive contraction `e in A` at least one of
`Her(e)`, `Her(1-e)` contains a nonzero projection.

### Proof of (a)

`M_2(A)` is simple: if `J` is a nonzero closed ideal and `X in J`, then
`e_(1i) X e_(j1) = X_ij tensor e_11 in J`, so the entries of elements of `J`
lie in `I={c in A: c tensor e_11 in J}`, a closed two-sided ideal of `A`
(`(d tensor e_11)(c tensor e_11)(d' tensor e_11)=dcd' tensor e_11`).  As
`J!=0`, `I!=0`, so `I=A`, `1 tensor e_11 in J` and
`1=e_11+e_21 e_11 e_12 in J`.

By `stw74-all-stabilized-projections-are-properly-infinite`, `p` is properly
infinite in `A tensor K`; the witnesses (orthogonal `e,f<=p` and partial
isometries `s` with `s*s=p`, `ss* in {e,f}`) satisfy `s=ss*sp` and lie in
`p(A tensor K)p = pM_2(A)p` (view `M_2(A)` as the corner cut down by
`1 tensor (e_11+e_22)`), so `p` is properly infinite in `M_2(A)`.  Lemma 4 in
`D=M_2(A)` gives `u in M_2(A)` with `u*u=1_2` and `uu*<=p`; hence `(1-p)u=0`,
i.e. `u=pu`.  Put `v=u epsilon_1`, where `epsilon_1=(1,0)^T in M_(2,1)(A)`.
Then `v*v=epsilon_1* epsilon_1=1_A` and

```text
vv* = p (u e_11 u*) p in p M_2(A) p subset M_2(H),
```

because `M_2(H)` is hereditary in `M_2(A)` and `p in M_2(H)`.  Writing
`v=(x,y)^T`, `v*v=x*x+y*y` and `vv*=[[xx*, xy*],[yx*, yy*]]`.  QED(a)

### Proof of (b)

Let `xi* = (conj(xi_1), conj(xi_2))` be the row, so `z_xi = xi* v` and
`e_xi = v* (xi xi*) v`, `b_xi = xi* (vv*) xi = sum_(i,j) conj(xi_i) xi_j
(vv*)_ij in H`.  If `xi,eta` are orthonormal then `xi xi* + eta eta* = 1_2`, so
`e_xi+e_eta = v*v = 1`.  Also `0 <= e_xi <= v*v = 1`.

*`e_xi` is not invertible:* otherwise Lemma K (with `z=z_xi`, `zz*=b_xi in H`)
gives a nonzero projection in `H`.  So `0 in sigma(e_xi)`; applying this to
`eta` and using `e_eta=1-e_xi` gives `1 in sigma(e_xi)`.  Since
`sigma(b_xi) union {0} = sigma(e_xi) union {0}`, also `1 in sigma(b_xi)`.

*No gaps:* suppose `lambda in (0,1)` is not in `sigma(e_xi)`.  The spectrum is
closed, so there is `epsilon>0` with `[lambda-epsilon,lambda+epsilon]`
disjoint from `sigma(e_xi) union {0} = sigma(b_xi) union {0}`.  Let `f` be
continuous on `R`, `f=0` on `(-inf,lambda-epsilon]` and `f=1` on
`[lambda+epsilon,inf)`.  Then `f` takes only the values `0,1` on
`sigma(b_xi)`, and `f(0)=0`, so `f(b_xi)` is a projection in the non-unital
C\*-algebra generated by `b_xi`, which lies in `H`; it is nonzero because
`f(1)=1` and `1 in sigma(b_xi)`.  This contradicts the hypothesis on `H`.
Hence `sigma(e_xi) superset (0,1)`, so `sigma(e_xi)=[0,1]`; and
`sigma(b_xi) union {0}=[0,1]` with `sigma(b_xi)` closed gives
`sigma(b_xi)=[0,1]`.  QED(b)

### Proof of (c)

Fix `xi`; write `z=z_xi`, `e=e_xi`.  Note `e in Her(e)` (it is the square
root of `e^2 = e1e`).  Suppose `r in Her(e)` is a nonzero projection.  By
the LXXIV hypothesis and `stw74-simple-infinite-projections-are-properly-infinite`,
`r` is properly infinite, and Lemma 4 (with `D=A`, `q=r`) gives `w in A` with
`w*w=1` and `ww*<=r`, so `rw=w`.

Let `f_n(t)=min(1,nt)` and `g_n=f_n(e) in C*(e) subset Her(e)`; `0<=g_n<=1`
and `g_n <= n e`.  For `X in A`,
`||(1-g_n) eXe|| <= ||(1-g_n)e|| ||X|| ||e|| <= ||X||/n`, since
`sup_(0<=t<=1) (1-min(1,nt)) t <= 1/n`.  As `||1-g_n||<=1`, a
`3`-term estimate extends `||(1-g_n)h|| -> 0` from `eAe` to its closure
`Her(e)`.  Hence `||r - g_n r|| -> 0` and so `||r - r g_n r|| -> 0`.  Now

```text
|| w* g_n w - 1 || = || w* (r g_n r - r) w || <= || r g_n r - r || -> 0,
```

using `w=rw` and `w*rw=w*w=1`.  Choose `n` with `||w*g_n w-1||<1/2`; then
`w*g_n w >= 1/2`, and `w* e w >= n^(-1) w* g_n w >= 1/(2n)`, so `w*ew` is
invertible.

Put `z'=zw`.  Then `z'*z'=w*z*zw=w*ew` is invertible and
`z'z'*=z(ww*)z* in H` by Lemma R (as `zz*=b_xi in H`).  Lemma K gives a
nonzero projection in `H`, a contradiction.  QED(c)

### Proof of Corollary B'

If `A` has (SP) and `e` is a positive contraction: when `e!=0`, `Her(e)` is
nonzero and contains a projection; when `e=0`, `Her(1-e)=A` contains `1`.
Conversely, if `A` fails (SP), Theorem A ("moreover") gives `0!=b in A_+`
with `H=Her(b)` projectionless and `M_2(H)` containing a nonzero projection;
(c) applied to `xi=(1,0)` and `eta=(0,1)` gives the positive contraction
`e=x*x` with `1-e=y*y`, and `Her(e)`, `Her(1-e)` both projectionless.  QED

*Remarks.*  (i) Theorem B complements the gapless-compression claims already
in the graph (`stw74-projectionless-corner-forces-gapless-compressions`,
`stw74-minimal-projection-has-uniform-gapless-compressions`), which concern
scalar compressions of a given projection over a projectionless corner and
give accumulation of the spectrum at `0` and a uniform norm floor `delta`.
The connectedness part of (b) is the elementary fact that a positive element
of a projectionless C\*-algebra has spectrum `[0,||b||]`; what is new in (b)
is the exact norm `||b_xi||=1`, which comes from choosing the subprojection
`vv*`, equivalent to `1 tensor e_11`, and from the non-invertibility of the
complementary support `e_eta=1-e_xi`.  Part (c) and Corollary B' (both
complementary supports have projectionless hereditary subalgebras, and this
characterizes failure of (SP)) are not consequences of the spectral
statements.
(ii) The obvious attempt to finish from here, mixing `x` and `y` by scalars
so as to make some `e_xi` invertible (Lemma K would then give the wanted
projection), cannot work from the algebraic data of (a) alone.  In `M_2(C)`
take `x=e_11`, `y=e_12`: then `x*x+y*y=e_11+e_22=1`, `xx*=yy*=e_11`,
`xy*=yx*=0`, `T=x*y=e_12` is nilpotent of norm `1`, and every `z_xi` is a
rank-one matrix, so no `e_xi` is invertible.  (There the projection is
obtained with operator coefficients, not scalars.)  This is recorded in the
Attempts of `stw74-separable-two-level-projection-descent`.

## 4. Theorem C: separable subcounterexamples

Here "nuclear" means the completely positive approximation property
(CPAP): for every finite `F subset A` and `epsilon>0` there are `k` and
completely positive contractive maps `phi: A -> M_k`, `psi: M_k -> A` with
`||psi(phi(a))-a||<epsilon` for `a in F`.  (Its equivalence with nuclearity
defined by tensor products is the Choi--Effros/Kirchberg theorem; the claim
is stated with CPAP so that no import is needed.)

**Theorem C.**  Let `A` be an LXXIV algebra and `S subset A` countable.
There is a separable unital C\*-subalgebra `C subset A` with
`S union {1_A} subset C` such that

* `C` is simple;
* every nonzero projection of `C` is infinite in `C`;
* `C` has the CPAP whenever `A` does.

In particular (i) if `a in S` and `Her_A(a)` contains no nonzero projection,
then neither does `Her_C(a)`, so `C` fails (SP) whenever `S` contains a
witness to the failure of (SP) in `A`; and (ii) combining with
`stw74-property-sp-is-the-exact-missing-condition` (applied to `A` and to
`C`), every counterexample to Problem LXXIV contains a separable
counterexample with the same unit, nuclear (CPAP) if the original one is.

### Construction

Let `C_0=C*(S union {1})`, separable.  Given a separable C\*-subalgebra
`C_n` containing `1`, choose countable dense subsets

* `P_n` of `{c in (C_n)_+ : ||c||=1}`,
* `Q_n` of the set of nonzero projections of `C_n` (possibly empty),
* `G_n` of `C_n`,

(subsets of separable metric spaces are separable) and add to `C_n` the
following countably many elements of `A`.

(alpha) For `c in P_n`: `a_c=(c-1/4)_+` is nonzero, as `||c||=1`.  Lemma 1
(with `D=A`) gives `y_(c,1),...,y_(c,k_c) in A` with
`sum_i y_(c,i)* a_c^2 y_(c,i)=1`.  Add all `y_(c,i)`.

(beta) For `q in Q_n`: `q` is infinite in `A`; choose `w_q in A` with
`w_q*w_q=q`, `w_qw_q*<=q`, `w_qw_q*!=q`.  Add `w_q`.

(gamma) Only if `A` has the CPAP: for every finite `F subset G_n` and every
`j>=1` choose c.p.c. `phi_(F,j): A -> M_(k(F,j))` and
`psi_(F,j): M_(k(F,j)) -> A` with `||psi_(F,j) phi_(F,j)(a)-a||<1/j` on `F`,
and add the finitely many elements `psi_(F,j)(e_rs)`.

Let `C_(n+1)` be the C\*-algebra generated by `C_n` and the added elements
(separable), and `C=closure(union_n C_n)`.

### Simplicity

Let `I` be a nonzero closed ideal of `C` and `pi: C -> C/I` the quotient map.
Pick `0!=a' in I`; then `a=a'*a'/||a'||^2 in I_+` has norm `1`.  Since
`union C_n` is dense, pick `d in C_n` (some `n`) with `||a^(1/2)-d||<1/40`;
then `||d||<=1+1/40` and `||a-d*d||<=||a^(1/2)-d||(||a^(1/2)||+||d||)<1/15`, so
`c'=d*d/||d*d||` satisfies `||a-c'||<2/15`.  Choose `c in P_n` with
`||c-c'||<1/10`; so `||a-c||<1/4`.  Then `||pi(c)||=||pi(c-a)||<1/4`,
`pi(c)>=0` has spectrum in `[0,1/4)`, and
`pi(a_c)=(pi(c)-1/4)_+=0`, i.e. `a_c in I`.  By (alpha),
`1=sum_i y_(c,i)* a_c^2 y_(c,i) in I` since `y_(c,i) in C_(n+1) subset C`.
Hence `I=C`.

### Projections are infinite in `C`

Let `p in C` be a nonzero projection.  Choose `n` and `h=h* in C_n` with
`||p-h||<1/10` (approximate `p` from `union C_n` and take the real part).  For
`lambda in R` at distance `>1/10` from `{0,1}`, `lambda-p` is invertible with
`||(lambda-p)^(-1)||<10`, so `lambda-h=(lambda-p)(1-(lambda-p)^(-1)(h-p))` is
invertible; thus `sigma(h) subset [-1/10,1/10] union [9/10,11/10]`.  Let `g`
be `0` on `(-inf,1/2]` and `1` on `[1/2+1/10, inf)`, continuous.  Then
`q'=g(h)` is a projection in `C_n` with `||q'-h||<=1/10`, so `||p-q'||<1/5`
and `q'!=0`.  Choose `q in Q_n` with `||q-q'||<1/5`, so `||p-q||<2/5`.

Put `z=qp+(1-q)(1-p) in C`.  A direct expansion gives
`z-1=2qp-q-p=(2q-1)(p-q)`, and `||2q-1||=1`, so `||z-1||<2/5` and `z` is
invertible in `C`.  Moreover `zp=qp=qz`, and `z*z=pqp+(1-p)(1-q)(1-p)`
commutes with `p`.  The unitary `u=z(z*z)^(-1/2) in C` satisfies

```text
u p u* = z p (z*z)^(-1) z* = z p z^(-1) = q.
```

By (beta), `w_q in C_(n+1) subset C`.  Put `w=u*w_q u in C`: `w*w=u*qu=p`,
`ww*=u*(w_qw_q*)u<=u*qu=p`, and `ww*!=p` because `w_qw_q*!=q`.  So `p` is
infinite in `C`.

### CPAP

Assume `A` has the CPAP; let `F subset C` be finite and `epsilon>0`.  Choose
`n` and, for each `a in F`, some `a' in G_n` with `||a-a'||<epsilon/3`
(possible since the `C_n` increase and `union C_n` is dense); let `F'` be the
set of these `a'`, and choose `j>epsilon^(-1)3`.  With `phi=phi_(F',j)|_C` and
`psi=psi_(F',j)`, the map `psi` takes values in the span of the
`psi(e_rs) in C_(n+1) subset C`.  Positivity of elements of `M_l(C)` does not
depend on whether they are regarded in `M_l(C)` or `M_l(A)`, so
`phi: C -> M_k` and `psi: M_k -> C` are c.p.c.  For `a in F`,

```text
||psi phi(a)-a|| <= ||psi phi(a-a')|| + ||psi phi(a')-a'|| + ||a'-a||
                 < epsilon/3 + epsilon/3 + epsilon/3.
```

### Consequences

(i) `Her_C(a)=closure(aCa) subset closure(aAa)=Her_A(a)`, and `Her_C(a)!=0`
when `a!=0`.  (ii) If `A` is a counterexample, i.e. LXXIV and not purely
infinite, `stw74-property-sp-is-the-exact-missing-condition` gives
`0!=a in A_+` with `Her_A(a)` projectionless; Theorem C with `S={a}` gives a
separable LXXIV algebra `C` failing (SP), hence (same claim, applied to `C`)
not purely infinite.  QED

*Remark.*  The graph's existing obstruction claims are repeatedly phrased
for a "separable counterexample"; Theorem C shows that assuming separability
costs nothing, both in the nuclear and in the general version of
Problem LXXIV.  (Referee note, 2026-09-16: the construction is the standard
countable-closure, Loewenheim--Skolem type argument for separably
inheritable properties; Lemmas 1--4, K and R are likewise standard
elementary facts.  They are proved here in full so that nothing is imported,
and no literature novelty is claimed for them.)

## 5. Routes between the two holes

**New hole** `stw74-separable-two-level-projection-descent`: *Let `B` be a
separable unital simple C\*-algebra in which every nonzero projection is
infinite.  If `H` is a hereditary C\*-subalgebra of `B` and `M_2(H)`
contains a nonzero projection, then `H` contains a nonzero projection.*

**Route `stw74-separable-two-level-descent-forces-sp`** (target
`stw74-hypothesis-forces-property-sp`; requires the new hole, Theorem A and
Theorem C).  Let `A` be an LXXIV algebra and suppose `A` fails (SP); pick
`0!=a in A_+` with `Her_A(a)` projectionless.  Theorem C with `S={a}` gives a
separable unital C\*-subalgebra `C` of `A`, simple, with all nonzero
projections infinite in `C`, and with `Her_C(a) subset Her_A(a)` nonzero and
projectionless; so `C` fails (SP).  Theorem A applied to `C` (implication
(2)=>(1), or its "moreover" part) gives a hereditary C\*-subalgebra `H` of `C`
with no nonzero projection such that `M_2(H)` contains one.  This
contradicts the new hole for `B=C`.  Hence `A` has (SP).

(The route uses only the non-"in particular" part of Theorem C; the claim
node for Theorem C nevertheless requires the exact-missing-condition claim
because its statement includes consequence (ii).)

**Route `stw74-property-sp-gives-separable-two-level-descent`** (target the
new hole; requires `stw74-hypothesis-forces-property-sp`).  Let `B` and `H`
be as in the new hole.  `B` has (SP) by the required claim; `M_2(H)` has a
nonzero projection, so `H!=0`; so `H` contains a nonzero projection.

Thus the two holes are equivalent (given Theorems A and C), and through the
existing route `stw74-via-property-sp` the general form of Problem LXXIV
follows from the purely level-two, separable statement: *in a separable
LXXIV algebra, a hereditary subalgebra whose `2 x 2` matrices contain a
projection contains a projection.*  The same argument, using the CPAP clause
of Theorem C, shows that the **nuclear** form of Problem LXXIV follows from
the same statement restricted to separable nuclear (CPAP) LXXIV algebras;
this nuclear restriction is recorded only here and in the Attempts of the
new hole, not as a separate node.  By Theorem B, a counterexample to the new
hole carries
`x,y` with `x*x+y*y=1`, `vv* in M_2(H)`, a full-spectrum sphere
`xi -> b_xi in H`, and a splitting `1=e+(1-e)` into two positive
contractions with projectionless hereditary subalgebras.

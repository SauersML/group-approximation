# A bounded Gram second moment gives an exactifiable positive-fraction corner

This proves the proposed weakening of full soft coverage in
`low-energy-schreier-frame-construction-2026-09-05.md`. It is conditional
on a bounded second moment of the full low-energy space. It does not
prove that arbitrary QRC5 output has that moment bound.

Use that artifact's notation: `G=SL_5(Z)`, symmetric Kazhdan generator
set `S`, `h=|S|`, constant `kappa`; finite quotient regular representations
`Pi_j` on `K_j`; canonical asymptotic input unitaries `U_(j,s)` on
`C^(d_j)`; full spectral spaces

```text
E_j=range 1_[0,epsilon_j^2](Delta_j),       epsilon_j->0,
Delta_j=(1/h)sum_s D_s^*D_s,
D_s(T)=Pi_j(s)T-TU_(j,s).
```

Assume `E_j!=0`, choose an HS-orthonormal basis `(T_a)`, and put

```text
r=dim E,       b=r/d,
B=sum_a T_a^*T_a,       C=sum_a T_a T_a^*,
H=B/b,       K_eff=Tr(C^2)/(b^2 d).
```

Suppose there is a fixed finite `M` such that

```text
tr_d(H^2)<=M.                                          (SM1)
```

Necessarily `tr_d H=1` and `M>=1`. After a subsequence there are
projections `P_j` with

```text
n_j=rank(P_j),       theta_j=n_j/d_j>=1/(16M),
max_s ||[P_j,U_(j,s)]||_(2,d_j)->0,                    (SM2)
```

and canonical asymptotic unitary tuples `W_(j,s)` on `P_j C^(d_j)`
which are compressions of the original generators up to vanishing HS
error. These corner tuples admit `(MSC7)` frames with trivial subgroup
holonomy, seed dimensions `k_j=o(d_j)`, and `beta_j,zeta_j->0`.
Consequently MSC gives exact representations `alpha_j` on dimensions
`D_j>=n_j` with

```text
(D_j-n_j)/n_j ->0,
max_s ||alpha_j(s)-(W_(j,s) direct_sum I)||_(2,D_j)->0.  (SM3)
```

The complementary compressed tuples remain canonical whenever their
relative dimension stays bounded away from zero. No full-dimension
stability endpoint is asserted here.

## 1. Second moment supplies density and almost invariance

The full spectral projection onto `E` commutes with the right regular
quotient action. Its decomposition is

```text
P_E=direct_sum_sigma P_sigma tensor I_(r_sigma),
r_sigma=dim sigma,       mu_sigma=rank P_sigma.
```

The partial trace defining `B` has rank at most
`sum_sigma r_sigma mu_sigma=r`: the partial trace of a rank-`mu_sigma`
projection over `V_sigma` has rank at most `r_sigma mu_sigma`, by
decomposing into rank-one vectors and bounding their Schmidt ranks.
Thus `rank H<=r`. Cauchy--Schwarz applied to its nonzero eigenvalues gives

```text
1=(tr_d H)^2 <= (rank H/d) tr_d(H^2) <= b M,
b>=1/M.                                                (SM4)
```

For `A_s(T)=Pi(s)T U_s^*`, low energy gives

```text
||(A_s-I)P_E||_HS <= sqrt(h) epsilon sqrt(r).
```

Expanding the difference of the two projections and using trace-norm
product bounds yields

```text
||A_s P_E A_s^*-P_E||_1 <= 2sqrt(h) epsilon r.
```

Partial trace over the target space is trace-norm contractive on this
selfadjoint difference. Its source covariance is `U_s B U_s^*-B`
(up to the harmless conjugation in the identification of Hom with a
tensor product). Dividing by `bd=r` gives

```text
a_j:=max_s ||U_s^* H U_s-H||_(1,d)
 <=2sqrt(h) epsilon_j ->0.                             (SM5)
```

## 2. A fixed spectral band captures positive dimension

Take a subsequential weak limit of the normalized spectral measures of
`H_j`; they are tight since `tr H_j=1`. Choose continuity points of
this limit with

```text
1/8<t<1/4,       4M<L<8M,
P_j=1_[t,L](H_j).
```

For every j, the spectral mass below t contributes at most t to `tr H`,
and the mass above L contributes at most `M/L`. Therefore

```text
tr(H P)>=1-t-M/L>1/2,
theta=tr(P)>1/(2L)>1/(16M).                            (SM6)
```

Also `tP<=PHP<=LP`.

Here is an explicit justification of asymptotic commutation of the
spectral band; no operator-Lipschitz assertion for a discontinuous
cutoff is being used. Put `K=(H+I)^(-1)`. The resolvent identity gives

```text
||U^*KU-K||_1 <= ||U^*HU-H||_1.
```

Both resolvents are positive contractions, so their difference has
operator norm at most one. Hence

```text
||U^*KU-K||_(2,d)^2 <= ||U^*HU-H||_(1,d).               (SM7)
```

The desired band is an interval spectral projection of K, with endpoints
`1/(L+1)` and `1/(t+1)`. Approximate its indicator by a continuous
piecewise-linear function with transition width eta. The HS functional
calculus Lipschitz bound follows directly by expansion in two spectral
bases. It bounds the commutator of that function of K by
`eta^(-1) sqrt(a_j)`. The HS distance from the band projection is bounded
by the square root of the spectral mass in the eta-neighborhoods of the
two endpoints. First let j tend to infinity, then eta tend to zero.
The continuity-point choice makes the latter mass vanish, proving `(SM2)`.

## 3. The weighted leakage estimate resolves the unbounded-frame issue

Suppress j and set

```text
F=b^(-1/2) col_a T_a,       F^*F=H,
ell_j=max_s ||(I-P)U_sP||_(2,d_j)->0.
```

The full F can have arbitrarily large operator norm. Only `FP` has
singular values bounded between `sqrt(t)` and `sqrt(L)`. Thus it would
be incorrect to bound `F(U_sP-PW_s)` by using `sqrt(L)` on its entire
argument.

Instead, write `Q=I-P` and use the following weighted bound:

```text
||F Q U_sP||_(2,d)^2
 =tr(P U_s^* Q H Q U_s P)
 <=a_j+L ||P U_s Q||_(2,d)^2
 =a_j+L ||Q U_s P||_(2,d)^2.                           (SM8)
```

To derive it, use that H commutes with P and expand the first trace as

```text
tr(P U_s^* H U_s P)-tr(P U_s^* P H P U_s P).
```

The first term is at most `tr(PH)+a_j`. Cyclicity rewrites the second
as `tr(H P U_s P U_s^* P)`, which is at least
`tr(HP)-L tr(P U_s Q U_s^* P)`. Their difference proves the inequality.
The last equality follows because the two off-diagonal blocks of a
unitary have equal HS mass.

Choose a unitary polar completion `W_s` of the square compression
`P U_s P` on `P C^d`, choosing inverses consistently. Its singular values
are at most one, and `(1-x)^2<=1-x^2` gives

```text
||P U_s P-W_s||_(2,d)<=ell_j,
||U_sP-PW_s||_(2,d)<=sqrt(2) ell_j.                    (SM9)
```

Here `W_s` on the right is identified with its supported extension.
The residual of the restricted frame is

```text
Pi^direct_sum(s)FP-FP W_s
 =(Pi^direct_sum(s)F-FU_s)P
   +FQ U_sP+FP(PU_sP-W_s).
```

Its original-normalized HS norm is at most

```text
e_j:=sqrt(h)epsilon_j+sqrt(a_j)+2sqrt(L)ell_j ->0.       (SM10)
```

In this estimate the first term is bounded by the total low-energy
ledger, the second by `(SM8)`, and the third uses only the bounded
operator norm of `FP`.

## 4. Whitening and sublinear-seed compression

Define the exact isometry from the selected input space

```text
J_0=FP (PHP|_(P C^d))^(-1/2).
```

For full-column-rank rectangular maps with minimum singular values at
least `a>0`, the polar isometry map is HS Lipschitz with constant `1/a`.
One proof writes the two maps as `VH,WK`, with `H,K>=aI`, and expands
the real trace pairing with `V-W`: positivity of
`I-Re(V^*W)` gives a lower bound `a||V-W||_HS^2`, followed by
Cauchy--Schwarz. Apply this to `Pi(s)FP` and `FP W_s`, both of which
have least singular value at least `sqrt(t)`. It follows that

```text
max_s ||Pi^direct_sum(s)J_0-J_0 W_s||_HS/sqrt(n)
 <= e_j/sqrt(t theta_j).                              (SM11)
```

Already `(SM11)` is an exact isometric MSC input in a finite genuine
ambient representation, with no restriction on its multiplicity. To
obtain sublinear seed dimensions as well, use the effective-covariance
result `(LF8)` from the low-energy frame artifact. Its hypotheses are
met: the original input is canonical and `(SM4)` bounds b away from
zero. Thus `K_eff,j/d_j->0`.

Write `J_0=col_a S_a`. Since
`P(PHP|_P)^(-1)P<=t^(-1)I`, its other covariance satisfies

```text
C_sel=sum_a S_a S_a^* <= C/(bt),
Tr(C_sel^2)/n <= K_eff/(t^2 theta).                    (SM12)
```

The Gaussian compression in `(LF3)--(LF5)` therefore supplies a
rectangular frame with k fibres and bounds

```text
zeta <= 2sqrt(K_eff/(t^2 theta k)),
beta <= 2sqrt(h/(t theta)) e_j.                        (SM13)
```

For example take `k_j=ceil sqrt(d_j max(1,K_eff,j))`.
Then `k_j=o(d_j)`, `K_eff,j/k_j->0`, and both errors in `(SM13)` tend
to zero. The subgroup representation is trivial of dimension k_j.
Applying MSC with `gamma_j=beta_j+2sqrt(zeta_j)` gives explicitly

```text
(D_j-n_j)/n_j <=4gamma_j^2/kappa^2,
max_s ||alpha_j(s)-(W_(j,s) direct_sum I)||_(2,D_j)
 <=(1+10/kappa)gamma_j,
```

which proves `(SM3)`.

## 5. The corner remains canonical

The polar compression errors `(SM9)`, normalized by `sqrt(n/d)` which
is bounded away from zero, show by fixed-word telescoping that W is an
asymptotic representation. Its limiting normalized word traces agree
with those of `P U(word)P/n`.

For completeness, `SL_5(Z)` is ICC. If a matrix has finite conjugacy
class, its centralizer has finite index and therefore contains a nonzero
power of every elementary root generator. Commuting with those powers
means commuting with every matrix unit `E_ij`. The matrix is consequently
scalar; an integral scalar matrix of determinant one in odd dimension
is the identity.

Pass to a further subsequence so `theta_j->theta>=1/(16M)` and all
corner characters converge. Asymptotic commutation makes the corner
limit a normalized positive-definite class function `chi_P`. If
`theta<1`, the complementary corner has such a limit `chi_Q` as well,
and the canonical input traces give

```text
delta_e=theta chi_P+(1-theta)chi_Q.                     (SM14)
```

The regular character of an ICC group is extremal: its group von
Neumann algebra is a factor, so a dominated tracial functional has
scalar central Radon--Nikodym derivative. Therefore `(SM14)` forces
both characters to equal `delta_e`. If `theta=1`, the vanishing
complementary trace directly gives `chi_P=delta_e`. This proves the
claimed canonicality. The same argument applies along every further
convergent subsequence, so it yields convergence rather than just one
canonical cluster point.

This establishes positive-fraction exactifiable corners from `(SM1)`.
The existence of suitable low-energy cutoffs satisfying `(SM1)` for
arbitrary canonical approximate SL5 tuples is still an additional input.

# A finite native S3 reduces the second heat-rounding demand

2026-09-08. Written algebra and finite-matrix inequalities. No script,
job, build, search, or new Lean verification is used. The theorem is
conditional on the supplied algebra enlargement; it does not establish
that enlargement or determine hyperlinearity.

## 1. Two fixed native observables and their finite subgroup

Let `R=L_(F_2)(1,2)` and write

```text
s=s_0, t=t_0, a=s_1, b=t_1,
ts=ba=1, ta=bs=0, st+ab=1, e=ab=1-st.
```

Use the established identification `H=GL_4(R)=EL_4(R)`, with
`L=diag(GL_3(R),1)` and `K=diag(1,1,1,R^x)`. These two native
subgroups commute. The identification follows from
[[leavitt-gl-equals-el-and-perfect-unit-group]] and prefix self-similarity.

The actual compressor and its inverse are

```text
u = [ s 0 0 e    ],        u^(-1) = [ t  0   0   0   ],
    [ 0 s 0 e t  ]                 [ 0  t   0   0   ]
    [ 0 0 s e t^2]                 [ 0  0   t   0   ]
    [ 0 0 0 t^3  ]                 [ e  s e s^2 e s^3].
```

Both products are identity by the displayed Leavitt relations; the
last diagonal entry of `u^(-1)u` is
`e+s e t+s^2 e t^2+s^3t^3=1`.
Put

```text
k_+=diag(1,1,1,1+a t^3),
k_-=diag(1,1,1,1+s^3 b),
F_0=<k_+,k_-> <= K.                                (1)
```

These are involutions: their added terms square to zero, since
`ta=bs=0`. They generate exactly `GL_2(F_2)`, and hence `S_3`.
Here is a prefix proof that keeps the subgroup finite. For a binary
word `alpha`, let `s_alpha` be its creation word and `t_alpha` its
annihilation word in reverse order. The two added terms are

```text
a t^3=s_1 t_000,       s^3 b=s_000 t_1.
```

The leaves `000` and `1` are incomparable, with orthogonal nonzero
idempotents `p=s^3t^3` and `e=ab`. The four elements
`p,e,s_1t_000,s_000t_1` are the matrix units of a copy of
`M_2(F_2)` on their sum; the two units in (1) are its opposite
elementary transvections and act as identity on the complement.
Equivalently, use the complete prefix code `{000,001,01,1}` and
fix its other two leaves. The two transvections generate the six
invertible binary matrices of size two. This proves `F_0≅S_3`,
without assuming that the whole group `K≅H` is finite or manageable.

Direct multiplication by the displayed `u` gives

```text
y_+=u k_+ u^(-1)=x_14(a),
y_-=u k_- u^(-1)=x_41(b).                           (2)
```

For the first equality, `u k_+` and `x_14(a)u` differ from `u`
only by `a t^3` in position `(1,4)`. For the second, the only
difference is `b` in position `(4,4)`.

For every `r in R`, three-distinct-index commutators give

```text
x_24(r)=[x_21(r b),y_+],
x_42(r)=[y_-,x_12(a r)].                            (3)
```

The products of coefficients are `rba=r` and `bar=r`, respectively.
Commuting these roots with `x_i2(1)` or `x_2j(1)` in `L` gives
the remaining roots involving coordinate four. Since all elementary
roots generate `H`,

```text
H=<L,u F_0 u^(-1)>.                                (4)
```

Only the two fixed elements in (1), not a generating set for `K`,
are needed in (4).

## 2. The finite-observable enlargement hypotheses

Let `phi_n` be a full canonical matrix microstate sequence of `H`
in `M_(d_n)`, with normalized trace and Hilbert--Schmidt norm.
Thus every fixed true relation has defect tending to zero, and
every fixed nonidentity group word has trace tending to zero.
Evaluate fixed literal words for `u,k_+,k_-`, obtaining unitaries
`U_n,K_(+,n),K_(-,n)`. Choose a fixed finite symmetric generating
list `S_L` of `L`, with matrix evaluations `V_(n,s)`.

Suppose there are unital finite-dimensional *-subalgebras
`A_n subset M_(d_n)`. Write

```text
E_n=E_(A_n),
F_n=Ad(U_n) E_n Ad(U_n*),
e_n=sum_(s in S_L) integral_(v in U(A_n)) ||[V_(n,s),v]||_2^2 dv,
kappa_n=max_(sign=+,-) ||K_(sign,n)-E_n(K_(sign,n))||_2,
alpha_n=integral_(v in U(A_n)) ||v-F_n(v)||_2^2 dv.   (5)
```

Every Haar measure has mass one, and every expectation preserves
normalized trace. Assume precisely

```text
e_n -> 0,       kappa_n -> 0,       alpha_n -> 0.    (6)
```

**Theorem.** Under (6), the full external `H`-commutant in any
tracial matrix ultraproduct of this sequence contains a self-adjoint
element `z` with

```text
tau(z)=0,       ||z||_op<=1,       ||z||_2>=1/8.     (7)
```

In particular the full commutant is not scalar. The conclusion does
not assert that `z` is central in that full commutant.

## 3. Uniform centralization and the reverse witness

For a unitary `V`, Haar averaging over `U(A_n)` gives

```text
integral ||[V,v]||_2^2 dv=2||V-E_(A_n')(V)||_2^2.
```

Since `E_(A_n')(V)` commutes with every contraction `x in A_n`,

```text
sup_(x in A_n, ||x||_op<=1) ||[V_(n,s),x]||_2
 <= sqrt(2e_n) -> 0.                               (8)
```

Fixed-word telescoping extends this to every fixed element of `L`.
This converts the mean condition into the uniform control needed
for central heights; no unproved uniformity over words is used.

Put `Y_n=U_n K_(+,n) U_n*`, a literal evaluation of `y_+`.
The captured observable gives

```text
||F_n(Y_n)-Y_n||_2<=kappa_n.                        (9)
```

There is already a robust one-word reverse bound. With
`ell=x_21(b) in L`, (3) gives `[ell,y_+]=x_24(1)!=1`.
Canonicality implies that the additive matrix commutator of their
evaluations has norm tending to `sqrt(2)`. By (8),
`E_n(Y_n)` nearly commutes with the evaluation of `ell`. Thus

```text
||Y_n-E_n(Y_n)||_2>=1/sqrt(2)-o(1).
```

If `rho_n=||E_n F_n-F_n||_(infinity->2)`, (9) yields

```text
rho_n>=1/sqrt(2)-o(1).                             (10)
```

For full canonical microstates, the native algebra gives the sharper
`rho_n->1`. For every `r in R`, the element `g_r=x_21(r b)` lies
in `L`, and (3) gives

```text
g_r y_+ g_r^(-1)=x_24(r)y_+.                        (11)
```

These conjugates are distinct for distinct `r`; `R` is infinite.
Fix any `M` distinct choices and average their literal matrix
conjugates into `T_n`. Canonicality gives `||T_n||_2^2->1/M`.
The contractions `X_n=E_n(Y_n)` nearly commute with each of these
fixed conjugating matrices by (8). Consequently

```text
||X_n||_2^2=tr(Y_n*X_n)=tr(T_n*X_n)+o(1).
```

Cauchy--Schwarz bounds the limsup by `1/sqrt(M)`. Let `M` grow
after taking the limit in `n`, proving `||E_n(Y_n)||_2->0`.
Together with (9), this gives

```text
||(I-E_n)F_n(Y_n)||_2 -> 1,       rho_n -> 1.        (12)
```

The upper bound `rho_n<=1` holds because `I-E_n` is an `L^2`
contraction and `F_n` sends contractions to contractions. The orbit
argument uses no heat identification and no assumption that `y_+`
lies in `L`.

## 4. A finite central-height lemma with constants

The following finite-dimensional lemma supplies the height.
Let `A subset M_d` be a unital finite-dimensional
algebra, `B=UAU*`, and `E,F` their expectations. Write `alpha`
and `beta` for the forward and reverse Haar-mean squared leakages.
The general Haar supremum-to-mean inequality gives

```text
||FE-E||_(infinity->2)^2<=2alpha,
rho^2:=||EF-F||_(infinity->2)^2<=2beta.              (13)
```

To see the inequality, average commutators against the unitary group
of the target commutant to express a leakage as half their squared
norm. For any fixed matrix, its commutator with a source unitary is
at most twice its distance from the source commutant; averaging that
commutator squared over source unitaries gives twice the squared
distance. This bounds each leakage by twice its Haar mean.
The unit ball of a matrix algebra is the convex hull of its unitaries,
so this also gives the displayed mixed-norm statements.

Suppose `rho^2/2-alpha>=1/4`. Let `p_i` be the central atoms of
`A`, set `q_i=Up_iU*`, and define

```text
t_i=tr(p_i),      w_i=t_i/a_i^2,      h_i=log(w_i),
m_ij=tr(p_iq_j),
```

where `a_i` is the simple degree of `p_i A`. Let `P_i,Q_j` be
the Hilbert projections onto `p_i A,q_j B` and
`H_ij=Tr_HS(P_iQ_j)`. Haar matrix-entry covariance gives

```text
w_i H_ij<=m_ij,       w_j H_ij<=m_ij,
alpha=sum_ij(m_ij-w_i H_ij),
beta =sum_ij(m_ij-w_j H_ij).                        (14)
```

For completeness, the covariance of a Haar unitary of `p_i A`
is `w_i P_i`. Its projected squared norm onto `q_j B` averages
to `w_i H_ij`, and is bounded by `tr(p_iq_j)` because the
projection is contractive and supported on `q_j`. Interchanging
the two blocks gives the other bound. Summing the losses gives
the two equalities in (14).

The nonnegative matrix `m` has both marginals `t_i`. Define

```text
up=sum_(h_j>h_i) m_ij(1-exp(-(h_j-h_i))),
down=sum_(h_i>h_j) m_ij(1-exp(-(h_i-h_j))).
```

Equation (14) implies

```text
up<=alpha,       down>=beta-alpha>=rho^2/2-alpha>=1/4.
```

Choose a physical-weight median `c` of the heights, and set
`r=1/16`. If `T=sum_(|h_i-c|>=r)t_i`, edges whose endpoints
are both inside that interval contribute at most `2r` to `down`;
edges with an outside endpoint have total mass at most `2T`.
Thus `T>=1/16`. One tail has mass at least `1/32`, while the
opposite median side has mass at least `1/2`.

Use the increasing ramp across that tail interval, clipped to
`[0,1]`. Denote it by `f`; its two endpoint level sets have those
respective masses. Hence `Var_t(f)>=1/64`. Moreover stationarity,
monotonicity, and the elementary inequality
`min(x/r,1)<=(1-exp(-x))/(1-exp(-r))` give

```text
sum_ij m_ij|f(h_i)-f(h_j)|^2
 <=2up/(1-exp(-r))<=2alpha/(1-exp(-1/16)).
```

Consequently the self-adjoint central matrix

```text
z=sum_i (f(h_i)-sum_j t_j f(h_j))p_i
```

satisfies

```text
tr(z)=0, ||z||_op<=1, ||z||_2>=1/8,
||[U,z]||_2^2<=2alpha/(1-exp(-1/16)).               (15)
```

The last squared commutator is precisely the preceding balanced-flow
sum. This proves the height lemma directly. A merely positive lower
bound `rho^2/2-alpha>=c_0>0` also suffices: take `r=c_0/4`
in the same argument to obtain `||z||_2>=sqrt(c_0)/4` and
the denominator `1-exp(-c_0/4)` in (15). Thus (10) alone can
use `c_0=1/8`; the orbit upgrade (12) permits the constants displayed
in (15).

## 5. Finite capture turns the height into a whole-group commutant element

By (6) and (12), the height lemma applies to `A_n,U_n` for all
sufficiently large `n`. It supplies `z_n in Z(A_n)` obeying (15),
with `alpha=alpha_n`. Equation (8) makes `z_n` asymptotically
commute with every fixed element of `L`. Its commutator with `U_n`
tends to zero by (15). Finally, centrality in `A_n` gives

```text
||[K_(sign,n),z_n]||_2
 <=2||K_(sign,n)-E_n(K_(sign,n))||_2<=2kappa_n -> 0.
```

Thus its ultraproduct limit commutes with `L,u,k_+,k_-`, and
hence with `u F_0 u^(-1)`. The generation identity (4) puts it in
the full `H`-commutant. Its trace and norms satisfy (7), proving
the theorem.

Only the two captured observables were used. We did not identify
the ultraproduct of `A_n` with the entire `L`-commutant, so we
do not infer centrality in the entire `H`-commutant. Nonscalarity
is enough to contradict the scalar commutant produced by the
separate global selection argument.

## 6. The finite S3 algebra supplies a starting point, not the enlargement

Suppose the fixed native `F_0` restriction has been perturbed to
an exact representation `sigma_n:S_3->U(d_n)` at distance tending
to zero on its two generators. Set `A_n^0=sigma_n(C[S_3])`.
This captures `K_(+,n),K_(-,n)`. Since `F_0` commutes with `L`,
the commutator errors of its six fixed elements with each generator
of `L` tend to zero.

Canonical traces imply that every irreducible `S_3` type eventually
occurs. Every contraction in `A_n^0` then has a group-basis lift
with coefficient l1 norm at most `sqrt(6)`: its regular l2 norm
is at most its operator norm, and apply Cauchy--Schwarz to six
coefficients. Thus these finite commutator estimates are uniform
on the algebra unit ball, supplying the first two conditions in (6).

They cannot supply the third. The three irreducible degrees are
`1,1,2`. By the exact central-character projection formulas and
canonical trace convergence, the physical weights of these three
blocks tend to `1/6,1/6,4/6`. Therefore their trace-weight
distortion `R_n=max_i(t_i/a_i^2)/min_i(t_i/a_i^2)` tends to one.
The covariance argument gives `beta_n<=R_n alpha_n` directly:
the forward covariance operator is between `w_min E_n` and
`w_max E_n`, and the reverse one obeys the same bounds with `F_n`.
The Hilbert projections have equal rank `D`, and
`Tr_HS(E_n(I-F_n))=Tr_HS(F_n(I-E_n))=D-Tr_HS(E_nF_n)`.
Thus the forward mean is at least `w_min` times this common
quantity, and the reverse mean is at most `w_max` times it.
Combining this with (12)--(13) yields

```text
alpha_n>=rho_n^2/(2R_n)>=1/2-o(1).                 (16)
```

This argument is conditional on the stated finite-group repair and
does not require a new stability theorem. Even granting such repair,
the resulting fixed finite algebra fails the required forward inclusion.
A larger algebra with a different central structure is needed.

## 7. The remaining construction problem

The theorem requires only the three explicit quantities in (5) to
vanish. It does not ask for uniform approximation of a heat map on
the whole operator unit ball. Its finite-group starting point is
specified, and (16) explains why enlarging that algebra is essential.

In a program that separately obtains canonical microstates with scalar
full commutant from global heat rounding, proving this enlargement
for the selected sequence would give a contradiction. The global
selection and the actual algebra enlargement are not supplied or used
as proved prerequisites here. In particular this theorem does not
certify a complete graph route to nonhyperlinearity through any
concurrent heat-rounding notes. The proved endpoint is the conditional
nonscalarity statement (7).

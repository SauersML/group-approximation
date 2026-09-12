# Native central heights commute with the whole Leavitt group

2026-09-08. Written finite-matrix and group arguments. No computation,
build, job, or new Lean verification. Hyperlinearity of
`H=L_(F_2)(1,2)^x` remains undecided.

## 1. A quantitative central height from one-sided inclusion

Let `A subset M_d` be a unital finite-dimensional algebra, `B=UAU*`,
and let `E,F` be their trace-preserving expectations. Write

```text
delta=||FE-E||_(infinity->2),
rho=||EF-F||_(infinity->2).
```

Suppose

```text
rho^2/2-delta^2 >= 1/4.                              (1)
```

Then there is a self-adjoint `z in Z(A)` with

```text
tr(z)=0,       ||z||_op<=1,       ||z||_2>=1/8,
||[U,z]||_2 <= sqrt(2/(1-exp(-1/16))) delta.           (2)
```

In particular, (1) eventually holds whenever `delta->0` and `rho->1`.

Here is a proof with constants. Let `p_i` be the central atoms of `A`,
put `q_i=Up_iU*`, and write

```text
t_i=tr(p_i),       w_i=t_i/a_i^2,       h_i=log(w_i),
m_ij=tr(p_i q_j),
```

where `a_i` is the simple degree of `p_iA`. The matrix `m` is a
nonnegative balanced flow: its row and column sums are both `t_i`.
Let `alpha_A,alpha_B` be the forward and reverse Haar-mean squared
leakages. The
[central-overlap estimates](leavitt-regular-trace-cp-reversal-2026-09-08.md)
give

```text
up := sum_(h_j>h_i) m_ij (1-exp(-(h_j-h_i)))
   <= alpha_A <= delta^2,

down := sum_(h_i>h_j) m_ij (1-exp(-(h_i-h_j)))
     >= alpha_B-alpha_A >= rho^2/2-delta^2.           (3)
```

Indeed, if `P_i,Q_j` are the Hilbert projections onto `p_iA,q_jB`
and `H_ij=Tr_HS(P_iQ_j)`, then both `w_i H_ij` and `w_j H_ij`
are at most `m_ij`. Thus the forward loss
`sum_ij(m_ij-w_i H_ij)` bounds `up`; the reverse-minus-forward
loss is at most `down`. The bound `rho^2<=2alpha_B` is the general
Haar supremum-to-mean inequality.

Choose a physical-weight median `b` of `h`, so each of
`{h<=b}` and `{h>=b}` has mass at least `1/2`. Set `r=1/16` and
`T=sum_(|h_i-b|>=r)t_i`. Edges with both endpoints inside this
interval have downward cost at most `2r`, and edges with an endpoint
outside have total mass at most `2T`. Consequently

```text
1/4 <= down <= 2r+2T,       T>=1/16.
```

At least one tail has mass at least `1/32`. For such an upper tail,
use `f(h)=clamp((h-b)/r,0,1)`; for a lower tail, use the increasing
ramp `f(h)=clamp((h-(b-r))/r,0,1)`. In either case one level set
`f=0` or `f=1` has mass at least `1/2`, and the opposite level set
has mass at least `1/32`. The pairwise formula for variance gives

```text
Var_t(f) = (1/2) sum_ij t_i t_j |f(h_i)-f(h_j)|^2
         >= 1/64.                                   (4)
```

For every positive increment `a`, concavity of `1-exp(-a)` gives

```text
min(a/r,1) <= (1-exp(-a))/(1-exp(-r)).
```

Using `0<=f<=1`, monotonicity, and stationarity of `m`, we obtain

```text
sum_ij m_ij |f(h_i)-f(h_j)|^2
 <= sum_ij m_ij |f(h_i)-f(h_j)|
 = 2 sum_(h_j>h_i) m_ij (f(h_j)-f(h_i))
 <= 2 up/(1-exp(-r)).                               (5)
```

Set `z=sum_i(f(h_i)-sum_j t_j f(h_j))p_i`. Its commutator squared
norm is exactly the first sum in (5). Equations (3)--(5) prove (2).
Median atoms and interval endpoints are included in the stated level
sets, so they require no continuity or non-atomicity assumption.

## 2. Application to the actual native heat maps

Use the native subgroup `L=EL_3(R)` on coordinates `1,2,3`, its
compressor `u`, and the canonical heat maps `P_n,Q_n` from the
[native heat argument](leavitt-heat-rounding-forces-unbounded-trace-distortion-2026-09-08.md).
Suppose a full canonical microstate sequence admits rounded algebras
`A_n` with

```text
eta_n=||E_(A_n)-P_n||_(infinity->2) -> 0.
```

For `F_n=Ad(U_n)E_(A_n)Ad(U_n*)`, the expectation forward defect is
at most `delta_heat,n+3eta_n -> 0`, while its reverse defect tends to
one. Therefore (2) supplies self-adjoint `z_n in Z(A_n)` with

```text
tr(z_n)=0,       ||z_n||_op<=1,       ||z_n||_2>=1/8,
||[U_n,z_n]||_2
 <= sqrt(2/(1-exp(-1/16))) (delta_heat,n+3eta_n) -> 0. (6)
```

These heights also asymptotically commute with every fixed generator
of `L`. To see this uniformly, `||P_nz_n-z_n||_2<=eta_n`, and the
heat-energy estimate bounds every generator commutator of `P_nz_n`
by a quantity tending to zero. Transferring to `z_n` costs `2eta_n`.

In the tracial ultraproduct `M`, let

```text
D=pi(L)' intersect M,       C=pi(H)' intersect M.
```

The full heat identification and rounding give `D=product_omega A_n`.
Thus the height limit satisfies

```text
z in Z(D),       [pi(u),z]=0,
tau(z)=0,        ||z||_op<=1,       ||z||_2>=1/8.     (7)
```

It also commutes with the native fourth-coordinate copy `K`, since
`pi(K) subset D`. This conclusion uses the actual native compressor,
with the full canonical microstate and rounding hypotheses above.

## 3. The compressed complementary corner generates the missing roots

Use the standard binary Leavitt generators

```text
s=x_1,       t=y_1,       a=x_2,       b=y_2,
ts=ba=1,     ta=bs=0,     st+ab=1,
e=1-st=ab,   ea=a,        be=b.
```

For `p=diag(1,1,1,0)`, the actual compressor matrix gives
`upu^{-1}=diag(st,st,st,0)`. Consequently `uKu^{-1}` is the full
unit group supported on `q=diag(e,e,e,1)`, with identity on `1-q`.
In particular it contains `x_14(a r)` and `x_41(r b)` for every
`r in R`. Steinberg commutators now give

```text
x_24(r)=[x_21(b),x_14(a r)],
x_42(r)=[x_41(r b),x_12(a)].                         (8)
```

The first factor or the second factor, respectively, lies in `L`.
Commuting the roots in (8) with the other roots in `L` gives all
remaining roots involving coordinate `4`. Thus

```text
H=<L,uKu^{-1}>.                                    (9)
```

This uses the full Leavitt complement: the identity `ba=1` turns the
overlap with `q` into arbitrary root coefficients. The entire conjugate
`uKu^{-1}` is supported on `q`, which includes coordinate `4`.

There is also an explicit fixed word for the constant coordinate swap
`w=w_34`. Define the following two involutions in `K`:

```text
k_+=diag(1,1,1,1+a t^3),
k_-=diag(1,1,1,1+s^3 b).
```

Their added terms square to zero, by `ta=bs=0`. Direct multiplication
by the displayed native compressor gives

```text
u k_+ u^{-1}=x_14(a),       u k_- u^{-1}=x_41(b).
```

For example, `u k_+` and `x_14(a)u` both differ from `u` only by
`a t^3` in position `(1,4)`; `u k_-` and `x_41(b)u` both differ
from `u` only by `b` in position `(4,4)`. Put

```text
r_24=[x_21(b),u k_+ u^{-1}],
r_42=[u k_- u^{-1},x_12(a)],
r_34=[x_32(1),r_24],       r_43=[r_42,x_23(1)].

w_34=r_34 r_43 r_34.                               (10)
```

Here `r_ij=x_ij(1)`, and the last equality is the characteristic-two
elementary formula for the transposition. Independently, `L` and
`wLw^{-1}` contain all elementary roots except `(3,4),(4,3)`, which
their commutators supply. Hence `H=<L,w>` as well.

## 4. Quantitative control of the actual coordinate swap

Evaluate the literal spelling (10) on a unitary tuple, writing
`W_word` for that spelling, and let `z` be any contraction. Set

```text
c_u=||[U,z]||_2,       c_+=||[K_+,z]||_2,
c_-=||[K_-,z]||_2,
c_32=||[X_32(1),z]||_2,   c_21=||[X_21(b),z]||_2,
c_12=||[X_12(a),z]||_2,   c_23=||[X_23(1),z]||_2.
```

The product commutator bound and
`||[VTV*T*,z]||_2<=2||[V,z]||_2+2||[T,z]||_2` give the exact ledger

```text
||[W_word,z]||_2
 <= 24c_u+8c_++4c_-+4c_32+8c_21+4c_12+2c_23.       (11)
```

If a different literal spelling `W` is used for the same native swap,
add `2||W-W_word||_2` to this bound. That is a separate fixed native
equality allowance, which tends to zero in full canonical microstates.

For the heights from Section 2, `c_u->0` by (6), and the four
`L`-root terms vanish by generator telescoping. The terms `c_+,c_-`
also tend to zero. Indeed, each `K_+` and `K_-` asymptotically commutes
with `L`; integrated heat retention gives `||P_nK_+-K_+||_2->0`
and the same for `K_-`. Rounding then places these matrices at
distance tending to zero from `A_n`. Since `z_n` is central in `A_n`,

```text
||[K_+,z_n]||_2 <= 2||K_+-E_(A_n)(K_+)||_2 -> 0,
```

and similarly for `K_-`. This use of integrated retention needs no
extra rate for their commutator convergence. Equation (11) therefore
controls the native swap and, together with `H=<L,w>`, every fixed
native generator of `H`.

## 5. Uniform rounding forces a nonfactorial global commutant

The exact ultraproduct argument is particularly short. The height
`z in Z(D)` commutes with `pi(K) subset D`, and it commutes with
`pi(u)` by (7). Thus it commutes with `pi(uKu^{-1})`. Equation (9)
shows `z in C`. Since it also commutes with `C subset D`, we have

```text
z in Z(C),       tau(z)=0,       ||z||_2>=1/8.        (12)
```

Therefore uniform expectation rounding of the native `L`-heat maps
forces the full external `H`-commutant to be nonfactorial. This is
stronger than merely producing a diffuse part in `Z(D)`. It excludes
rounding for any canonical embedding with factorial global commutant.

Property (T) is consistent with (12). Its invariant subspace in the
external conjugation representation is `L^2(C)`. More precisely, for
any `f in Z(D)`, `C`-bimodularity gives `E_C(f) in Z(C)`, and a
Kazhdan constant for `S_L union {w}` yields

```text
||f-E_(Z(C))(f)||_2 <= kappa_H^(-1)||[pi(w),f]||_2.
```

For these native heights the right side vanishes, so the gap places
them in `Z(C)` exactly. Their positive variance does not contradict
the gap. Factoriality of the canonical group trace concerns `pi(H)''`
and does not identify `Z(C)`.

The subsequent
[component-selection theorem](leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md)
removes a separate embedding-selection assumption under universal
heat rounding. One rounded global H-heat permits selection of a
canonical model with scalar full global commutant. A second rounding
instance for its restriction to the isomorphic L then contradicts
(12). The universal rounding premise is still unproved, so the
hyperlinearity question remains open.

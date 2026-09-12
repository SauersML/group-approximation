---
rg: 2
id: kt-nested-compressor-flat-tower-wall-proof
kind: route
title: Truncate the monomial chain, gauge every strict level, and count nonliftable blocks
target: kt-nested-compressor-flat-tower-has-uniform-wall
requires:
  - infranormal-compact-closure-normal
---

Put

```text
R_L=F_q[x,y]/(x^L,y^2)
```

and send every `z_i` to zero.  Let `q_L:Gamma->B_L=EL_r(R_L)` be the
resulting finite quotient.  For `0<=j<=L`, set

```text
S_j=F_q[x,x^j y] subset R_L,
H_j=q_L(alpha^j(Gamma))=EL_r(S_j).                       (KFP1)
```

Because every `y`-coefficient in `S_j` is divisible by `x^j`,

```text
g_j=q_L(alpha^(j-1)(gamma))=e_(ab)(x^(j-1)y)
       belongs to H_(j-1) but not H_j                    (KFP2)
```

for `1<=j<=L`.  The last assertion is visible in the `(a,b)` matrix entry:
every matrix in `EL_r(S_j)` has all entries in `S_j`, while
`x^(j-1)y` is not in `S_j`.

Let `lambda_L` be the left regular representation of `B_L`.  For each
`1<=j<L`, choose a diagonal sign involution `D_j` on `ell^2(B_L)`, constant
on every left `H_j`-orbit, such that

```text
D_j in lambda_L(H_j)',
||lambda_L(g_j)-D_j^* lambda_L(g_j)D_j||_2^2>=2.          (KFP3)
```

Such a sign exists by independent random signs on the left `H_j`-orbits.
Since `g_j` is not in `H_j`, the two orbit labels at `u` and `g_j u` are
distinct for every `u`; hence the expected real normalized inner product is
zero and the expected squared distance in `(KFP3)` is two.  Put `D_0=1`.

On

```text
K_L=direct_sum_(j=0)^(L-1) ell^2(B_L)
```

define

```text
Pi_L(delta)|_(K_j)=lambda_L(q_L(alpha^j(delta))).         (KFP4)
```

Let `T_L` be the cyclic backward block shift `K_j->K_(j-1 mod L)`, put

```text
D_L=direct_sum_(j=0)^(L-1) D_j,
T_(0,L)=T_L,                 T_(1,L)=T_L D_L.             (KFP5)
```

Equation `(KFP1)` says `D_L` commutes with `Pi_L(Gamma)`.  On the first
`L-1` target blocks, conjugation by `T_L` implements `alpha` exactly; only
the wrap block compares levels `0` and `L`.  Its normalized weight is
`1/L`, and a difference of two unitaries has squared norm at most four.
This proves `(KFT2)` for `T_(0,L)`, and `(KFP5)` plus
`[D_L,Pi_L(Gamma)]=0` gives the identical bound for `T_(1,L)`.

For the returned word, on block `K_j`, `1<=j<L`,

```text
T_(0,L)^* Pi_L(gamma)T_(0,L)=lambda_L(g_j),
T_(1,L)^* Pi_L(gamma)T_(1,L)=D_j^*lambda_L(g_j)D_j.       (KFP6)
```

Averaging `(KFP3)` over the `L-1` interior blocks proves `(KFT3)`.  The
usual fixed-word evaluation of the generator maps then gives asymptotic
representations of the ascending HNN group `V`; the only presentation
errors are the covariance errors already estimated.  In the tracial matrix
ultraproduct set

```text
pi(v)=diag(eta_0(v),eta_1(v)),
S=[[0,1],[1,0]].                                           (KFP7)
```

Exact agreement on `Gamma` gives `S in pi(Gamma)'`, while `(KFT3)` gives
`[S,pi(h)]!=1`.  This is the asserted bare wall for the one-compressor
subgroup.

For the full-actor firewall, every genuine finite-dimensional pair
`rho_0,rho_1:G->U(n)` agreeing on `Gamma` folds `h`: by
`infranormal-compact-closure-normal`, the compact closure of the common
`Gamma` image is normal, and the calculation in
`kt-double-shortest-fold-repair-proof` gives `rho_0(h)=rho_1(h)`.  Hence the
fold distance is zero on every exact block.  If the complementary blocks
have total normalized dimension `beta_L`, their squared unitary distance is
at most four, so orthogonality of the block sum gives

```text
c_L<=4 beta_L,
```

which is `(KFT4)`.  This proves the claimed positive-density extension
firewall without asserting that an arbitrary non-block-preserving
approximate extension to `G` is impossible.

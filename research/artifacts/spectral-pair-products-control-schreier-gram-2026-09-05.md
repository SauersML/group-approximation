# Spectral pair products control the Schreier Gram matrix without index loss

The full low-energy spectral space constructs an exact target
representation of its own dimension r. Polar completion gives an exact
rank-r corner when `r<=d`, with error `O(epsilon)` normalized by r; when
`r>d`, it gives a full exact correction with `O(epsilon^2)` relative
padding. These estimates are independent of the quotient index and of
the fraction r/d. For canonical inputs with r/d bounded below, an exact
multiplicity embedding supplies sublinear seeds without Gaussian loss.

The mechanism is a weighted pair-product trace identity and property
(T), which rigidly control the source Gram matrix once the spectral
dimension is known.

This does not prove the existence of sufficiently many low-energy
vectors for arbitrary approximate inputs. It removes Gram shape as a
separate obstruction after that spectral count has been supplied.

## 1. Setting and notation

Let G have a finite symmetric Kazhdan generating set S, with `h=|S|`
and constant kappa in the convention

```text
dist(v,H^G)<=kappa^(-1) max_s ||pi(s)v-v||.
```

Let Q be any finite quotient and `Pi=lambda_Q` on `K=ell^2(Q)`: here
there is one copy of the regular representation before constructing
frames. Let `U_s` be arbitrary unitaries on `C^d`, with
`U_(s^-1)=U_s^*`. No defining-relator estimate is needed for the estimates
in Sections2--5. Define, on the unnormalized HS space `Hom(C^d,K)`,

```text
D_s(T)=Pi(s)T-TU_s,
Delta=(1/h)sum_s D_s^*D_s,
P_E=1_[0,epsilon^2](Delta),       E=range(P_E),
r=dim E>0.
```

For an HS-orthonormal basis `(T_a)` of E, put

```text
B=sum_a T_a^*T_a,       b=r/d,       H=B/b,
a_0=2h epsilon^2/kappa^2.
```

Assume `a_0<1`. All traces and HS norms until explicitly normalized are
unnormalized. In particular `Tr B=r` and `tr_d H=1`.

## 2. Schur orthogonality counts the invariant pair products exactly

The Laplacian and its full spectral projection commute with the right
regular Q-action. Decompose the regular representation as

```text
K=direct_sum_sigma V_sigma tensor C^(r_sigma),
r_sigma=dim sigma,
E=direct_sum_sigma E_sigma tensor C^(r_sigma),
mu_sigma=dim E_sigma,
r=sum_sigma r_sigma mu_sigma,
```

where `E_sigma` is a subspace of `Hom(C^d,V_sigma)`. Choose an
HS-orthonormal basis `W_(sigma,alpha)`, `1<=alpha<=mu_sigma`, of each
`E_sigma`. The corresponding basis of E is

```text
T_(sigma,alpha,l)=W_(sigma,alpha) tensor e_l,
1<=l<=r_sigma.
```

Let `mathcal E` denote orthogonal projection onto the invariants of
`Ad(Pi)` on `HS(K)`; it is the average over the finite quotient. For
two basis indices `a=(sigma,alpha,l)` and `b=(tau,beta,m)`, Schur's
lemma and the HS orthonormality give

```text
mathcal E(T_a T_b^*)=0
       unless sigma=tau and alpha=beta,
mathcal E(T_a T_b^*)=(I_(V_sigma)/r_sigma) tensor E_(l,m)
       when sigma=tau and alpha=beta.
```

The squared HS norm in the nonzero case is `1/r_sigma`. Summing over
all indices therefore gives exactly

```text
sum_(a,b) ||mathcal E(T_a T_b^*)||_HS^2
 =sum_sigma mu_sigma r_sigma^2/r_sigma=r.              (SP1)
```

On the other hand,

```text
sum_(a,b)||T_a T_b^*||_HS^2=Tr(B^2).
```

Orthogonality of the conditional expectation proves

```text
sum_(a,b)||T_a T_b^*-mathcal E(T_a T_b^*)||_HS^2
 =Tr(B^2)-r>=0.                                       (SP2)
```

## 3. Positive right multiplication is the missing weighted energy estimate

Set

```text
X_s=sum_a T_a^* Pi(s) T_a.
```

Expanding the pair-product commutators and cycling the trace gives the
exact identity

```text
sum_(a,b)||Pi(s)T_aT_b^*Pi(s)^*-T_aT_b^*||_HS^2
 =2(Tr(B^2)-||X_s||_HS^2).                            (SP3)
```

In particular each quantity in parentheses is nonnegative.

Define the positive operator `R_B` on the HS space by `R_B(T)=TB`.
Because P_E is a spectral projection,

```text
0<=Delta P_E<=epsilon^2 P_E.
```

Taking its trace against the positive operator R_B yields

```text
Tr_HS(R_B Delta P_E)
 <=epsilon^2 Tr_HS(R_B P_E)
 =epsilon^2 Tr(B^2).                                  (SP4)
```

No invariance of E under right multiplication by B is assumed or
needed here. Positivity and the spectral inequality justify the trace
bound even though R_B need not commute with P_E.

Symmetry of S and the inverse convention give

```text
Delta(T)=2T-(2/h)sum_s Pi(s)T U_s^*.
```

Expanding the left side of `(SP4)` in the basis of E consequently gives

```text
Tr_HS(R_B Delta P_E)
 =(1/h)sum_s [Tr(B^2)-||X_s||_HS^2+||X_s-BU_s||_HS^2]. (SP5)
```

For clarity, the two cross terms in the square are
`2 Re Tr(X_s^* B U_s)=2 Re Tr(B X_s U_s^*)`, by conjugation and
cyclicity. This is the order of multiplication required by the
Laplacian expansion.

Drop the final nonnegative squares in `(SP5)` and combine with `(SP3)`:

```text
sum_s sum_(a,b)||Ad(Pi(s))(T_aT_b^*)-T_aT_b^*||_HS^2
 <=2h epsilon^2 Tr(B^2).                              (SP6)
```

## 4. The resulting moment and soft-mass bounds

Apply the Kazhdan inequality to each pair product, square it, and sum.
The sum of generator maxima is at most the sum over all generators.
Using `(SP2)` and `(SP6)` gives

```text
Tr(B^2)-r <= a_0 Tr(B^2),
r<=Tr(B^2)<=r/(1-a_0).                                (SP7)
```

There is no dependence on the quotient index or dimension. Since
`(Tr B)^2<=d Tr(B^2)`, this also implies

```text
b<=1/(1-a_0),
tr_d(H^2)<=1/[b(1-a_0)].                              (SP8)
```

The elementary right-regular rank estimate gives `rank H<=r`: each
rank-one vector in `E_sigma` contributes a source partial trace of rank
at most r_sigma, and summing over its mu_sigma basis vectors and over
sigma gives the bound. Thus, for `K_soft=H(H+I)^(-1)`,

```text
tr_d K_soft<=rank(H)/d<=b.
```

Cauchy--Schwarz in the form
`1=(tr H)^2<=tr[H/(H+I)] tr[H(H+I)]` and `(SP8)` give the matching
positive lower bound

```text
b(1-a_0)/(1+b(1-a_0)) <=tr_d K_soft<=b.                (SP9)
```

For sequences with epsilon tending to zero, positive limit inferior of
the normalized spectral count `r/d` is therefore equivalent to positive
limit inferior of the soft mass. The mathematical content is the new
automatic moment bound `(SP7)--(SP8)`: positive count cannot hide in an
uncontrolled source Gram matrix for these full spectral spaces.

## 5. A compressed exact target and polar completion

The same Schur decomposition constructs the following exact G
representation on a space of dimension r:

```text
Theta=direct_sum_(sigma,alpha=1,...,mu_sigma) sigma,
T=col_(sigma,alpha) sqrt(r_sigma) W_(sigma,alpha)
      : C^d -> C^r.
```

It satisfies

```text
T^*T=B,
mathcal E_(Ad Theta)(TT^*)=I_r,
||TT^*-I_r||_HS^2=Tr(B^2)-r<=a_0 r/(1-a_0).            (SP10)
```

Indeed a block of TT* is
`sqrt(r_sigma r_tau) W_(sigma,alpha)W_(tau,beta)^*`.
Its invariant average is zero unless sigma=tau and alpha=beta, in
which case it is the identity on V_sigma. This proves the middle
identity. The norm identity also follows directly by expanding its
square, since `Tr(TT*)=r`.

The compressed map preserves the entire spectral energy ledger:

```text
sum_s ||Theta(s)T-TU_s||_HS^2 <=h epsilon^2 r.          (SP11)
```

For each `(sigma,alpha)`, its weighted term has coefficient r_sigma,
exactly accounting for the r_sigma right-regular basis copies in E.

Put

```text
xi=sqrt(h)epsilon+2sqrt(a_0/(1-a_0)).                  (SP12)
```

If `r<=d`, complete the polar partial isometry of T to a coisometry
`V:C^d->C^r`, so `VV*=I_r`. There is sufficient room for the missing
singular vectors because `d-rank(T)>=r-rank(T)`. For every singular
value x, `(x-1)^2<=(x^2-1)^2`, hence

```text
||T-V||_HS<=sqrt(a_0/(1-a_0)) sqrt(r),
max_s||Theta(s)V-VU_s||_HS<=xi sqrt(r).                 (SP13)
```

Let `J=V^*`, `P=JJ^*`, and let the exact representation on `P C^d` be
`W_s=J Theta(s)J^*`. Taking the adjoint residual in `(SP13)` and
multiplying by the unitaries U_s and Theta(s) gives

```text
rank(P)=r,
||U_sJ-JTheta(s)||_HS<=xi sqrt(r),
||U_sP-W_s||_HS<=xi sqrt(r),
||(I-P)U_sP||_HS<=xi sqrt(r).                          (SP14)
```

Also `||[P,U_s]||_HS<=sqrt(2)xi sqrt(r)`. The column estimate has no
additional square-root-of-two loss: if `R_s=Theta(s)V-VU_s`, then
`U_s R_s^* Theta(s)=U_sJ-JTheta(s)`, and right multiplication by
the coisometry `J^*` preserves its HS norm.

Thus there is an exact corner whose retained-column error and boundary
are `O_(h,kappa)(epsilon)` when normalized by its own rank. This is
independent of `r/d`, even if the corner has vanishing relative size.

If desired, polar-complete `(I-P)U_s(I-P)` on the complement and take
its direct sum with W_s. The total squared generator change is at most
`3xi^2 r`: the P-column error contributes at most `xi^2 r`, and the
complementary column contributes its off-diagonal mass plus its polar
deficiency, at most `2||(I-P)U_sP||_HS^2`. The complementary tuple is
not asserted exact.

Alternatively, `alpha_s=W_s+(I-P)` is exact on the whole original
space, since it is W direct sum the trivial representation. Orthogonal
input columns give the sharper estimate for this full exact replacement

```text
||alpha_s-U_s||_(2,d)^2<=xi^2 b+4(1-b).                 (SP14b)
```

Thus count b tending to one suffices for full same-dimensional
correction in the `r<=d` case.

If `r>d`, instead append r-d zero columns to T and append r-d identity
coordinates to each U_s. The same polar completion is now a unitary
`V:C^r->C^r`. Set `alpha(s)=V^*Theta(s)V`. Equations `(SP10)--(SP13)`
give a full exact correction with

```text
(r-d)/d<=a_0/(1-a_0),
max_s||alpha(s)-(U_s direct_sum I_(r-d))||_(2,r)<=xi.    (SP15)
```

The case r=d may be read in either construction and gives a full
same-dimensional correction. These conclusions require no soft
threshold, Gaussian compression, or subgroup-index estimate.

## 6. Deterministic sublinear seeds retain the linear error rate

The target Theta has multiplicity mu_sigma in type sigma. Its exact
smallest embedding multiplicity into copies of the same quotient
regular representation is

```text
k=max_(mu_sigma>0) ceil(mu_sigma/r_sigma).
```

Choose any multiplicity-space isometries realizing the exact equivariant
embedding

```text
L:C^r ->ell^2(Q) tensor C^k,
(Pi(s) tensor I_k)L=L Theta(s).
```

In the `r<=d` case, the original-space partial frame `F=L V` has

```text
F^*F=P,
max_s ||(Pi(s) tensor I_k)F-FU_s||_HS/sqrt(d)<=xi sqrt(b).
                                                               (SP19)
```

On the recovered corner, `F|_P` is exactly Parseval and exactly
equivariant for W. Relative to the unitary polar compression Z_s of
`PU_sP`, its edge error normalized by r is at most `2xi`: both
`W_s-PU_sP` and `Z_s-PU_sP` have HS norm at most `xi sqrt(r)`.
In the `r>d` case the same formula `F=L V`, with V the padded unitary,
is exactly Parseval on the padded space, and its edge error relative to
`U_s direct_sum I` is at most xi.

For canonical asymptotic SL5 inputs and `liminf r_j/d_j>0`, these
multiplicities satisfy `k_j=o(d_j)`, hence also `o(r_j)`. Indeed the
exact Theta_j are canonical: use the positive-fraction exact-corner
character argument in the `r<=d` case, and the full correction
`(SP15)` with vanishing relative padding in the `r>d` case. Every fixed
finite-dimensional type has vanishing relative mass in such a canonical
sequence, by the Kazhdan tensor test in the universal-host artifact.
There are only finitely many SL5 types below each fixed dimension M.

For high types `r_sigma>=M`,

```text
mu_sigma/(r_sigma d)<=r/(r_sigma^2 d)<=b/M^2.
```

For each of the finitely many low types, `mu_sigma/d->0`. Thus the
maximum defining k, divided by d, has limit superior at most `1/M^2`,
using `b<=1+o(1)` from `(SP8)`. Let M tend to infinity. This proves
sublinearity. Unlike Gaussian compression, the exact multiplicity
embedding adds no Gram error and loses no epsilon-rate.

## 7. Optional projection form of the Gram rigidity

Here is a direct form useful for examining source geometry. Let
`F=col_a T_a` and let the block matrix indexed by the basis of E be

```text
Z_(a,b)=T_aT_b^*-mathcal E(T_aT_b^*).
```

The Schur formulas in Section2 show

```text
F^* [mathcal E(T_aT_b^*)]_(a,b) F=B,
F^* Z F=B^2-B,
||Z||_HS^2=Tr(B^2)-r.
```

In the first identity, for fixed sigma and alpha the r_sigma squared
choices of right indices contribute
`r_sigma W_(sigma,alpha)^*W_(sigma,alpha)`, exactly its term in B.
Trace-norm duality and Hilbert--Schmidt Cauchy--Schwarz yield

```text
||B^2-B||_1
 <=sqrt(Tr(B^2)) sqrt(Tr(B^2)-r)
 <=sqrt(a_0) r/(1-a_0).                               (SP16)
```

For the first inequality, test `F^*ZF` against a source unitary U and
use `||FUF^*||_HS^2=Tr(U^*BU B)<=Tr(B^2)`.

Let `Q_B=1_[1/2,infinity)(B)`. The scalar bound
`|x-1_[1/2,infinity)(x)|<=2|x^2-x|`, for `x>=0`, gives

```text
||B-Q_B||_1<=2sqrt(a_0) r/(1-a_0).                     (SP17)
```

In particular `rank Q_B=r(1+O(sqrt(a_0)))`. The resolvent identity
makes `f_b(X)=X(X+bI)^(-1)` trace-norm Lipschitz with constant 1/b on
positive matrices. Since `K_soft=f_b(B)` and
`f_b(Q_B)=Q_B/(1+b)`, `(SP17)` implies the explicit asymptotic formula

```text
|tr_d K_soft-b/(1+b)|<=4sqrt(a_0)/(1-a_0).              (SP18)
```

Thus the soft mass is asymptotically determined by the normalized
spectral count; this is stronger than merely bounding its second moment.

## 8. What the estimate does not supply

These arguments do not give a positive lower bound on r/d. This is a
real cutoff issue even for inputs already close to exact ones. Take one
untwisted canonical exact block rho_j and a_j copies of the same block
with generator phases `exp(i t_j x_s)`, where `t_j->0`, `a_j->infinity`,
and some defining relator has nonzero phase exponent. Use a universal
quotient containing rho_j. The twisted part has no exact intertwiner
into any genuine representation, by evaluating that relator.

At the zero-energy space, or a positive cutoff below the first positive
eigenvalue, E consists exactly of intertwiners from the untwisted block.
Then `b=1/(a_j+1)->0`, B is the source projection onto that block, and
`Tr(B^2)=r`. Every pair-product commutator in `(SP6)` is zero. Choosing
strictly positive cutoffs that also tend to zero is possible since each
finite-dimensional positive spectral gap is nonzero.

Enlarging the cutoff resolves this particular example. It is not a
counterexample to the existence of a suitable cutoff or to flexible
stability. It demonstrates that pair-product rigidity alone cannot
supply the missing low-energy count.

For canonical approximate SL5 inputs, a count `r/d` bounded below now
gives positive-fraction exact corners directly by `(SP13)--(SP14)`;
their canonicality follows from asymptotic centrality and ICC whenever
their relative dimension stays positive. If r exceeds d, `(SP15)`
already gives full flexible correction. Establishing adequate spectral
count for suitable quotient hosts and thresholds remains the arithmetic
existence step.

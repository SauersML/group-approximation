# Positive soft Schreier mass gives a quantitative exactifiable corner

This strengthens the sufficient condition in
`second-moment-schreier-positive-corner-2026-09-05.md`. A fixed positive
soft Gram mass suffices; a bounded second moment is unnecessary for this
construction. Soft normalization makes the entire frame a contraction,
and spectral coarea selects the corner with an explicit boundary bound.

The arithmetic existence of the needed soft mass is not proved here.

## 1. Exact hypotheses and conclusions

Let `G=SL_5(Z)`, with symmetric finite Kazhdan generating set S,
`h=|S|`, and constant kappa in the MSC convention. Let `U_(j,s)` be
canonical asymptotic unitary representations on `C^(d_j)`, with
`U_(j,s^-1)=U_(j,s)^*`. Let `Q_j`
be finite quotients of G, and let `Pi_j=lambda_(Q_j)`. They may be the
universal quotients at the dimension bound `2d_j`.

On `Hom(C^(d_j),ell^2(Q_j))`, use unnormalized HS inner product and set

```text
D_s(T)=Pi_j(s)T-TU_(j,s),
Delta_j=(1/h)sum_s D_s^*D_s,
E_j=range 1_[0,epsilon_j^2](Delta_j),       epsilon_j->0.
```

Assume these full spectral spaces are nonzero. For an orthonormal basis
`(T_a)` define, independently of the choice of basis,

```text
r_j=dim E_j,       b_j=r_j/d_j,
B_j=sum_a T_a^*T_a,       C_j=sum_a T_a T_a^*,
H_j=B_j/b_j,
K_j=H_j(H_j+I)^(-1),
K_eff,j=Tr(C_j^2)/(b_j^2 d_j).
```

The sufficient hypothesis is that there exists a fixed `0<c<1` such
that eventually

```text
tr_(d_j)(K_j)>=c.                                      (SS1)
```

For every sufficiently large j, the construction below selects a
projection `P_j` with `n_j=rank(P_j)` and

```text
theta_j=n_j/d_j>=c/2.
```

The unitary polar compressions `W_(j,s)` on `P_j C^(d_j)` are canonical
asymptotic representations. They admit exact flexible corrections on
dimensions `D_j>=n_j`, with the explicit bounds in Section4. They also
admit rectangular MSC frames with trivial subgroup seeds of dimension
`o(d_j)` and vanishing Gram and edge errors, as proved in Section5.

No subsequence is needed to choose the projections. The assertion holds
whenever `(SS1)` holds eventually. Equivalently, a positive limit inferior
of the displayed soft mass suffices by choosing c below that limit
inferior and discarding finitely many terms.

## 2. Soft normalization bounds the full frame and its Gram commutator

Suppress the index j. Stack the spectral basis and regularize:

```text
F_0=b^(-1/2) col_a T_a,
F=F_0(H+I)^(-1/2),
F^*F=K=H(H+I)^(-1),       ||F||_op<=1.
```

By low energy and the rectangular soft-polar estimate proved in
`low-energy-schreier-frame-construction-2026-09-05.md`,

```text
sum_s ||Pi^direct_sum(s)F-FU_s||_HS^2/d <=2h epsilon^2.  (SS2)
```

Write the generator residuals as `R_s`. Both maps `Pi(s)F` and `FU_s`
are contractions. Expanding the difference of their Gram matrices gives

```text
||U_s^* K U_s-K||_(2,d)<=2||R_s||_HS/sqrt(d).
```

Summing this estimate and using Cauchy--Schwarz in S yields

```text
sum_s ||[K,U_s]||_(2,d)<=2sqrt(2) h epsilon.             (SS3)
```

This is a Hilbert--Schmidt commutator estimate for the bounded Gram
matrix, rather than a trace-norm estimate for the possibly unbounded H.

## 3. Coarea chooses a positive-fraction corner with a quantitative boundary

For `0<=t<=1` put `P_t=1_[t,1](K)`. In an eigenbasis of K,

```text
integral_0^1 ||[P_t,U]||_(2,d)^2 dt
 =(1/d)sum_(i,l) |lambda_i-lambda_l| |U_(il)|^2
 <= ((1/d)sum_(i,l) |lambda_i-lambda_l|^2 |U_(il)|^2)^(1/2)
 =||[K,U]||_(2,d).                                     (SS4)
```

The Cauchy--Schwarz factor omitted from the second line is
`((1/d)sum |U_(il)|^2)^(1/2)=1`.

Sum `(SS4)` over S, use `(SS3)`, and average over the interval
`[c/4,c/2]`, whose length is `c/4`. There exists a threshold in that
interval such that, for `P=P_t`,

```text
max_s ||[P,U_s]||_(2,d)^2
 <=sum_s ||[P,U_s]||_(2,d)^2
 <=A_j,       A_j=8sqrt(2) h epsilon_j/c.               (SS5)
```

No spectral continuity assumption is needed; a threshold can be chosen
outside the finitely many eigenvalues if desired. As `0<=K<=I` and
`tr K>=c`,

```text
c<=tr K<=tr P+t tr(I-P),
theta=tr P>=(c-t)/(1-t)>=c/2.                          (SS6)
```

Also `tP<=PKP<=P` and `t>=c/4`.

Let `W_s` be a unitary polar completion of `P U_s P` on `P C^d`, with
inverse symbols chosen consistently. Write
`ell_s=||(I-P)U_sP||_(2,d)`. The two off-diagonal blocks of a unitary
have equal HS mass, so `2ell_s^2=||[P,U_s]||_(2,d)^2`. The usual square
contraction polar estimate gives

```text
||P U_s P-W_s||_(2,d)<=ell_s,
||U_sP-PW_s||_(2,d)<=sqrt(2)ell_s<=sqrt(A_j).            (SS7)
```

## 4. The globally bounded frame gives a quantitative correction

The restricted map `FP:P C^d->ell^2(Q)^direct_sum r` has Gram matrix `PKP|_P` with
minimum eigenvalue at least t. Since the entire F is a contraction,

```text
Pi^direct_sum(s)FP-FP W_s
 =R_sP+F(U_sP-PW_s)
```

has original-normalized HS norm at most

```text
e_j=sqrt(2h)epsilon_j+sqrt(A_j).                        (SS8)
```

There is no uncontrolled contribution from the discarded subspace.
Now take the polar isometry

```text
J_0=FP(PKP|_P)^(-1/2).
```

The rectangular polar map is HS Lipschitz with constant `1/sqrt(t)`
on maps with minimum singular value at least `sqrt(t)`. Applying this
to `Pi(s)FP` and `FPW_s`, and then normalizing by the selected dimension
`n=theta d`, gives

```text
beta_0:=max_s ||Pi^direct_sum(s)J_0-J_0 W_s||_HS/sqrt(n)
 <=e_j/sqrt(t theta)
 <=(2sqrt(2)/c)(sqrt(2h)epsilon_j+sqrt(8sqrt(2)h epsilon_j/c)).
                                                               (SS9)
```

This exact isometry alone is already an MSC input in a genuine finite
ambient representation, with no Gram error. Therefore the corrected
representation can be chosen with

```text
(D_j-n_j)/n_j <=4 beta_0^2/kappa^2,
max_s ||alpha_j(s)-(W_(j,s) direct_sum I)||_(2,D_j)
 <=(1+10/kappa)beta_0.                                 (SS10)
```

For `epsilon_j<=1`, `(SS9)` is in particular
`O_h(sqrt(epsilon_j)/c^(3/2))`. The corresponding relative padding
bound is `O_(h,kappa)(epsilon_j/c^3)`. These quantitative statements use
the stacked isometry; its subgroup-seed multiplicity is unrestricted.

Fixed-word telescoping in `(SS7)` shows that W is asymptotically
multiplicative. Its limiting traces are canonical: P asymptotically
commutes with the original tuple, and its dimension fraction is bounded
below by c/2. Any convergent subsequence of the corner traces and
fractions splits the original regular character into a convex combination
of corner characters. The regular character is extremal for ICC
`SL_5(Z)`, so each positive-fraction corner character is regular. If the
complementary fraction tends to zero, its trace contribution vanishes.
The detailed ICC and corner argument is given in Section5 of the
second-moment artifact. It applies to every convergent subsequence here,
and thus proves canonical convergence for the chosen full sequence.

## 5. Sublinear seed dimensions are available, with an asymptotic error bound

The right-regular invariance of the full spectral space gives
`rank H<=r`, as proved in the low-energy frame artifact. Since K is a
positive contraction supported on H,

```text
c<=tr K<=rank(H)/d<=r/d=b.                             (SS11)
```

Consequently the canonical effective-covariance theorem `(LF8)` applies:

```text
K_eff,j/d_j ->0.
```

Write `J_0=col_a S_a`. Whitening simplifies exactly on the selected
spectral subspace:

```text
(H+I)^(-1/2) P(PKP|_P)^(-1/2)=P(H|_P)^(-1/2).
```

As K has eigenvalues at least t on P, H has eigenvalues at least
`t/(1-t)` there. It follows that

```text
C_sel=sum_a S_a S_a^* <= C/(bt),
Tr(C_sel^2)/n <= K_eff/(t^2 theta)<=32 K_eff/c^3.        (SS12)
```

Apply the Gaussian compression identities `(LF3)--(LF5)` to J_0,
using k fibres. There is a realization with

```text
zeta <=2sqrt(K_eff/(t^2 theta k)),
beta <=2sqrt(h/(t theta)) e_j.                         (SS13)
```

Choose `k_j=ceil sqrt(d_j max(1,K_eff,j))`. Then `k_j=o(d_j)` and
`K_eff,j/k_j->0`, so `(SS13)` gives `zeta_j,beta_j->0`. The subgroup
representation is trivial of dimension k_j. Since `n_j>=cd_j/2`, these
seed dimensions are also `o(n_j)`.

MSC again gives exact flexible corrections. This compressed construction
has vanishing error, but without a rate relating `K_eff,j/d_j` to
epsilon_j its Gram error need not have the explicit epsilon-rate in
`(SS9)--(SS10)`. The quantitative stacked construction and the sublinear
seed conclusion are deliberately kept distinct.

## 6. Relation to the second-moment hypothesis

Since `tr H=1`, Cauchy--Schwarz gives

```text
1=(tr H)^2
 <=tr(H(H+I)^(-1)) tr(H(H+I))
 =tr K (tr H^2+1).
```

Thus `tr H^2<=M` implies

```text
tr K>=1/(M+1).                                        (SS14)
```

The soft-mass condition tolerates large second moments. For example,
the abstract positive matrices with eigenvalues `(d+1)/2` once and
`1/2` with multiplicity `d-1` have normalized trace one, second moment
`d/4+3/4` tending to infinity, but soft mass tending to `1/3`. This is
an illustration of the difference between the two operator conditions,
not an assertion that these particular matrices arise from a given
Schreier spectral space.

What remains unproved is the following input to this construction:
for arbitrary canonical approximate SL5 tuples, choose finite quotient
hosts and cutoffs epsilon_j tending to zero whose full spectral Gram
matrices have positive soft mass as in `(SS1)`. No claim that QRC5
already supplies this input is made.

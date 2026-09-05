---
rg: 2
id: moving-schreier-induction-original-rank-proof
kind: route
title: Normalize the induced corner by its original rank and retain orthogonality at the spectral cut
target: moving-subgroup-schreier-correction-has-no-index-loss
requires:
  - residual-finite-regularization-removes-the-weak-ucp-quantifier
artifacts:
  - research/artifacts/quadratic-curvature-flexible-dilation-2026-09-05.md
  - research/artifacts/rectangular-seed-quotient-alignment-2026-09-05.md
  - research/artifacts/universal-dimension-schreier-host-2026-09-05.md
  - research/artifacts/low-energy-schreier-frame-construction-2026-09-05.md
  - research/artifacts/second-moment-schreier-positive-corner-2026-09-05.md
  - research/artifacts/positive-canonical-corners-bootstrap-stability-2026-09-05.md
---

Let `H=C^d`, `K=direct_sum_(t in T) H`, and form the exact induced
representation

```text
Pi(g)(delta_t tensor xi)=delta_(t') tensor pi(n(g,t))xi,
g t=t' n(g,t).
```

This is genuine for any subgroup: if `h t=t_1 n_1` and
`g t_1=t_2 n_2`, then `(gh)t=t_2 n_2 n_1`, exactly the multiplication
rule needed for `Pi(g)Pi(h)=Pi(gh)`.

Define an isometry and its range projection by

```text
W:H->K,       W xi=m^(-1/2) sum_t delta_t tensor V_t^*xi,
P=WW^*,       rank(P)=d.
```

For every `s`, block orthogonality gives the exact equality

```text
||Pi(s)W-WU_s||_HS^2/d
 =(1/m)sum_t ||pi(n(s,t))V_t^*-V_(t')^* U_s||_(2,d)^2
 =(1/m)sum_t ||U_s V_t-V_(t')pi(n(s,t))||_(2,d)^2.        (MSP1)
```

All norms on maps into `K` below are unnormalized HS norms divided by
`sqrt(d)`, not by `sqrt(dim K)`.  Put `R_s=Pi(s)W-WU_s`.  Since `P`
and its unitary conjugate have the same finite rank,

```text
||Pi(s)P Pi(s)^*-P||_HS^2
 =2||(1-P)Pi(s)W||_HS^2
 <=2||R_s||_HS^2 <=2 beta^2 d.                          (MSP2)
```

Let `E` be orthogonal projection in `HS(K)` onto the invariant subspace
of the genuine conjugation representation `Ad(Pi)`.  Property `(T)` gives

```text
a:=||P-E(P)||_HS <= sqrt(2) beta sqrt(d)/kappa.           (MSP3)
```

The operator `Z=E(P)` is a positive contraction: it is the limit of lazy
averages of unitary conjugates of `P`.  Put `Q=1_[1/2,1](Z)`.
Spectral cutoff is a best approximation to `Z` among orthogonal
projections in HS norm.  Indeed in an eigenbasis of `Z`, the expression
`||Z-R||_HS^2=Tr(Z^2)+Tr(R)-2Tr(ZR)` is minimized by including exactly
the eigenvectors with eigenvalues at least `1/2`.  Thus
`||Z-Q||_HS<=||Z-P||_HS=a`.

Both `Z` and `Q` are invariant.  Therefore `P-Z` is HS-orthogonal to
`Z-Q`, which improves the usual triangle-inequality estimate to

```text
h^2:=||P-Q||_HS^2
 =||P-Z||_HS^2+||Z-Q||_HS^2
 <=2a^2 <=4 beta^2 d/kappa^2.                           (MSP4)
```

Write `d'=rank(Q)`.  For two projections,

```text
|d'-d| <= d'+d-2Tr(PQ)=h^2.                            (MSP5)
```

The subspace `QK` carries an exact representation.  If `d'<d`, add
`d-d'` copies of the trivial representation.  Denote the resulting invariant
space by `K_0`, its representation by `alpha`, and its dimension by
`D=max(d,d')`.  The padding used at this stage is on an auxiliary summand
orthogonal to `K`, and `0<=D-d<=h^2`.

Extend the polar part of `QW` to an isometry `J:H->K_0`.  This is possible
because `D>=d`.  On the kernel of `QW` choose the missing orthonormal
vectors in `K_0`; they are orthogonal to the corresponding vectors in
`WH`, because those vectors are orthogonal to `QK` and to the auxiliary
padding.  If `lambda_1,...,lambda_d` are the eigenvalues of `W^*QW`,
this choice gives

```text
||J-W||_HS^2
 =2 sum_i(1-sqrt(lambda_i))
 <=2 sum_i(1-lambda_i)
 =2(d-Tr(PQ)) <=2h^2.                                  (MSP6)
```

Regard `W` and `J` as maps into the common enlarged ambient space and
extend `Pi` there by the same trivial representation.  From `(MSP1)` and
`(MSP6)`,

```text
||alpha(s)J-JU_s||_HS
 <=||R_s||_HS+2||J-W||_HS
 <=(1+4sqrt(2)/kappa) beta sqrt(d).                      (MSP7)
```

Identify `JH` with the original `C^d` inside `K_0`.  On its orthogonal
complement the desired padded tuple is the identity.  The two maps
`alpha(s)` and that identity padding have HS norm at most `sqrt(D-d)`
on this complement.  The triangle inequality and `(MSP7)` give

```text
||alpha(s)-(U_s direct_sum I_(D-d))||_HS
 <=(1+4sqrt(2)/kappa) beta sqrt(d)+2sqrt(D-d)
 <=(1+(4sqrt(2)+4)/kappa) beta sqrt(d).
```

Since `D>=d` and `4sqrt(2)+4<10`, division by `sqrt(D)` proves `(MSC2)`.
No step introduced a factor involving `m`, nor was a normal core taken.

The induced representation extends to a unital star representation of
`C^*(G)`, and the compression `Phi(x)=W^*Pi(x)W` is ucp because `W` is
an isometry.  Computing its coset blocks gives `(MSC5)`.  Each summand of
`Phi(s)` is unitary; expanding its squared distance from `U_s` and
averaging gives the equality in `(MSC6)`.  The inequality follows from
the triangle inequality followed by Cauchy--Schwarz for the uniform coset
average (or directly by compressing `(MSP1)`).

For `(MSC3)`, relator telescoping and subgroup-word telescoping give each
edge error at most `A_(s,t)delta+ell_(s,t)xi`.  Apply the triangle
inequality in `ell^2(T)` with probability measure `1/m`, then maximize
over `s`.  Finally `(MSC4)` follows by contraposition from `(MSC2)`:
a smaller `beta` than both displayed thresholds produces an exact padded
representation inside both the prescribed dimension and distance budgets.

For the rectangular assertion `(MSC7)`, induce the genuine k-dimensional
representation on `K=direct_sum_T C^k` and stack the frame maps into

```text
J_0:C^d->K,       J_0 x=sum_t delta_t tensor A_t x.
```

Then `J_0^*J_0=H`, and block orthogonality gives exactly

```text
max_s||Pi(s)J_0-J_0 U_s||_HS/sqrt(d)=beta_rect.
```

If dim K is below d, enlarge K by d-dim K trivial representation
dimensions and extend J_0 by zero. This leaves H and the displayed
intertwining errors unchanged. The ambient dimension is now at least d,
so the polar partial isometry of J_0 extends on its kernel to an isometry
`J_1:C^d->K`. With lambda_i the nonnegative eigenvalues of H,

```text
||J_1-J_0||_HS^2
 =sum_i(sqrt(lambda_i)-1)^2
 <=sum_i|lambda_i-1|=d zeta.
```

No invertibility of H is used. Since Pi(s) and U_s are unitaries,

```text
max_s||Pi(s)J_1-J_1 U_s||_HS/sqrt(d)
 <=beta_rect+2sqrt(zeta)=gamma.
```

The proof from `(MSP2)` onward uses only an isometry from dimension d,
a genuine ambient representation, and this intertwining bound. Apply it
with W=J_1 and beta=gamma; it gives exactly the claimed final padding
and generator estimates. Compression by J_1 also gives a ucp map with
generator error at most gamma.

Finally rank(H)<=mk before the auxiliary enlargement, so at least
max(0,d-mk) eigenvalues of H are zero. Their contribution to
`||H-I||_(1,d)` proves the stated capacity lower bound. The construction
normalizes the stacked frame once, rather than separately rounding every
fibre to a unitary; there is no hidden square-fibre or common-range
assumption. Exact seed holonomy and the two error bounds remain explicit
inputs to the construction.

To prove `(MSC8)`, let rho be genuine and use the genuine representation
`T -> Pi(g)T rho(g)^*` on the rectangular HS space. Project J_0
orthogonally onto its invariant subspace, obtaining an intertwiner T_0.
The Kazhdan bound gives

```text
||J_0-T_0||_HS^2<=beta_rect^2 d/kappa^2.
```

Schur decomposition gives rank(T_0)<=R. If E is projection onto its
kernel, rank(E)>=d-R, and trace duality gives

```text
||J_0-T_0||_HS^2>=||(J_0-T_0)E||_HS^2
 =Tr(EH)>=rank(E)-||H-I||_1>=d-R-d zeta.
```

This proves the bound. Conversely, when R=d choose an equivariant
isometry into Pi and use its coordinate maps as the frame. Frobenius
reciprocity gives the displayed multiplicity criterion.

For a nearby tuple, put B_s=U_s-rho(s). Unitarity gives
`||B_s||_op<=2`, hence

```text
||J_0 B_s||_HS^2=Tr(H B_s B_s^*)
 <=||B_s||_HS^2+4||H-I||_1<=d(eta^2+4zeta).
```

The triangle inequality reduces this to the exact-input estimate with
the claimed replacement for beta_rect. No bound on `||J_0||_op` is used.

For the congruence example, reduction `Gamma(q)->SL_5(F_p)` is surjective
when p and q are coprime: choose an integer coefficient zero modulo q
and equal to any desired scalar modulo p, and use its elementary matrix.
Consequently the irreducibles of the quotient remain irreducible and
pairwise inequivalent on Gamma(q). Their multiplicities a_sigma in the
seed obey `sum dim(sigma) a_sigma<=k`. Frobenius reciprocity gives
`m_Pi(sigma)=a_sigma`, so R<=k. At Gamma(p), induction of the trivial
seed is the regular quotient representation itself. Coordinate rows
`A_t x=x_t` obey both `sum A_t^*A_t=I` and
`A_(t')rho(s)=A_t` for every Schreier transition. Restriction to the
mean-zero input keeps these equalities and the coprime bound. The linked
artifact records the canonical trace limits as p tends to infinity.

For `(MSC9)`, fix a genuine d-dimensional representation of `SL_5(Z)`.
Each root C=rho(e_ij(1)) is the central commutator of
`A_l=rho(e_il(1))`, `B_l=rho(e_lj(1))` for any of the three spare indices
l. Its eigenspace of eigenvalue lambda is invariant under these operators.
Taking determinants there shows that lambda has finite order h dividing
the eigenspace dimension. The three A_l commute, the three B_l commute,
and `[A_l,B_m]=C^(delta_lm)`. Joint A_l eigenspaces are therefore permuted
by independent multiplication of their three eigenvalues by lambda.
Each orbit has h^3 distinct weights of equal multiplicity. Thus h^3
divides the C-eigenspace dimension and h^3<=d<=D.

Every root image consequently has order dividing q_D. The kernel contains
every e_ij(a q_D) and their normal closure. Bass--Milnor--Serre, §4 and
Corollary 4.3(a),(b), identifies this normal closure inside `SL_5(Z)`
with Gamma(q_D), for every integer level including even levels. The
linked artifact gives the primary citation and verifies its exact
normal-closure convention. This proves factorization through Q_D.

Inducing a trivial k-dimensional seed from N_D gives
`lambda_(Q_D) tensor I_k`. Each irreducible sigma of Q_D appears with
multiplicity `k dim(sigma)`. Schur decomposition therefore proves the
exact minimum in `(MSC9)`. Choose isometries of the input multiplicity
spaces into those of this induced representation to construct an
equivariant isometry J, and take its coset coordinate rows A_t. These
give an exact Parseval frame and exact Schreier edge equations.

For completeness, the sublinear assertion requires a spectral argument.
Fix an irreducible sigma of dimension r and a sequence rho_j with
regular limiting normalized character. Put
`theta_j=rho_j tensor conjugate(sigma)`. For any genuine theta let

```text
L_theta=(I+(1/|S|)sum_s theta(s))/2,
c=kappa^2/(4|S|).
```

These are positive contractions, with spectrum on invariant complements
bounded above by 1-c: expand their quadratic forms as
`sum_s||theta(s)v-v||^2/(4|S|)` and apply the Kazhdan inequality.
For each positive integer a, the invariant multiplicity obeys

```text
m_j(sigma)/(d_j r)<=tr_(d_j r)(L_theta_j^a).
```

The finite word expansion and convergence of normalized characters make
the right side tend to `tau_G(L_lambda^a)`. The infinite group's regular
representation has no invariant vector, so this is at most `(1-c)^a`.
Let j tend to infinity and then a tend to infinity. It follows that the
isotypic fraction `m_j(sigma)r/d_j` tends to zero.

Only finitely many irreducibles have dimension below any fixed M: the
first part puts them all in the finite quotient Q_M. Thus their total
dimension fraction epsilon_(j,M) tends to zero. Also d_j tends to
infinity, since bounded dimensions would force every representation to
kill the same nonidentity root e_12(q_D), contrary to the canonical limit.
The exact multiplicity formula now gives

```text
k_min(rho_j)/d_j
 <=max(epsilon_(j,M),1/M^2)+1/d_j.
```

For large-dimensional constituents use `m_sigma dim(sigma)<=d_j`; for
the others use their total fraction epsilon_(j,M). Let j tend to
infinity and then M tend to infinity. This proves sublinearity without
discarding any sector. Finally, because the constructed J is an isometry,
replacing rho(s) by U_s changes its intertwining error by exactly
`||U_s-rho(s)||_(2,d)`, proving the nearby-input assertion.

For `(MSC10)`, stack the low-energy basis into
`F_0=b^(-1/2) col_a T_a`. Its Gram matrix is H and its summed squared
edge error, normalized by d, is at most `h epsilon^2`. The equivariant
map `F -> F(F^*F+tau I)^(-1/2)` is HS Lipschitz with constant at most
`sqrt(2/tau)`. This follows by applying the scalar Lipschitz function
`x/sqrt(x^2+tau)` to the Hermitian block dilation of F and expanding in
two spectral bases. The soft polar frame therefore has Gram defect
`tr_d[tau(H+tau I)^(-1)]`, summed squared edge error at most
`2h epsilon^2/tau`, and target covariance at most `C/(b tau)`.

For any stacked frame `F=col_a S_a`, compress its multiplicity to k by
independent standard complex Gaussian combinations
`J=k^(-1/2) col_l(sum_a g_(la) S_a)`. Wick's two pairings give

```text
E(J^*J)=F^*F,
E ||J^*J-F^*F||_(2,d)^2
 =Tr((sum_a S_a S_a^*)^2)/(k d).
```

The expected summed squared edge error is unchanged. Applying Markov's
inequality with factor four to both quantities simultaneously gives the
two bounds in `(MSC10)` with positive probability. The coset coordinate
rows of J are the required Schreier frame. Quotient size never multiplies
either error.

To prove automatic sublinear covariance, let P_E be the full spectral
projection. The unitary `A_s(T)=Pi(s)T U_s^*` satisfies
`||(A_s-I)P_E||_HS<=sqrt(h) epsilon sqrt(r)`. Hence
`||A_s P_E A_s^*-P_E||_1<=2sqrt(h) epsilon r`. Partial trace onto the
target gives the same bound on `Pi(s)C Pi(s)^*-C`. Since `0<=C<=dI`,
the latter difference has squared HS norm at most `2sqrt(h) epsilon d r`.
Apply property (T) to the genuine conjugation representation on the
target HS space. Its invariant projection C_0 obeys

```text
Tr(C^2)=Tr(C_0^2)+||C-C_0||_HS^2,
||C-C_0||_HS^2<=2sqrt(h) epsilon d r/kappa^2.
```

Right regular invariance of the full spectral space gives
`P_E=direct_sum_sigma P_sigma tensor I_(r_sigma)`, where
`r_sigma=dim sigma`, `mu_sigma=rank P_sigma`, and
`sum r_sigma mu_sigma=r`. Its centralized target covariance is
`C_0|sigma=(mu_sigma/r_sigma)I_(r_sigma^2)`. Therefore

```text
K_eff/d<=sum_sigma mu_sigma^2/(b^2 d^2)
          +2sqrt(h) epsilon/(kappa^2 b).
```

For each fixed sigma, consider `L_(j,sigma)=I-Delta_(j,sigma)/4`, a
positive contraction. On its low-energy space it is at least
`1-epsilon_j^2/4`. For every fixed positive integer a,

```text
mu_(j,sigma)/(r_sigma d_j)
 <=(1-epsilon_j^2/4)^(-a) tr_(r_sigma d_j)(L_(j,sigma)^a).
```

Canonical fixed-word moments make the trace converge to the lazy regular
averaging trace, bounded by `(1-kappa^2/(4h))^a`. Let j tend to infinity
and then a tend to infinity. Thus `mu_(j,sigma)/d_j->0`. By `(MSC9)`,
only finitely many irreducible types have dimension below any fixed R;
their contribution vanishes when b is bounded below. The remaining
contribution is at most `1/R^2`. This proves `K_eff/d->0`.

Right invariance also gives `rank B<=r`: on the conjugate source,
`overline(B)=sum_sigma r_sigma Tr_(V_sigma)(P_sigma)`, and each partial
trace has rank at most `r_sigma mu_sigma`. Thus soft coverage forces
`liminf b_j>=1`. Choose tau_j decreasing slowly enough that the soft Gram
defect, `epsilon_j^2/tau_j`, and `K_eff,j/(tau_j^2 d_j)` all vanish, then
take `k_j=ceil sqrt(d_j max(1,K_eff,j/tau_j^2))`. This proves the full
coverage conclusion. The linked low-energy artifact records all details
and an exact-plus-small-phase example showing why an arbitrarily tiny
spectral cutoff can miss half the input even for correctable tuples.

For `(MSC11)`, the second moment and `rank H<=r` imply `b>=1/M`.
Partial trace of the same projection displacement onto the source gives

```text
a_j=max_s ||U_s^*H U_s-H||_(1,d)<=2sqrt(h) epsilon_j.
```

Choose a subsequential limiting spectral measure of H and its continuity
points `t in (1/8,1/4)` and `L in (4M,8M)`. Set `P=1_[t,L](H)`.
The portions below t and above L contribute at most t and M/L to tr H.
Consequently `theta=tr P>1/(2L)>1/(16M)`. This spectral projection
asymptotically commutes with U. Indeed `(H+I)^(-1)` has squared normalized
HS displacement at most a_j; continuous approximation to the interval
indicator at its continuity endpoints proves the assertion.

Write `F=F_0`, `Q=I-P` and
`ell_j=max_s ||Q U_s P||_(2,d)->0`. The required leakage estimate retains
the unbounded part of H rather than silently bounding all of F:

```text
||F Q U_s P||_(2,d)^2
 <=a_j+L ||P U_s Q||_(2,d)^2
 =a_j+L ||Q U_s P||_(2,d)^2.
```

Expand its trace as `tr(PU_s^*HU_sP)-tr(PU_s^*PHPU_sP)`; the first
term is at most `tr(PH)+a_j`, and the second is at least
`tr(PH)-L tr(PU_sQU_s^*P)`. Let W_s be consistent unitary polar
completions of `PU_sP`. Their compression errors are at most ell_j.
The restricted frame FP then has edge error at most
`e_j=sqrt(h)epsilon_j+sqrt(a_j)+2sqrt(L)ell_j` in the original normalization.

Since `tP<=PHP<=LP`, polar whitening FP gives an exact isometry with
edge error at most `e_j/sqrt(t theta)`, normalized by `n=rank P`.
This uses the HS Lipschitz constant `1/sqrt(t)` for polar factors of
full-rank maps whose least singular value is at least `sqrt(t)`.
For its component covariance, positivity gives
`Tr(C_sel^2)/n<=K_eff/(t^2 theta)`. The same Gaussian argument gives

```text
zeta<=2sqrt(K_eff/(t^2 theta k)),
beta_rect<=2sqrt(h/(t theta)) e_j.
```

Automatic sublinear covariance applies since b is bounded below. Taking
`k_j=ceil sqrt(d_j max(1,K_eff,j))` makes `k_j=o(d_j)` and both errors
vanish. Equation `(MSC7)` now corrects the positive corner.

Canonicality survives this compression. The group SL5 is ICC: a matrix
with finite conjugacy class commutes with a nonzero power of every
elementary transvection, hence with every off-diagonal matrix unit, hence
is scalar; the only integral scalar of determinant one in odd dimension
is the identity. The regular character of an ICC group is extremal.
Along a subsequence where theta converges, normalized traces of the two
asymptotically reducing corners give a convex decomposition of that
character. Every positive-weight summand must be the regular character.
Equivalently, in the tracial ultraproduct the projection belongs to the
relative commutant of the represented factor L(G); its conditional
expectation onto that factor is the scalar theta. Polar compression and
fixed-word telescoping preserve the limit.

For `(MSC12)`, suppose a canonical sequence stays uniformly away from
flexible correction. Take the supremum a of limiting fractions of
asymptotically reducing, flexibly correctable corners on any subsequence
of it. Diagonal selection over certificates approaching the supremum
attains a while making all errors and relative padding vanish. If a<1,
the positive-density complement is canonical by the preceding argument.
Apply the assumed positive-corner property there, passing to a further
subsequence if needed. It recovers some limiting fraction c>0 of that
complement. Combining the two exact corrected blocks gives a correctable
reducing corner of fraction `a+(1-a)c>a`, a contradiction. Thus a=1.
Filling its o(d) complement with trivial representations gives a full
flexible correction, again contradicting the chosen bad sequence.

The supremum argument allows sequence-dependent M and recovery fractions;
it does not assume a uniform finite number of steps. Compressing the
resulting exact padded representations gives ucp corrections of every
canonical sequence. The required residual-finite regularization theorem
tensors arbitrary approximations with exact regular quotient packets,
then untensors their ucp corrections with normalized HS constant one.
Kazhdan corner rounding yields flexible stability for all asymptotic
tuples. The linked bootstrap artifact spells out the quantifiers and
diagonal choices. Existence of suitable full low-energy spaces with the
bounded second moment remains an unproved hypothesis throughout.

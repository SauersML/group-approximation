---
rg: 2
id: moving-schreier-induction-original-rank-proof
kind: route
title: Normalize the induced corner by its original rank and retain orthogonality at the spectral cut
target: moving-subgroup-schreier-correction-has-no-index-loss
requires:
  - residual-finite-regularization-removes-the-weak-ucp-quantifier
  - sequential-exact-corner-extraction-has-quadratic-error-ledger
  - kazhdan-approximate-coefficients-have-curved-hodge-control
  - kazhdan-irreducible-compressions-have-quadratic-defect
artifacts:
  - research/artifacts/quadratic-curvature-flexible-dilation-2026-09-05.md
  - research/artifacts/rectangular-seed-quotient-alignment-2026-09-05.md
  - research/artifacts/universal-dimension-schreier-host-2026-09-05.md
  - research/artifacts/low-energy-schreier-frame-construction-2026-09-05.md
  - research/artifacts/second-moment-schreier-positive-corner-2026-09-05.md
  - research/artifacts/positive-canonical-corners-bootstrap-stability-2026-09-05.md
  - research/artifacts/soft-schreier-mass-positive-corner-2026-09-05.md
  - research/artifacts/spectral-pair-products-control-schreier-gram-2026-09-05.md
  - research/artifacts/flexible-correction-forces-universal-schreier-mass-2026-09-05.md
  - research/artifacts/universal-host-captures-all-low-energy-types-2026-09-05.md
  - research/artifacts/expansion-blocks-local-schreier-spectral-seeds-2026-09-05.md
  - research/artifacts/maximal-canonical-residual-has-uniform-spectral-exclusion-2026-09-05.md
  - research/artifacts/microscopic-schreier-extraction-dimension-ledger-2026-09-05.md
  - research/artifacts/universal-root-torsion-does-not-control-averaged-relations-2026-09-05.md
  - research/artifacts/curved-hodge-heat-transfers-fixed-schreier-mass-2026-09-05.md
  - research/artifacts/general-irreducible-compression-quadratic-defect-2026-09-05.md
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

For the weaker `(MSC13)`, put `F=F_0(H+I)^(-1/2)`, a contraction with
Gram `K=H(H+I)^(-1)`. Soft polar normalization at tau=1 gives
`sum_s ||Pi^direct_sum(s)F-FU_s||_(2,d)^2<=2h epsilon^2`.
The difference of the Gram matrices of `Pi(s)F` and `FU_s` is the sum
of two products with contraction factors. Therefore

```text
sum_s ||[K,U_s]||_(2,d)^2<=8h epsilon^2,
sum_s ||[K,U_s]||_(2,d)<=2sqrt(2)h epsilon.
```

For `P_t=1_[t,1](K)`, expand in an eigenbasis of K. Integrating the
commutator formula and applying Cauchy--Schwarz with weights
`|U_s(i,j)|^2/d` gives the finite-dimensional coarea bound

```text
integral_0^1 ||[P_t,U_s]||_(2,d)^2 dt
 =sum_(i,j) |lambda_i-lambda_j| |U_s(i,j)|^2/d
 <=||[K,U_s]||_(2,d).
```

The interval `[c/4,c/2]` has length c/4, so some threshold in it makes
the sum of generator squared boundary norms at most
`A=8sqrt(2)h epsilon/c`. Since `tr K>=c`, every threshold in that
interval has `theta=tr P_t>=c-t>=c/2`. This choice is made separately
at each j; no continuity-point subsequence is needed for the estimate.

Choose inverse-compatible unitary polar completions W_s of `P U_s P`.
The compression estimate in the bootstrap artifact gives
`||U_sP-PW_s||_(2,d)<=||[P,U_s]||_(2,d)`. Since the whole F is now a
contraction, the restricted edge error is bounded directly by
`e=sqrt(2h)epsilon+sqrt(A)`. The least singular value of FP is at least
`sqrt(t)`. Polar whitening costs at most `1/sqrt(t theta)` in the corner
normalization, yielding `beta_0<=2sqrt(2)e/c` as claimed. Applying the
original-rank Kazhdan correction directly to this isometry gives relative
padding at most `4beta_0^2/kappa^2` and generator error at most
`(1+10/kappa)beta_0`. The corner is canonical by the ICC argument above.

For the separate sublinear-seed conclusion, `rank H<=bd` and `0<=K<=I`
give `b>=tr K>=c`, so `(MSC10)` supplies `K_eff/d->0`. The whitened
component covariance satisfies `C_sel<=C/(bt)` and hence

```text
Tr(C_sel^2)/(theta d)<=K_eff/(t^2 theta)<=32K_eff/c^3.
```

Gaussian compression therefore gives
`zeta<=2sqrt(32K_eff/(c^3 k))` and `beta_rect<=2sqrt(h)beta_0`.
Taking `k=ceil sqrt(d max(1,K_eff))` proves sublinear seeds and vanishing
errors. The extra Gram term has only qualitative o(1) control; the
explicit beta_0 correction rate belongs to the uncompressed isometry.

Finally, scalar Cauchy--Schwarz in a spectral basis gives
`1=(tr H)^2<=tr[H/(1+H)] tr[H(1+H)]`. Thus a moment bound M implies
soft mass at least `1/(M+1)`. Positive mass itself is all this proof
uses. The positive-corner bootstrap proves the final conditional
stability assertion with sequence-dependent c and subsequences. The
linked soft-mass artifact includes the full constants and retains
existence of suitable spectral spaces as an unresolved hypothesis.

For `(MSC14)`, choose a full low-energy basis `(T_a)` into the regular
host Pi and set `X_s=sum_a T_a^*Pi(s)T_a`. Exact expansion of all pair
products gives

```text
sum_(a,b)||T_a T_b^*||_HS^2=Tr(B^2),
sum_(a,b)||Pi(s)T_a T_b^*Pi(s)^*-T_a T_b^*||_HS^2
 =2(Tr(B^2)-||X_s||_HS^2).
```

Their total invariant squared norm under genuine conjugation is exactly
r. To check the multiplicities, decompose the right-regular invariant
spectral space as `direct_sum_sigma E_sigma tensor C^(r_sigma)`,
where `r_sigma=dim sigma`, `mu_sigma=dim E_sigma`. A basis is indexed
by `(sigma,u,l)`, with u in an orthonormal basis of E_sigma and l in
the regular multiplicity space. Schur averaging of a product within
one sigma block is `delta_(u,v) I_(V_sigma)/r_sigma tensor |l><m|`;
cross-type averages vanish. The squared norm is `delta_(u,v)/r_sigma`,
and summing yields `sum_sigma r_sigma mu_sigma=r`.

The key bound is a weighted spectral trace. Right multiplication
`R_B(T)=TB` is a positive operator on the rectangular HS space, and
`0<=Delta P_E<=epsilon^2 P_E`. Positivity of the trace of a product of
positive operators gives

```text
Tr(R_B Delta P_E)<=epsilon^2 Tr(R_B P_E)
 =epsilon^2 Tr(B^2).
```

This does not assume that R_B commutes with the spectral projection or
the Laplacian. Symmetry of S and inverse compatibility give
`Delta T=2T-(2/h)sum_s Pi(s)T U_s^*`. Expansion and completing the
square identify the weighted trace exactly as

```text
(1/h)sum_s [Tr(B^2)-||X_s||_HS^2+||X_s-BU_s||_HS^2].
```

The order BU_s matters; the cross term agrees by cyclicity and complex
conjugation. Drop the last squared norms and apply the Kazhdan bound to
the direct sum of all pair-product conjugation spaces. Its invariant
part has squared norm r, so
`Tr(B^2)-r<=2h epsilon^2 Tr(B^2)/kappa^2`. Orthogonality also gives
`Tr(B^2)>=r`. Since `Tr B=r`, Cauchy--Schwarz gives `r^2/d<=Tr(B^2)`.
These prove all three inequalities in `(MSC14)`.

To construct the exact r-dimensional target efficiently in multiplicity,
choose orthonormal block maps `A_(sigma,u):C^d->V_sigma` for E_sigma
and stack `T=col_(sigma,u) sqrt(r_sigma) A_(sigma,u)`. Its target
representation is `Theta=direct_sum_sigma sigma tensor I_(mu_sigma)`.
The construction gives exactly

```text
T^*T=B,       Tr(TT^*)=r,
E_(Ad Theta)(TT^*)=I_r,
sum_s ||Theta(s)T-TU_s||_HS^2<=h epsilon^2 r.
```

In particular `||TT^*-I_r||_HS^2=Tr(B^2)-r<=a r/(1-a)`.
If r<=d, complete the polar factor of T to a coisometry V. In a singular
value decomposition this changes each singular value sqrt(lambda) to
one, with squared cost at most `(lambda-1)^2`. The null spaces have
enough dimension for completion, and
`||T-V||_HS<=sqrt(a/(1-a))sqrt(r)`. Thus
`||Theta(s)V-VU_s||_HS<=xi sqrt(r)`.

Write J=`V^*` and P=`JJ^*`. Taking the adjoint residual and multiplying
by the unitaries U_s and Theta(s) shows
`||U_sJ-JTheta(s)||_HS=||Theta(s)V-VU_s||_HS`.
Right multiplication by J^* preserves this HS norm, proving
`||U_sP-JTheta(s)J^*||_HS<=xi sqrt(r)`. The off-diagonal part yields
the asserted commutator bound. Extend `JTheta J^*` trivially on I-P.
Its squared error is the sum of errors on the orthogonal input columns
P and I-P, bounded by `xi^2 r+4(d-r)`. This proves the full-input bound.

If r>d, append r-d zero columns to T and use the input unitaries
`U_s direct_sum I_(r-d)`. The target Gram TT^* and residual estimates
are unchanged. Complete the polar factor to a unitary V on C^r and
conjugate Theta by it. This gives the asserted exact padded correction.
The count bound `b<=1/(1-a)` gives the quadratic relative-padding bound.

For the deterministic seed assertion, Theta embeds into
`lambda_Q tensor I_k` with
`k=max_sigma ceil(mu_sigma/r_sigma)`, by exact multiplicity comparison.
Along canonical sequences with b bounded below, the fixed-type
low-energy multiplicity estimate in `(MSC10)` gives `mu_sigma/d->0`
for every fixed sigma. There are finitely many types below any fixed
dimension R; types above R contribute at most `b/R^2` to
`mu_sigma/(r_sigma d)`. Hence k/d tends to zero, and k/r does too.
Compose this exact embedding with V. On the original input when r<=d
the resulting partial Parseval frame has Gram P and edge error at most
`xi sqrt(b)`; on the padded input when r>d it has Gram I and error at
most xi. Exact embeddings add no error. Positive-density recovered
corners remain canonical by the established ICC argument.

For `(MSC15)`, use an exact correction rho factoring through Q_(2d)
and the coordinate inclusion J from C^d into C^D. An HS-orthonormal
basis `(T_a)` of `Hom_G(rho,lambda_Q)` has dimension D and source Gram
`sum_a T_a^*T_a=I_D`, by the regular multiplicity formula. Restrict it
to the input with `S_a=T_a J`. On the rectangular HS space the frame
operator `A=sum_a |S_a><S_a|` obeys `0<=A<=I`: restriction by J is a
contraction, so A is the contraction of an orthogonal projection.
Moreover `Tr A=d`. The exact intertwining equations give

```text
Tr(Delta A)
 =(1/h)sum_s ||rho(s)J-JU_s||_HS^2<=eta^2 D.
```

Since `Delta>=epsilon^2(I-P_E)`, we have
`Tr(P_E A)>=d-eta^2 D/epsilon^2`. The bound A<=I makes this no greater
than rank(P_E), proving `(MSC15)`. No orthogonality of the restricted
maps is assumed. For flexible corrections choose epsilon tending to
zero with eta/epsilon tending to zero. The resulting lower count and
`(MSC14)` force b to one, then
`||H-I||_(2,d)^2<=1/[b(1-a)]-1->0`. Thus soft mass tends to one half
and full soft coverage holds. This verifies necessity at the fixed
universal host without asserting existence of an exact correction.

For `(MSC16)`, the connection block `Delta_(sigma,U)` depends only on
the G-equivalence class of sigma and on U. Its low-energy multiplicity
mu_sigma is therefore the same in every quotient containing sigma.
In a regular quotient host Q,

```text
r_Q=sum_(sigma in Irr(Q)) dim(sigma) mu_sigma,
B_Q=sum_(sigma in Irr(Q)) B_sigma,
B_sigma=dim(sigma) sum_u A_(sigma,u)^*A_(sigma,u)>=0,
```

where the A_(sigma,u) are an orthonormal basis of its low-energy block.
This source operator is independent of basis and of unitary realization
of sigma. If mu_sigma>0, `(MSC14)` bounds
`dim(sigma)<=r_Q<=d/(1-a)`, hence `dim(sigma)<=M`. The exact universal
host theorem `(MSC9)` puts sigma into Q_M. The two displayed sums give
the count and operator inequalities term by term. A quotient containing
all active Q_M types has equality; in particular a refinement cannot
add further active types. Taking M=2d works for every a<=1/2.

Every finite-dimensional SL5 unitary irreducible has finite image by
`(MSC9)`. For one of dimension m>d, let lambda be its smallest connection
eigenvalue. If lambda>=kappa^2/(2h), the claimed lower bound is immediate.
Otherwise choose cutoff epsilon^2=lambda in the finite image quotient.
Its low-energy count is at least m, so `(MSC14)` yields
`m<=d/(1-2h lambda/kappa^2)`. Rearranging proves the large-type gap.

For `(MSC17)`, put `f(t)=||A_t||_HS` on the scalar coset space. At a
Schreier transition `s t=t' n`, reverse triangle and unitary holonomy
give
`|f(t)-f(t')|<=||pi(n)A_t-A_(t')U_s||_HS`.
The scalar permutation energy of f is thus at most the connection
energy of A. Constants are the only invariant vectors of the transitive
coset action, so the Kazhdan estimate gives

```text
<Delta A,A> >=(kappa^2/h)
  (||f||_2^2-m^(-1)|sum_t f(t)|^2).
```

Support on theta m cosets gives
`m^(-1)|sum f|^2<=theta ||f||_2^2`, and
`||f||_2^2=||A||_HS^2`. This proves the Rayleigh floor for arbitrary
unitary input, regardless of inverse compatibility. Each connection
transport and its adjoint moves row support by one edge, and
`Delta=2I-(1/h)sum_s(mathcal A_s+mathcal A_s^*)`.
A degree-L polynomial starting on v cosets therefore has support at
most `v sum_(l=0)^L h^l<=v h^(L+1)/(h-1)`. Combining this with the
support lower bound and taking logarithms proves the degree estimate.
It does not bound the support of the full spectral projection, which
is a global operation. The linked artifact also explains why the
obstruction persists for local positive mixtures while allowing coherent
combinations that spread over the quotient.

For `(MSC18)`, if r=0 the bound is immediate. Otherwise `(MSC14)`
extracts an exact representation Theta on C^r and a contraction
`C:C^d->C^r` with `Tr(C^*C)=min(r,d)` and
`max_s||Theta(s)C-CV_s||_HS<=xi sqrt(r)`. For r<=d use its polar
coisometry; for r>d restrict its padded polar unitary to the original
d input columns. The assumption a<=1/2 gives r<=2d, so Theta factors
through Q_(2d). An HS-orthonormal basis `(T_a)` of its exact regular
intertwiner space has source Gram I_r. The positive frame operator
`A=sum_a |T_a C><T_a C|` on the original rectangular HS space obeys
`0<=A<=I`, `Tr A=min(r,d)`, and

```text
Tr(Delta_U A)
 =(1/h)sum_s ||Theta(s)C-CU_s||_HS^2
 <=(xi sqrt(r)+eta sqrt(d))^2.
```

The same spectral Bessel-frame argument as `(MSC15)` gives `(MSC18)`.
Along vanishing cutoffs epsilon_j and perturbations eta_j->0, choose
t_j->0 slowly enough that `(xi(epsilon_j)+eta_j)/t_j->0`. Since r_j/d_j
is at most `1/(1-a_j)`, positive normalized count transfers from V_j
to U_j. Interchanging the two tuples proves invariance of exclusion.

For the residual assertion, failure of full flexible stability supplies
a canonical bad sequence by the contrapositive of the required
residual-finite ucp regularization theorem. Maximize the limiting fraction
of asymptotically reducing, flexibly correctable corners over every
subsequence. The diagonal argument already used for `(MSC12)` attains
its supremum alpha, with alpha=0 handled by the zero projection.
Necessarily alpha<1, since a fraction-one corner yields a full flexible
correction after filling its negligible complement trivially. The
complementary polar tuple is canonical by ICC and has positive relative
dimension. It can have no further positive-density correctable corner
on any subsequence, since adjoining one would exceed alpha.

If its normalized low-energy count at some cutoffs t_j->0 were bounded
below along a subsequence, `(MSC14)` would produce precisely such a
corner, or a full flexible correction when the count exceeds the input
dimension. Thus every vanishing-cutoff count tends to zero. Monotonicity
of the count makes this equivalent to
`lim_(t down to 0) limsup_j N_j(t)/n_j=0`: a failure of that iterated
limit permits diagonal selection of a violating vanishing cutoff.
By `(MSC16)`, N_j(t) in Q_(2n_j) equals the supremum over all finite
quotients for sufficiently small t. Equation `(MSC18)` then proves
invariance under vanishing HS changes. The linked residual artifact
records every subsequence and fixed-cutoff quantifier. Neither the
iterated limit nor its proof asserts a lower bound on the smallest
eigenvalue. The later `(MSC21)` does strengthen the density exclusion
to one fixed positive cutoff.

For `(MSC19)`, choose epsilon=L delta(U). At sufficiently small defect,
`a=2h epsilon^2/kappa^2<=1/2`. The nonzero low-energy space in `(MSC14)`
then has a retained-column correction bound
`xi<=sqrt(h)(1+4/kappa)L delta(U)` and, if its count exceeds the input
dimension, padding at most `4h L^2 delta(U)^2/kappa^2`. Choose a single
constant K bounding these two coefficients. Thus every sufficiently
small positive-defect tuple supplies a nonzero exact corner with error
at most K delta(U) relative to its rank, or a full flexible correction
with error at most K delta(U) and relative padding at most K delta(U)^2.

Fix an original dimension d, defect delta_0>0 and a threshold theta in
(0,1), to be chosen below. Extract such corners and use unitary polar
completions on the remaining spaces
until their dimension is at most theta d. Stop earlier if the remaining
tuple is exact or receives a full flexible correction. Write r_i for
the extracted ranks, delta_i for the current normalized defect, and

```text
A_i=(1/d)sum_(l<i) xi_l^2 r_l,       xi_l=K delta_l,
x_i=n_i/d,
```

By the required sequential extraction ledger, the original tuple is
within sqrt(3A_i) of the block tuple consisting of all extracted exact
representations and the current residual. If ell is the longest
defining-relator length, fixed-word telescoping and the exactness of
the extracted blocks give, as long as the residual dimension exceeds
theta d,

```text
delta_i <=(delta_0+ell sqrt(3A_i))/sqrt(x_i),
delta_i^2 <=(2/x_i)(delta_0^2+3ell^2 A_i).
```

Set B_i=`delta_0^2+3ell^2 A_i` and `c=6K^2 ell^2`. Its increments satisfy

```text
B_(i+1)<=B_i(1+c r_i/n_i).
```

Whenever n_(i+1)>0, put u=r_i/n_i<1. The inequality
`log(1+cu)<=cu<=-c log(1-u)` gives inductively

```text
B_i<=delta_0^2 x_i^(-c),
delta_i^2<=2delta_0^2 x_i^(-c-1).
```

Choose a fixed delta_bar>0 below the uniform seed threshold and small
enough for the cutoff a<=1/2 used above. For sufficiently small delta_0,
set `theta=(2delta_0^2/delta_bar^2)^(1/(c+1))<1`. Every pre-step
x_i>theta then satisfies

```text
delta_i^2<=delta_bar^2,
delta_i^2 x_i<=delta_bar^2 theta,
B_i<=delta_bar^2 theta/2.
```

Thus the seed threshold remains valid throughout; the intermediate
defects need only stay below this fixed threshold. Each step removes
at least one dimension, so there are at most d steps. If an extraction
first crosses to residual dimension at most theta d, its last B
multiplier is at most 1+c, including the case of zero remaining
dimension. Trivial filling and the ledger give squared normalized error
at most `[4+(1+c)delta_bar^2/(2ell^2)]theta`.

In the terminal flexible alternative, let q be the residual padding.
Then `q<=K delta_i^2 n_i`, so `q/d<=K delta_bar^2 theta`. Combine
that correction with the already exact blocks. One final triangle
inequality bounds the squared error normalized by d+q by

```text
6A_i+2K^2 delta_i^2 (n_i+q)/(d+q)
 <=[delta_bar^2/ell^2
    +2K^2(1+K delta_bar^2)delta_bar^2]theta.
```

This retains the residual dimension weight even if delta_i itself does
not tend to zero. An exact residual is easier, and delta_0=0 is exact
from the start. Since theta is a constant times delta_0^(2/(c+1)), the
generator error is `O(delta_0^(1/(c+1)))` and relative padding is
`O(delta_0^(2/(c+1)))`. This proves the conditional Holder refinement
of flexible stability under the uniform microscopic seed estimate.

The ledger controls accumulated error even for arbitrarily many tiny
corners, but does not justify a qualitative seed iteration by itself.
Without a relation between xi_i and delta_i, the next residual need
not stay within a vanishing-defect regime. Nor is a vanishing-density
extracted corner necessarily canonical. Positive-density remainders
are canonical only after the accumulated ledger tends to zero, by
approximate reduction and the ICC conditional-expectation argument.
The linked artifact separates these rate and trace issues explicitly.

For `(MSC20)`, fix the twenty elementary generators x_ij of SL5 and
the presentation with commuting-root relators, root relators
`[x_ij,x_jk]x_ik^(-1)`, and `(x_12 x_21^(-1) x_12)^4`.
Use `[a,b]=a^(-1)b^(-1)ab`; this precise presentation appears in
[Biswas, *Uniform two-generator presentations for SL_n(Z) with polynomial
complexity bounds*, Eq. (1)](https://arxiv.org/html/2604.17777v1#S1.E1).
The Weyl relator uses no x_13.

For odd primes p tending to infinity, let rho_p be the regular
representation of Q_p=SL5(F_p), N=|Q_p|, d=N+m, and
`q=lcm(1,...,n)`, `n=floor((2d)^(1/3))`. The upper unitriangular
subgroup has order p^10 and the diagonal sign subgroup has order 16,
so `p^10|N` and `16|N`. Thus p<=n, p|q, and q is even. Also
`q>=lcm(n,n-1,n-2)>=n(n-1)(n-2)/2`, so `q>=c d` eventually.

Choose a phase lambda of order s dividing q and define

```text
U_ij=rho_p(x_ij) direct_sum I_m,              (i,j)!=(1,3),
U_13=lambda rho_p(x_13) direct_sum (-I_m).
```

Every U_ij has exact q-torsion. For any fixed word w with exponent
sum e(w) in x_13,

```text
U(w)=lambda^(e(w))rho_p(w) direct_sum (-1)^(e(w)) I_m.
```

The chosen defining relators have exponent sum zero or -1, with -1
attained by `[x_12,x_23]x_13^(-1)`. Therefore their exact maximum
defect satisfies

```text
delta^2=(N/d)|lambda-1|^2+4m/d.
```

If m/d tends to zero and lambda tends to 1, every fixed true SL5
relation is asymptotically satisfied. Any fixed nonidentity integer
matrix remains nonidentity modulo all sufficiently large primes, so
its regular trace is eventually zero; the word formula then proves
canonicality. If additionally `|lambda-1|=o(delta)`, the last m
coordinates give an exactly reducing support P with
`tr_d(P)~delta^2/4`. The singular values of any defining defect on
P are either 0 or 2, and its complementary norm is o(delta). Thus
the relative low-angle curvature energy vanishes at every fixed
cutoff below 2, as required for the QRC normal form.

For uniform residues a,b modulo q the exact root identity on the
regular block gives

```text
[U_12^a,U_23^b]U_13^(-ab)
 =lambda^(-ab) I_N direct_sum (-1)^(ab) I_m.
```

Character orthogonality gives the average of `lambda^(ab)` as 1/s:
the inner b average is one exactly when s divides a and zero
otherwise. The average of `(-1)^(ab)` is 1/2 because q is even.
Hence the squared averaged defect is exactly

```text
(N/d)(2-2/s)+m/d.
```

First take m=1 and `lambda=exp(2 pi i/q)`. Then
`delta^2=4/d+O(q^(-2))`, `delta~2/sqrt(d)`, and
`|lambda-1|=o(delta)`. The mean squared defect tends to 2, with
the phase character average exactly 1/q.

For the stronger spectral version take m=N/p and
`lambda=exp(2 pi i/p)`. Now `delta^2=4/(p+1)+O(p^(-2))`,
`|lambda-1|=o(delta)`, and the averaged defect is exactly
`(2p-1)/(p+1)`, again tending to 2. The spectrum of each good root
block consists of every p-th root with multiplicity N/p; multiplying
one block by lambda permutes this spectrum. The only additional
possible eigenvalues are 1 and -1. All orders are at most n.
Each primitive p-th root eigenspace has dimension N/p divisible
by p^3, while the -1 eigenspace has dimension m divisible by 8.
Thus even the individual three-Heisenberg-pair divisibility tests
hold. These spectral facts do not assert exact joint root relations.

Both versions are repaired by replacing U_13 with
`rho_p(x_13) direct_sum I_m`, at exact normalized HS cost delta.
Removing only the scalar phase costs `o(delta)` and leaves averaged
error m/d, which tends to zero. Root rounding alone fixes the
already allowed spectra. This establishes the stated failure of
the uncorrected power-defined ledger, while explicitly ruling out
any interpretation as an instability counterexample. The linked
universal-root-torsion artifact records the full construction.

For `(MSC21)`, use the finite presentation cochain maps d0,d1 with
`(d0 v)_s=(T_s-I)v` and the Fox/word differential satisfying
`(d1 d0 v)_r=(T(r)-I)v`. If the symmetric generator labels are treated
as independent cochain coordinates, include their inverse-consistency
relators in the presentation. Their evaluated defects are zero for our
tuples. This ensures ker d1 is precisely the group cocycle space for
genuine coefficient actions.

Property (T) gives full H^1 vanishing for every unitary coefficient
representation. Hence there is an exact uniform Hodge gap 2mu>0:

```text
||d0* f||^2+||d1 f||^2 >= 2mu ||f||^2.
```

Otherwise unit cochains of vanishing Hodge energy in genuine actions
have a Hilbert-ultraproduct limit that is a nonzero cocycle orthogonal
to all coboundaries, contradicting full H^1 vanishing.

Let rho:G->U(D) be exact and let U act on C^d with defining defect
delta. On rectangular matrices put `T_s(A)=rho(s) A U_s^*`, and
normalize HS norms by sqrt(d). Uniform constants C0,delta_0>0 give
the curved inequality

```text
mu ||f||_2^2 <= ||d0* f||_2^2+||d1 f||_2^2
                  +C0 delta^2 max_s||f_s||op^2.
```

To prove uniformity, a sequence violating it with C0=j and
0<delta_j<1/j can be normalized to ||f_j||_2=1, forcing
`delta_j max_s||f_(j,s)||op<=sqrt(mu/j)`. In the rectangular HS
ultraproduct, the closure of classes represented by A_j satisfying
`delta_j||A_j||op->0` carries a genuine G action, because
`||(T(r)-I)A_j||_2<=delta_j||A_j||op`. The limiting cochain belongs
to that Hilbert subspace and has Hodge energy at most mu, violating
the exact gap 2mu. At delta=0 the exact inequality applies directly.

For any contraction A0 define `A_t=exp(-t L0)A0`,
`L0=d0*d0=sum_s(2I-T_s-T_s*)`. The heat semigroup is a Poisson
average of powers of `(1/(2h))sum_s(T_s+T_s*)`, hence preserves
operator contractivity. Write `E(t)=||d0 A_t||_2^2` and
`N(t)=||A_t||_2^2`. The curvature identity gives
`||d1d0 A_t||_2^2<=|R|delta^2`, while
`max_s||(d0 A_t)_s||op<=2`. With K0=|R|+4C0, differentiation
and the curved inequality yield

```text
E'(t)<=-2mu E(t)+2K0 delta^2,       N'(t)=-2E(t),
E(t)<=E(0)e^(-2mu t)+(K0/mu)delta^2,
N(t)>=N(0)-E(0)/mu-(2K0/mu)delta^2 t.
```

Choose epsilon_*>0 so `a_*=2h epsilon_*^2/kappa^2<=1/2` and,
for `xi_*=sqrt(h)epsilon_*+2sqrt(a_* /(1-a_*))`,
`gamma=h xi_*^2/[mu(1-a_*)]<=1/4`. Put r=N_U(epsilon_*).
If r=0 the claimed bound is immediate. Otherwise `(MSC14)` gives
an exact target Theta of dimension r and a contraction A0:C^d->C^r
with `N(0)=min(r,d)/d` and `E(0)<=h xi_*^2 r/d`. When r>d,
take the original d columns of its padded polar unitary. Since
`r/d<=1/(1-a_*)`, in both cases `E(0)/mu<=gamma N(0)`.

At `t=log(1/delta)/mu`, the heat estimates give energy at most
C1 delta^2 and mass at least
`(1-gamma)min(r,d)/d-C1 delta^2 log(1/delta)`. Also r<=2d,
so Theta factors through the universal host Q_(2d). Choose an
HS-orthonormal basis T_a of exact intertwiners Theta->lambda_Q;
regular multiplicities give `sum_a T_a* T_a=I_r`. Since A_t is
an operator contraction, the usual Bessel frame satisfies

```text
F=sum_a |T_a A_t><T_a A_t|<=I,
Tr F=d N(t),            Tr(Delta F)=d E(t)/h.
```

Spectral truncation implies `N_U(eta)/d>=N(t)-E(t)/(h eta^2)`.
This proves `(MSC21)`, uniformly over tuples and dimensions. At
eta=sqrt(delta), its two remainder terms are O(delta). Positive
fixed-cutoff normalized count thus produces positive count at a
vanishing cutoff. Applied to the maximal residual's iterated-limit
exclusion, it forces its count density at epsilon_* to vanish.
The conclusion concerns density, not the smallest eigenvalue.

For the stated HS basin, take D=d, A0=I, and
`max_s||rho(s)-U_s||_2<=eta_0` with `h eta_0^2<=mu/4`.
Then N(0)=1 and E(0)<=h eta_0^2. At logarithmic time and small
delta, N(t)>=1/2 and E(t)<=(h eta_0^2+K0/mu)delta^2. The
Rayleigh quotient of A_t for Delta=L0/h is at most
`[2eta_0^2+2K0/(h mu)]delta^2`. At least one irreducible component
of rho has no larger quotient. That component occurs in regular
Q_(2d), proving the claimed local form of `(MSC19)`. The coarse
exact comparison remains a hypothesis. The linked curved-Hodge
artifact supplies the full normalization and quantifier details.

For `(MSC22)`, the required generic compression theorem gives constants
theta_0,c,C and a heat-flow contraction A:C^d->C^N satisfying
`||A||HS^2>=d/2` and
`sum_s||rho(s)A-AU_s||HS^2<=B delta^2 d`, as well as the full
two-sided defect comparison. Decrease theta_0 to at most 1/2.
Then N=(1+k/d)d<2d, so the universal-conductor result places rho
in the regular Q_(2d) host. The map A has Rayleigh quotient at most
`L^2 delta^2`, where L^2=2B/h. Hence the coefficient block of rho
has a nonzero low-energy vector. Its regular multiplicity is dim rho=N,
so the full low-energy space has dimension at least N, proving MSC22.
MSC14 also bounds this count by d/(1-a), with
`a=2hL^2 delta^2/kappa^2`; when a<=1/2 this yields
`k/d<=4hL^2 delta^2/kappa^2` directly in the arithmetic host.
The general theorem's Schur-variance proof needs no finite quotient.
The original rectangular Kazhdan comparison excludes every correction
dimension below N at vanishing error, so its necessary k/d padding
is now comparable to delta^2 for all k=o(N), including growing k.

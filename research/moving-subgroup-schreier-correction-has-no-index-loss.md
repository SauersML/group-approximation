---
rg: 2
id: moving-subgroup-schreier-correction-has-no-index-loss
kind: claim
title: Kazhdan correction from Schreier holonomy has no subgroup-index loss
artifacts:
  - research/artifacts/moving-schreier-correction-audit-2026-09-04.md
  - research/artifacts/quadratic-curvature-flexible-dilation-2026-09-05.md
  - research/artifacts/rectangular-seed-quotient-alignment-2026-09-05.md
  - research/artifacts/universal-dimension-schreier-host-2026-09-05.md
  - research/artifacts/low-energy-schreier-frame-construction-2026-09-05.md
  - research/artifacts/second-moment-schreier-positive-corner-2026-09-05.md
  - research/artifacts/positive-canonical-corners-bootstrap-stability-2026-09-05.md
distinct_from:
  subgroup-exact-outliers-do-not-exist: that fixes the subgroup and absorbs its section and index into constants; this allows arbitrary moving finite-index subgroups and gives a root-mean-square edge bound with no index or normal-core factor.
  kazhdan-almost-invariant-corner-near-invariant-projection: that rounds a supplied invariant-corner candidate; this constructs that candidate from exact subgroup holonomy and gives a quantitative correction of the original generator tuple.
  sl3-z-weakly-ucp-stable: that must correct arbitrary lattice microstates; this assumes an exact subgroup representation and small measured Schreier edge discrepancy, neither of which follows just from small defining-relator defect when the subgroup moves.
---

Let `G` have a finite symmetric Kazhdan set `S` and constant `kappa>0`,
in the convention

```text
dist(v,H^G) <= kappa^(-1) max_(s in S)||pi(s)v-v||
```

for every genuine unitary representation.  Let `N<=G` have any finite
index `m`, with a left-coset transversal `T`.  No normality is required.
Let `pi:N->U(d)` be genuine, let `U_s in U(d)` be arbitrary, and choose
arbitrary gauge unitaries `V_t in U(d)` for `t in T`.  For

```text
s t=t' n(s,t),       t' in T, n(s,t) in N,
```

define the measured edge energy

```text
beta^2=max_(s in S) (1/m) sum_(t in T)
 ||U_s V_t-V_(t') pi(n(s,t))||_(2,d)^2.                 (MSC1)
```

There is an exact representation `alpha:G->U(D)` with `D>=d` and a
unitary identification `C^D=C^d direct_sum C^(D-d)` such that

```text
0 <= (D-d)/d <= 4 beta^2/kappa^2,
max_(s in S)||alpha(s)-(U_s direct_sum I_(D-d))||_(2,D)
 <= (1+10/kappa) beta.                                 (MSC2)
```

There is no dependence on `m`, `d`, the section lengths, or a Kazhdan
constant of `N` in `(MSC2)`.  The subgroup, its representation, the gauges,
and the index may all change along a sequence.  In particular `beta_j->0`
implies flexible normalized-HS correctability even if `[G:N_j]->infinity`
arbitrarily fast.  The induced representation can be large; the corrected
invariant summand has dimension asymptotic to the original `d_j`.

The same data give an explicit ucp map on the full group C*-algebra:

```text
Phi(g)=(1/m)sum_(t in T) V_(t') pi(n(g,t)) V_t^*,
g t=t' n(g,t).                                         (MSC5)
```

If `beta_s^2` is the generator-specific average in `(MSC1)`, then

```text
beta_s^2=2-2 Re tr_d(U_s^* Phi(s)),
||Phi(s)-U_s||_(2,d)<=beta_s.                           (MSC6)
```

Thus the certificate supplies prescribed matrix-valued positive-definite
approximants as well as flexible exact representations.  Positivity comes
from the exact induced representation, not from averaging an approximate
representation as though it were genuine.

There is a rectangular version in which the genuine subgroup representation
can be much smaller than the tuple being corrected. Let
`pi:N->U(k)` be genuine and let `A_t:C^d->C^k` be arbitrary linear maps.
For the same Schreier transitions define

```text
H=sum_t A_t^* A_t,
zeta=||H-I_d||_(1,d),
beta_rect^2=max_s (1/d)sum_t
 ||pi(n(s,t))A_t-A_(t')U_s||_HS^2,
gamma=beta_rect+2sqrt(zeta).                            (MSC7)
```

The norms inside the sum are unnormalized. There is an exact padded
representation as in `(MSC2)`, with beta replaced everywhere by gamma,
and a full-group-algebra ucp map with generator error at most gamma.
Neither bound depends on k, m, or a lower singular-value bound for H.
The maps need not be square, unitary, or a PVM. The original certificate
is the special case `k=d`, `A_t=m^(-1/2)V_t^*`, and zeta zero.

If `mk>=d`, the ucp dilation is the exact induced representation itself.
If `mk<d`, first add `d-mk` trivial ambient dimensions before normalizing
the stacked frame; the same estimates hold. Necessarily
`zeta>=max(0,1-mk/d)`, so a small Gram error still records the dimension
capacity needed for an almost isometric d-dimensional corner. Supplying
small beta_rect and zeta and genuine k-dimensional subgroup holonomy is
essential; curvature concentration alone does not produce these data.

There is a quantitative constraint on selecting the small seed. Suppose
the input tuple is an exact representation `rho:G->U(d)`, and let R be
the dimension of the largest common subrepresentation of rho and
`Pi=Ind_N^G pi`. Then every rectangular frame satisfies

```text
R=sum_sigma dim(sigma) min(m_rho(sigma),m_Pi(sigma)),
R/d >= 1-zeta-beta_rect^2/kappa^2.                      (MSC8)
```

Zero Gram and edge errors are possible exactly when R=d. By Frobenius
reciprocity this means
`m_rho(sigma)<=dim Hom_N(Res_N sigma,pi)` for every irreducible sigma.
For a tuple at generator HS distance eta from rho, replace beta_rect in
`(MSC8)` by `beta_rect+sqrt(eta^2+4zeta)`. These estimates concern the
original induced space, before auxiliary trivial padding.

For example, take `G=SL_5(Z)` and the regular quotient representation
`rho=lambda_(SL_5(F_p))`, of dimension d. At any coprime congruence level
`N=Gamma(q)`, every seed has `R<=k`, so small Gram and edge errors require
`k/d>=1-zeta-beta_rect^2/kappa^2`. At the matching level `N=Gamma(p)`,
the trivial one-dimensional seed and coordinate-row frame give zero
errors exactly. The distinction persists after removing the single
trivial line of the regular input, and under vanishing HS perturbations.
Thus large index is insufficient: the subgroup must match the quotient
representation content, which arbitrary QRC data do not yet identify.

For exact `SL_5(Z)` inputs there is nevertheless one explicit universal
choice of subgroup depending only on a dimension bound D:

```text
q_D=lcm(1,...,floor(D^(1/3))),
N_D=Gamma(q_D),       Q_D=SL_5(Z)/N_D.                  (MSC9)
```

Every genuine unitary representation rho of dimension `d<=D` factors
through Q_D. If its irreducible multiplicities are m_sigma, the smallest
trivial seed for an exact rectangular frame at this host is

```text
k_min(rho)=max_(m_sigma>0) ceil(m_sigma/dim(sigma)).
```

The resulting frame has zeta=beta_rect=0. For every sequence of exact
representations whose normalized characters converge to the canonical
regular character, `k_min(rho_j)/d_j->0`. Every constituent is retained.
The same frames have zeta zero and edge error at most eta for any tuple
within generator HS distance eta of the exact input.

Thus the subgroup and triviality of the seed can be fixed before choosing
an exact comparison representation. Selecting a good frame directly from
an arbitrary approximate tuple is still unproved. The large quotient in
`(MSC9)` is an existence construction; no efficient enumeration is claimed.

There is a spectral construction for approximate inputs as well. Let
`G=SL_5(Z)`, `h=|S|`, and let `U_(j,s)` be inverse-compatible canonical
asymptotic tuples on `C^(d_j)`: every fixed evaluated word has normalized
trace tending to the regular character of its group element. For any
finite quotient regular host `Pi_j=lambda_(Q_j)`, define on the rectangular
HS space

```text
D_s(T)=Pi_j(s)T-TU_(j,s),
Delta_j=(1/h)sum_s D_s^*D_s,
E_j=range 1_[0,epsilon_j^2](Delta_j),       epsilon_j->0.
```

Assume `E_j!=0`. For an HS-orthonormal basis `(T_a)` of E put

```text
r=dim E,       b=r/d,
B=sum_a T_a^*T_a,       C=sum_a T_a T_a^*,
H=B/b,       K_eff=Tr(C^2)/(b^2 d),       tr_d H=1.
```

If b stays bounded below, canonicality alone implies `K_eff/d->0`.
For any positive tau and integer k, soft polar normalization and Gaussian
compression supply a trivial k-dimensional seed with

```text
zeta <= tr_d[tau(H+tau I)^(-1)]+2sqrt(K_eff/(tau^2 k)),
beta_rect <= 2sqrt(2h/tau) epsilon.                    (MSC10)
```

Consequently the soft coverage condition
`lim_(tau down to 0) limsup_j tr_d[tau(H_j+tau I)^(-1)]=0`
produces full-input frames with `k_j=o(d_j)` and both errors tending to
zero. The effective-covariance assertion applies to the approximate
tuple directly; no exact comparison representation is assumed.

A weaker hypothesis suffices for a positive part of the input. If

```text
tr_(d_j)(H_j^2)<=M<infinity,                           (MSC11)
```

then, after a subsequence, there are asymptotically reducing projections
P_j of relative rank at least `1/(16M)`. Their polar-compressed tuples
remain canonical and admit vanishing-error rectangular frames with
`k_j=o(d_j)`. Thus those tuples admit the exact flexible correction in
`(MSC2)`. Any complementary corner of positive limiting relative rank
also remains canonical. No bounded operator norm of H is required.

Finally, suppose **every** canonical asymptotic SL5 tuple sequence has a
subsequence, a choice of finite quotient hosts, and positive cutoffs
`epsilon_j->0` for which E_j is nonzero and `(MSC11)` holds with some
finite M. The constant M may depend on the sequence. Then

```text
SL_5(Z) is flexibly HS-stable.                        (MSC12)
```

The intermediate principle is useful independently: positive-fraction
correctable canonical corners on a subsequence of every canonical
sequence bootstrap to full canonical correction. Neither the fraction
nor the number of recoveries must be uniform. Maximize recoverable mass
over subsequences and apply the same hypothesis to a positive remainder.
The existing constant-one ucp untensoring theorem then removes the
canonical restriction. This conditional theorem does not assert its
moment hypothesis. Small curvature does not presently supply `(MSC11)`.

For presentation applications take `V_t=U(q_t)` for word representatives,
and express each `n(s,t)` by a word `q_(s,t)` in a chosen subgroup menu.
If the identity `s q_t=q_(t') q_(s,t)` has defining-relator area `A_(s,t)`,
the subgroup word has menu length `ell_(s,t)`, the defining defect is
`delta`, and `pi` is `xi`-close to the evaluated menu, then

```text
beta <= B delta+L xi,
B=max_s ((1/m)sum_t A_(s,t)^2)^(1/2),
L=max_s ((1/m)sum_t ell_(s,t)^2)^(1/2).                  (MSC3)
```

Thus even the word costs are root-mean-square costs, not sums over the
coset set.  Moving subgroups are permitted whenever the displayed combined
cost tends to zero.  The condition `delta_j->0` alone does not imply this
when `B_j,L_j` grow.

The contrapositive is useful for the arithmetic outlier branch: if a tuple
stays at least `eta` away from every exact padded representation with
relative padding at most `gamma`, then every choice in `(MSC1)` satisfies

```text
beta >= min(eta/(1+10/kappa), (kappa/2)sqrt(gamma)).       (MSC4)
```

The minimum follows by excluding both strict inequalities simultaneously.
This is a measured holonomy floor, not an existence proof for a correcting
subgroup representation.  It does not establish flexible HS stability of
`SL_3(Z)` or nonhyperlinearity of its HNN extension.

DERIVATION
moving-schreier-induction-original-rank-proof

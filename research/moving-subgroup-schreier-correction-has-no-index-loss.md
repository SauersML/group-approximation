---
rg: 2
id: moving-subgroup-schreier-correction-has-no-index-loss
kind: claim
title: Kazhdan correction from Schreier holonomy has no subgroup-index loss
artifacts:
  - research/artifacts/moving-schreier-correction-audit-2026-09-04.md
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

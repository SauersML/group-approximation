---
rg: 2
id: index-three-qsystem-rounding-is-relative-repair
kind: claim
title: Joint index-three Q-system rounding is quantitatively relative Iwahori repair
distinct_from:
  gauge-optimized-induced-energy-target: that uses induction from a growing finite BS core into a finite endpoint and asks for a uniform section-energy estimate; this uses the fixed index-three modular inclusion and identifies exactly what its joint flat-projection rounding would prove.
  three-coset-frame-saturation-is-not-pair-functorial: that gives a finite packet defeating separate averaging or intersection of the two supports; this proves the positive fixed-index encoding and shows why only joint rounding remains.
  subgroup-exact-outliers-do-not-exist: that rounds an induced range by the ambient group's property T; the modular vertex has no such gap, and the flat Q-system condition turns its missing rounding theorem into relative repair itself.
---

**ESTABLISHED.**  Let

```text
V=PSL_2(Z)=C_2*C_3,          B=Gamma_0(2)/{+-1},
[V:B]=3,                     A=V *_B V,                (IQR1)
```

with the second copy using the usual Nielsen identification of the abstract
edge group.  There is a fixed-constant, quantitatively reversible
correspondence between the following two problems.

1. Two exact finite-dimensional `V`-representations have close identified
   `B`-restrictions and are to be flexibly perturbed to exact vertex
   representations with one literally common `B`-restriction.
2. After optimizing one exact common fiber representation `sigma` of `B`,
   two canonical rank-`d` flat projections in the two index-three induced
   spaces are to be jointly perturbed to invariant flat projections over
   one literally common optimized fiber.

All metric constants and padding factors depend only on the index three and
fixed generating sets.  Thus a dimension-uniform joint flat-projection
rounding theorem proves relative Iwahori liftability, and conversely every
such relative repair canonically rounds the projections.  The Q-system
coordinate is an exact finite Morita reformulation of the remaining gate,
not an automatic projection-rounding theorem.

## The exact flat-projection dictionary

Fix `sigma:B->U(H)`, `dim H=d`, and put

```text
rho=Ind_B^V(sigma)  on  K=directSum_(i=0)^2 H,
E_i=the three coset-coordinate projections.            (IQR2)
```

If `pi:V->U(H)` extends `sigma`, the standard Frobenius isometry

```text
(W_pi xi)_i=3^(-1/2) pi(t_i)^* xi                     (IQR3)
```

for fixed coset representatives `t_0=1,t_1,t_2` intertwines `pi` with
`rho`.  Its range projection `P_pi=W_piW_pi^*` satisfies

```text
P_pi in rho(V)',       rank(P_pi)=d,
E_i P_pi E_i=(1/3)E_i             (i=0,1,2).           (IQR4)
```

Conversely, let `P in rho(V)'` be a rank-`d` projection satisfying the
identity-coordinate flatness equation

```text
E_0 P E_0=(1/3)E_0.                                  (IQR5)
```

Then

```text
J=sqrt(3) E_0|_(PK):PK->H                             (IQR6)
```

is unitary: `(IQR5)` makes it a coisometry and the two spaces have equal
dimension.  Since identity-coordinate evaluation is `B`-equivariant, `J`
identifies the restriction of `rho|_(PK)` exactly with `sigma`.  Hence
`rho|_(PK)` is a genuine `V`-extension of `sigma`.  The other two flatness
equations follow from invariance and transitivity, but retaining all three
is convenient for approximate data.

The same construction on the opposite copy of `V`, using its edge
embedding, gives the two projection systems over one fiber `sigma`.  Exact
joint flat invariant projections therefore compress to an exact
representation of the amalgam `A`, and every exact amalgam representation
returns those projections.

## Fixed-index quantitative encoding

Suppose `pi:V->U(H)` is exact and its identified edge restriction `beta`
obeys

```text
max_(b in S_B)||beta(b)-sigma(b)||_2<=epsilon.         (IQR7)
```

Use `(IQR3)` with `pi` even though its restriction is `beta`.  The map is
still an exact isometry and its range projection is still exactly flat.
For `v` in a fixed generating set of `V`, the failure of
`rho(v)W_pi=W_pipi(v)` is a direct sum of the three errors

```text
sigma(b_(i,v))-beta(b_(i,v)),                         (IQR8)
```

where the finite Schreier cocycles `b_(i,v)` are fixed words in `S_B`.
Ordinary word telescoping therefore gives

```text
max_(v in S_V)||rho(v)W_pi-W_pipi(v)||_2<=C_0 epsilon,
max_(v in S_V)||[rho(v),P_pi]||_2<=2C_0 epsilon.       (IQR9)
```

There is no growing section, area, or congruence-level constant here.

If a joint rounding supplies a nearby exact common fiber `sigma'` and
nearby invariant flat projections `Q_+`,`Q_-` in the two inductions, the
exact dictionary compresses them to two vertex representations with common
restriction `sigma'`.  The two-projection polar lemma transports the
compressions back to the original `W_pi H` ranges.  A rank discrepancy `r`
costs only a fixed multiple of `r` dimensions: unmatched edge pieces may be
induced across one index-three vertex, costing at most `3r`.  Consequently
squared normalized projection displacement and relative rank loss give the
usual square-root HS displacement and linear flexible-padding ledger.

Conversely, a flexible exact repair of the two vertex representations and
their common edge restriction changes each of the three blocks in `(IQR3)`
by only a fixed-word Lipschitz constant.  Its canonical range projections
are therefore a joint flat-projection rounding with the same asymptotic
rank and HS costs.  This proves quantitative reversibility.

## Consequence for the gauge-optimized energy lane

This fixed-index encoding does **not** prove

```text
G_N(X,b)<=C E_end(X,b).                               (IQR10)
```

The functional `G_N` in `gauge-optimized-induced-energy-target` measures a
particular growing finite-quotient section cocycle and is a sufficient
same-space strengthening of relative repair.  The index-three construction
replaces that cocycle by `(IQR9)`, but leaves the joint invariant-flat
rounding problem.  By the reversible dictionary, solving that problem is
already solving relative Iwahori liftability; it supplies no comparison
from its fixed three-coordinate defect back to the chosen `G_N` section
energy.

Nor may the projections be rounded separately.
`three-coset-frame-saturation-is-not-pair-functorial` gives the actual
opposite mod-two Iwahori packet where the two separate three-coset averages
are `I_2/2` and a rank-one projection, and their separately saturated cores
do not transport.  What survives is precisely **joint**, fiber-optimized
flat Q-system rounding.  Generic spectral cutting, finite-index
Pimsner--Popa inequalities, and Q-system permanence do not provide it.

DERIVATION
index-three-qsystem-dictionary-proof

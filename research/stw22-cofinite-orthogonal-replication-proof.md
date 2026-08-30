---
rg: 2
id: stw22-cofinite-orthogonal-replication-proof
kind: route
title: Assemble uncountably indexed spectral cuts as countable uniform-2 tails
target: stw22-finite-derived-set-factor-bundles-have-uniform-traces
requires: []
artifacts:
  - research/artifacts/stw22-uncountable-cofinite-bundle-audit-2026-08-30.md
---

## 1. Topological reduction

A compact Hausdorff scattered space is zero-dimensional.  Since `K'` is
finite, choose pairwise disjoint clopen neighbourhoods of its points.  Their
complement is compact and discrete, hence finite.  Each clopen neighbourhood
has exactly one nonisolated point and is therefore the one-point
compactification of its discrete complement.  Central clopen projections
split `M` into a finite direct sum, so it is enough to treat

```text
K=D union {infinity},                                   (UCF2)
```

the one-point compactification of an arbitrary discrete set `D`.

Write `p_d=1_{ {d} } in C(K)`.  The corner `p_dM` is complete on bounded
sets for its single tracial `2`-norm.  Its trace is faithful because the
uniform `2`-norm on `M` is faithful.  Hence `p_dM` is the finite-factor fibre
at `d`; in particular it contains its spectral projections and partial
isometries.

## 2. Atomic central disintegration without countability

Let `phi` be a tracial state on `M`, and let `mu` be the Radon probability
measure representing `phi|C(K)`.  Put `mu_d=mu({d})`.  Radon inner
regularity on the open discrete set `D` gives

```text
mu(D)=sum_(d in D) mu_d.                                (UCF3)
```

Indeed every compact subset of `D` is finite.  Thus only countably many
`mu_d` are nonzero and

```text
mu= sum_(d in D) mu_d delta_d + mu_infinity delta_infinity.
```

The normalized restriction of `phi` to a nonzero corner `p_dM` is the
unique trace of that finite factor.  Consequently the norm-convergent series

```text
phi_at=sum_d mu_d tau_d
```

is a positive tracial functional dominated by `phi`: on positive elements,
every finite partial sum is `phi(p_F .)` for a finite central projection
`p_F`.  Hence `nu=phi-phi_at` is positive and tracial, has norm
`mu_infinity`, and its central restriction is
`mu_infinity delta_infinity`.

If `mu_infinity=0`, formula `(UCF1)` already follows.  Otherwise normalize
`psi=nu/mu_infinity`.  Then

```text
psi|C(K)=delta_infinity,       psi(p_dM)=0  (d in D).    (UCF4)
```

It remains to prove that `psi` kills the trace-kernel ideal

```text
K_infinity={a:E(a*a)(infinity)=0}.
```

## 3. An arbitrary cofinite cut has countable support

Let `0<=b<=1` lie in `K_infinity`, and fix `eta>0`.  In the factor `p_dM`
put

```text
e_d=1_[eta,1](p_db),
t_d=tau_d(e_d)<=||p_db||_2^2/eta^2.                    (UCF5)
```

Continuity of `E(b^2)` at `infinity` says `t_d->0` in the cofinite filter:
for every `epsilon>0`, only finitely many `d` have `t_d>=epsilon`.  Since a
nonzero projection in a finite factor has positive trace, the support

```text
{d:e_d!=0}=union_(n>=1){d:t_d>=1/n}
```

is countable.  Enumerate it so that the finite partial sums

```text
e_F=sum_(d in F)e_d
```

are uniformly `2`-Cauchy.  They are contractions, so completeness gives a
projection `e in M` with `p_de=e_d` and zero fibre at `infinity`.
Fibrewise functional calculus and faithfulness of the uniform `2`-norm give

```text
b <= eta 1 + e.                                         (UCF6)
```

Thus `psi(b)<=eta+psi(e)`.

## 4. Cofinite orthogonal replication

Fix `m>=1`.  The set

```text
F_m={d:m t_d>1}
```

is finite.  For `d notin F_m`, choose in the factor `p_dM` partial
isometries `v_(1,d),...,v_(m,d)` with common initial projection `e_d` and
pairwise orthogonal ranges.  Set them to zero on `F_m`.  As in Step 3, for
each `i` the nonzero coordinates form a countable set and the finite central
sums converge uniformly in `2`-norm to an element `v_i in M`.  Therefore

```text
v_i^*v_i=e(1-p_(F_m)),
sum_(i=1)^m v_iv_i^* <=1.                               (UCF7)
```

The finite central correction is `psi`-null by `(UCF4)`.  Traciality and
`(UCF7)` yield

```text
m psi(e)=psi(sum_i v_iv_i^*)<=1.
```

Since `m` is arbitrary, `psi(e)=0`.  Equation `(UCF6)` and then
`eta->0` give `psi(b)=0`.  Thus `psi` annihilates `K_infinity`, factors
through the finite-factor fibre at `infinity`, and equals its unique trace.

Combining this with `(UCF3)--(UCF4)` proves `(UCF1)` for `(UCF2)`.  The
finite clopen decomposition from Step 1 proves the general case.  Finally,
every functional in `(UCF1)` obeys

```text
|integral E(a)dmu| <= ||a||_(2,u)
```

by Cauchy--Schwarz, so all the traces obtained are uniformly `2`-norm
continuous.

---
rg: 2
id: literal-antiphase-branches-recreate-regular-character-packing
kind: claim
title: Literal pairwise-antiphase branches recreate the regular character-packing ceiling
distinct_from:
  pairwise-antiphase-covariance-controls-cross-gram: That proves the analytic cross-Gram payment once opposite phases are supplied on compressed transports; this proves that implementing those phases by ordinary conjugacy acts on the whole literal Reynolds source and restores the canonical capacity obstruction.
  btb-three-line-tree-retains-multiplicity-return-gauge: That shows separate edge covariance is too weak because its multiplicity gauges align; this shows the most direct cross-edge antiphase repair is too strong and kills or globally packs the source packet.
  canonical-btb-static-packing-has-capacity-ceiling: That computes the ceiling for separately postulated orthogonal BTB translates; this derives their orthogonality automatically from pairwise antiphase conjugacy and applies to any finite source character.
---

**ESTABLISHED CROSS-EDGE FIREWALL.**  Let `A<=G` be finite, let `chi` be a
one-dimensional character of `A`, and put

```text
e_chi=|A|^(-1) sum_(a in A) conjugate(chi(a)) a.       (LAP1)
```

Let `c` be a projection commuting with the construction and satisfying
`e_chi<=c`.  Consider `L` branch words `u_1,...,u_L`.  The direct
ordinary-group implementation of pairwise antiphase introduces, for every
`i<j`, an involution `r_ij` and elements `a_(i,ij),a_(j,ij) in A` with

```text
u_i^(-1) r_ij u_i=a_(i,ij),     chi(a_(i,ij))=+1,
u_j^(-1) r_ij u_j=a_(j,ij),     chi(a_(j,ij))=-1.      (LAP2)
```

Put `p_i=u_i e_chi u_i^(-1)`.  Fourier inversion and `(LAP2)` give

```text
r_ij p_i=+p_i,              r_ij p_j=-p_j.             (LAP3)
```

The positive and negative spectral spaces of one involution are
orthogonal, hence

```text
p_i p_j=0                    (i!=j).                    (LAP4)
```

If all branch words preserve `c`, then `p_i<=c`, and every tracial
representation satisfies the exact packing inequality

```text
L tau(e_chi)=sum_i tau(p_i)<=tau(c).                   (LAP5)
```

In particular, in the canonical group trace, injectivity of `A` gives

```text
tau_G(e_chi)=1/|A|,
L<=|A| tau_G(c).                                      (LAP6)
```

The same conclusion holds for a higher-dimensional irreducible character
after replacing `1/|A|` by its central-isotypic Plancherel mass; using a
minimal matrix coefficient gives the corresponding `dim(chi)/|A|` mass.

Now let `Q` be an analytic reached carrier reducing `A`, and let

```text
F=Q e_chi.                                             (LAP7)
```

The literal antiphase branches do make the ranges `u_i F u_i^*` pairwise
orthogonal, but each is a subprojection of `p_i`.  Their complete capacity
ledger is therefore already dominated by `(LAP5)`:

```text
sum_i tau(u_i F u_i^*)=L tau(F)
 <=sum_i tau(p_i)<=tau(c).                             (LAP8)
```

Thus the pairwise-antiphase trick has gained no matrix-only mass.  Choosing
more branches than `(LAP5)` permits cannot create a finite-dimensional-only
defect: in the faithful left regular representation it forces `e_chi=0`, so
the extra relators have destroyed the embedded source subgroup or the
nontrivial coefficient root needed by the BTB detector.

This also explains why allowing a different involution for every pair does
not evade character capacity.  For each fixed branch `i`, all incident
target involutions are conjugated by the same `u_i` into `A`; consequently
its whole literal source character already has the prescribed joint phases.
Noncommutativity among unrelated pair tags changes neither `(LAP3)` nor the
global orthogonality `(LAP4)`.

The sharp surviving interface is a **compressed antiphase two-cell**.  It
would have to prove, only for the representation-dependent contractions

```text
T_i=Q u_i Q e_chi,
```

the opposite-phase residuals used by
`pairwise-antiphase-covariance-controls-cross-gram`, without making the full
projections `u_i e_chi u_i^*` opposite eigenspaces in the group algebra.
Such a relation is not finite-subgroup conjugacy: it must read the analytic
carrier or an equivalent matrix-coordinate cross-Gram.  Separate covariance
is too weak by the BTB tree gauge no-go, while literal covariance is too
strong by `(LAP5)`.

DERIVATION
literal-antiphase-regular-packing-proof


---
rg: 2
id: cyclic-hull-antiphase-has-propagation-or-radius-firewall
kind: claim
title: Finite cyclic-hull antiphase either overpropagates from the seed or misses most of the hull
distinct_from:
  literal-antiphase-branches-recreate-regular-character-packing: That treats full conjugacy on a finite-subgroup character and derives exact Reynolds packing; this treats the proposed localization through the reached cyclic hull and separates centralizer propagation from finite-radius support formulas.
  btb-three-line-tree-retains-multiplicity-return-gauge: That aligns anonymous multiplicity gauges when no mixed row is present; this allows a mixed phase row but proves that the two direct ways of making it read the analytic reached hull are respectively too global and too local.
  finite-radius-active-character-packets-do-not-collapse-the-mark: That gives regular character extensions for finite affine-Leavitt windows; this gives an elementary dihedral cyclic-hull obstruction and an exact propagation lemma for commuting phase tags.
---

**ESTABLISHED LOCALIZATION FIREWALL.**  Let `S={s_1,...,s_k}` be a fixed
finite family of unitaries in a finite-dimensional Hilbert space and let `P`
be a projection.  Write

```text
Q=join_(g in <S>) gPg^*                                  (CHP1)
```

for the smallest `S`-reducing projection containing `P`.

First consider the centralizer implementation.  If an involution `R`
satisfies

```text
[R,s_j]=0       (1<=j<=k),             RP=epsilon P,
epsilon in {+1,-1},                                      (CHP2)
```

then

```text
RQ=epsilon Q.                                            (CHP3)
```

Indeed `R(gP)=g(RP)=epsilon gP` for every word `g`, and the ranges `gP`
span `Q`.  Thus centralizing the reducer is a finite and exact way to make a
target phase preserve the analytic cyclic hull, but a phase authenticated on
the named seed propagates to the **whole** cyclic component.  It cannot
distinguish a proper payload cut `F=Qe` unless that cut is already a sum of
cyclic components.  Pairwise opposite phases obtained this way orthogonalize
the whole corresponding cyclic components and return to ordinary trace
packing, more strongly than the desired compressed-antiphase estimate.

The other direct implementation is a finite support or tight-frame formula
for `Q`.  No such formula is dimension-uniform.  It already fails for the
infinite-dihedral reducer

```text
D_infty=<s,t | s^2=t^2=1>.                              (CHP4)
```

For every `d`, represent its quotient `D_(2d)` on `ell^2(Z/d)` by

```text
s delta_n=delta_(-n),             t delta_n=delta_(1-n),
P_d=|delta_0><delta_0|.                                  (CHP5)
```

The product `ts` is the cyclic shift, so the cyclic hull in `(CHP1)` is

```text
Q_d=I_d.                                                 (CHP6)
```

But for every fixed finite word set `W subset D_infty`,

```text
H_(W,d)=sum_(w in W) rho_d(w)P_d rho_d(w)^*,
rank(H_(W,d))<=|W|,
tau_d(supp(H_(W,d)))<=|W|/d.                            (CHP7)
```

Hence neither `supp(H_(W,d))=Q_d` nor a tight-frame lower bound
`H_(W,d)>=kappa Q_d` with fixed `kappa>0` can hold for all `d`.  The same
conclusion holds for a fixed word-radius ball, and for any fixed positive
linear combination of its translates.  Products and spectral cuts of these
commuting rank-one translates remain supported on the same finite orbit
window.

Apply this to a reached BTB carrier.  By construction it is the cyclic hull
of finitely many named seed/range projections under the finitely generated
shared BCS/packet reducer.  Relations centralizing that reducer can certify
that a pair tag reduces `Q_sigma`, but seed-local phase relations then obey
`(CHP3)` and lose the contextual cut `F_sigma=Q_sigma e`.  Replacing
centralization by a finite support polynomial does not name `Q_sigma`
uniformly, by `(CHP4)--(CHP7)`.  Consequently a valid compressed-antiphase
cell cannot be only

```text
centralize the reducer + fix a phase on a named seed,
```

and cannot be a fixed-radius support/tight-frame surrogate for the hull.
It must contain a genuinely mixed corner loop coupling the contextual
Reynolds atom to reducer transport (or an equivalent finite-dimensional-only
matrix-coordinate identity).  This claim does not rule out such a loop; it
proves exactly why the two natural cyclic-hull localizers do not supply it.

DERIVATION
cyclic-hull-antiphase-localization-proof


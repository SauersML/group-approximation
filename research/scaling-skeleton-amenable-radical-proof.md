---
rg: 2
id: scaling-skeleton-amenable-radical-proof
kind: route
title: Read the dilation from the amenable radical of the telescope quotient
target: scaling-skeleton-quotients-pairwise-nonisomorphic
requires:
  - literal-base-presentation-complete
artifacts:
  - research/artifacts/scaling-skeleton-amenable-radical-2026-08-30.md
  - GroupApproximation/Monsters/LiteralBaseCompleteness.lean
  - GroupApproximation/Monsters/AffineSL3Scaling.lean
  - GroupApproximation/Sofic/ScalingFamilyPresentation.lean
---

Killing `c_m` makes the marked word trivial, so all marked-centrality
relators disappear.  What remains is the ascending HNN presentation of

```text
B ~= Z^3 semidirect SL_3(Z)
```

along `alpha_m(a,s)=(ma,s)`.  Direct-limit normal form gives

```text
V_m ~= (colim(B,alpha_m)) semidirect Z
    ~= (Z[1/m]^3 semidirect SL_3(Z)) semidirect Z
    ~= Z[1/m]^3 semidirect (SL_3(Z) x Z).
```

Put `A_m=Z[1/m]^3` and `R_m=A_m semidirect_m Z`.  It is solvable and
normal, and `V_m/R_m~=SL_3(Z)`.  The Margulis normal subgroup theorem for
the irreducible higher-rank lattice `SL_3(Z)` says every normal subgroup
is finite central or finite index.  Its center is trivial, and an amenable
normal subgroup cannot have finite index because `SL_3(Z)` is
nonamenable.  Hence `Rad_am(SL_3(Z))=1`.  The image of any amenable normal
subgroup of `V_m` in this quotient is trivial, while `R_m` itself is
amenable and normal.  Therefore `Rad_am(V_m)=R_m`.

Writing `A_m` additively and `t` for the `Z` generator,

```text
[t,a]=(m-1)a.
```

Thus

```text
[R_m,R_m]=(m-1)A_m,
R_m^ab ~= Z direct_sum (A_m/(m-1)A_m).
```

Since `gcd(m,m-1)=1`, localization at `m` does not change reduction
modulo `m-1`:

```text
Z[1/m]/(m-1)Z[1/m] ~= Z/(m-1)Z.
```

Therefore `Tor(R_m^ab)~=(Z/(m-1)Z)^3`, of order `(m-1)^3`.  Amenable
radicals are characteristic, so an isomorphism `V_m~=V_n` identifies
these torsion subgroups and forces `m=n`.

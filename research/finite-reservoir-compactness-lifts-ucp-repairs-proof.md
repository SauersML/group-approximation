---
rg: 2
id: finite-reservoir-compactness-lifts-ucp-repairs-proof
kind: route
title: Norm the reservoir by finitely many finite-dimensional representations, then take a compact intersection
target: finite-reservoir-compactness-lifts-ucp-repairs
requires: []
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
---

Write `V:=L(E,L)`, a finite-dimensional vector space because both `E` and `L`
are finite-dimensional.

**Step 1 (a finite norming packet).**  `A` is RFD, so the direct sum of all
its finite-dimensional representations is faithful, hence isometric:
`||x||=sup_rho ||rho(x)||` over finite-dimensional `rho`.  Let `S` be the unit
sphere of `L`, compact because `L` is finite-dimensional.  For each `x in S`
pick a finite-dimensional `rho_x` with `||rho_x(x)||>1/2`; by continuity of
`y |-> ||rho_x(y)||` this persists on a neighbourhood of `x`, and finitely many
such neighbourhoods cover `S`.  The corresponding finite packet
`R_0={rho_1,...,rho_m}` satisfies

```text
||x|| <= 2 max_(j<=m) ||rho_j(x)||       for all x in L.    (FRP1)
```

Note this is a statement about `L` only, and `L` is fixed before any packet is
chosen -- this is the exact point at which the uniformity hypothesis is spent.

**Step 2 (uniform bound on the repairs).**  For a finite packet `R` containing
`R_0`, let `d_R` be as in `(FR2)`.  Each `rho_j o (t+d_R)` is ucp, hence
contractive, so for `x in E`

```text
||rho_j(d_R(x))|| <= ||rho_j((t+d_R)(x))||+||rho_j(t(x))||
                  <= ||x||+||t|| ||x||.
```

Since `d_R(x) in L`, `(FRP1)` gives `||d_R(x)|| <= 2(1+||t||) ||x||`, so

```text
||d_R|| <= C:=2(1+||t||)                                    (FRP2)
```

for **every** finite packet `R` containing `R_0`.

**Step 3 (compact intersection).**  For a finite packet `R` put

```text
D_R:={d in V : ||d|| <= C,  rho o (t+d) ucp for all rho in R}.
```

Each `D_R` is closed: for fixed `rho` and fixed `k`, the set of `d` with
`(rho o (t+d))^(k)` positive on the positive cone of `M_k(E)` is an
intersection of closed conditions, since `d |-> rho o (t+d)` is affine and
continuous and positivity is closed; unitality is one linear equation.  Each
`D_R` is bounded by construction, hence compact in the finite-dimensional `V`.
Each is nonempty: apply `(FR2)` to `R u R_0` and use `(FRP2)`.  Finally
`D_(R_1 u ... u R_p) subset D_(R_1) inter ... inter D_(R_p)`, so the family
`{D_R}` has the finite intersection property.  By compactness

```text
D:=inter_R D_R != empty set,                                (FRP3)
```

the intersection running over all finite packets of finite-dimensional
representations.  Fix `d in D` and set `s:=t+d`.

**Step 4 (from all finite-dimensional representations to `A`).**  By
construction `rho o s` is ucp for **every** finite-dimensional representation
`rho` of `A`.  Let `pi:=(+)_rho rho` over all of them; `pi` is a faithful
representation of `A` because `A` is RFD, so `pi` and `pi^(k)` are isometric
`*`-isomorphisms onto their images and reflect positivity in both directions.
For `[x_(ab)] in M_k(E)` positive, `pi^(k)([s(x_(ab))])=(+)_rho
[(rho o s)(x_(ab))]` is positive since each `rho o s` is `k`-positive;
therefore `[s(x_(ab))]` is positive in `M_k(A)`.  So `s` is completely
positive.  Unitality: `rho(s(1))=1` for all `rho`, hence `pi(s(1))=pi(1)` and
`s(1)=1`.  Self-adjointness is then automatic (each `rho o s` is
`*`-preserving, and `pi` is faithful).

Finally `d(E) subset L subset I`, so `q s = q t = id_E`.  This is `(FR3)`.

**Two remarks on what the proof does not need.**  It never uses that the `d_R`
are self-adjoint or unital -- both come out of the ucp conditions in the limit.
And it never uses separability, nuclearity or exactness of `A`, only RFD; in
particular it applies verbatim to non-exact `A`.

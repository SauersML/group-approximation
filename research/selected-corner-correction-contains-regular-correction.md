---
rg: 2
id: selected-corner-correction-contains-regular-correction
kind: claim
title: Correcting a selected regular lattice corner is already the full regular-microstate correction problem
distinct_from:
  sl3z-regular-microstates-are-congruence-correctable: that asks for correction of the whole regular-trace lattice microstate; this proves that selecting a positive-density approximately reducing corner does not weaken that problem unless cross-corner actor data is used simultaneously.
  stable-representation-block-rounding: that rounds an almost-reducing projection after the ambient tuple has already been corrected to a genuine representation of a stable group; this shows why obtaining that ambient correction is still load-bearing for the regular lattice.
  character-rigidity-equals-hyperfinite-hs-stability: that corrects amenable-limit traces; this computes that the selected four-atom traces in the G_cc canonical model are regular and hence nonamenable.
---

Let `C=SL_3(Z)` with a fixed finite presentation.  Consider the following
putatively weaker correction principle.

> **Selected regular-corner correction.**  If `U_n` is an approximate
> representation of `C` and `P_n` is a projection of trace bounded away from
> zero such that
>
> ```text
> max_(s in S_C)||[P_n,U_n(s)]||_2 ->0,                 (SCC1)
> tr(P_n w(U_n))/tr(P_n) -> delta_(w,e)                 (SCC2)
> ```
>
> for every fixed lattice word `w`, then the compressed tuple on `P_n H_n`
> can be corrected, in normalized HS norm (with the corresponding flexible
> or projective convention), to genuine representations of `C`.

This principle already implies the matching version of
`sl3z-regular-microstates-are-congruence-correctable`.  Indeed, start with
an arbitrary regular-trace microstate `U_n` of `C`, amplify it by one
external bit,

```text
Utilde_n(s)=U_n(s) tensor I_2,
P_n=I tensor e_11.                                      (SCC3)
```

Then `(SCC1)` is exact, `tr(P_n)=1/2`, and `(SCC2)` is precisely the regular
trace of `U_n`.  A correction of the selected corner is a correction of the
original tuple.  The same reduction preserves flexible padding and
projective correction.

Thus selecting one positive-density reducing block does not bypass the
known regular-sector wall.  Any genuinely weaker theorem for `G_cc` must
use the `h`-transport and several four-atom/parahoric corners **during** the
correction; it cannot first correct each corner from its lattice restriction
alone.

## The native four atoms are regular, not hyperfinite

Let `c` and `d=hch^-1` be the two commuting canonical lamp involutions and
put

```text
E_(epsilon,eta)=(1+epsilon c)(1+eta d)/4.               (SCC4)
```

Whenever a subgroup `D<=C` fixes both lamp coordinates, each `E_(epsilon,
eta)` commutes with `D`.  For nonidentity `g in D`, canonical trace gives

```text
tr(E_(epsilon,eta)u_g)
 =1/4[tr(u_g)+epsilon tr(cu_g)+eta tr(du_g)
                 +epsilon eta tr(cdu_g)]=0,             (SCC5)
```

because the four displayed group elements are nonidentity (and distinct in
the native lamp group).  Also `tr(E_(epsilon,eta))=1/4`.  Hence the
normalized trace on every positive four-atom corner restricts to the regular
trace of `D`.

For the finite-index Kazhdan parahorics used in the arithmetic hexagon this
corner limit is nonamenable.  The unconditional hyperfinite-HS stability
coming from character rigidity therefore does not apply.  Spectral cutting
the selector changes neither this trace computation nor the need to correct
a regular-sector lattice microstate.

The weakest plausible correction interface is consequently a **coupled
multi-corner theorem**: six parahoric restrictions and their literal
`h`/Weyl transitions must be corrected on one joint mass ledger.  Once such
genuine endpoint actions exist, `kazhdan-polar-rounding-produces-supported-
gallery-edges` handles the edge intertwiners.  One-corner correction by
itself is not a simplification.

---
rg: 2
id: sofic-safe-finite-presentation-compiler
kind: claim
title: Compile the parametric switch to finite presentations without losing its sofic branch
distinct_from:
  mf-safe-finite-presentation-compiler: that preserves the operator-MF positive branch through a tensor-synchronized rope, an operator-norm argument with no permutation analogue; this must preserve soficity, and the same rope is an HNN extension over a non-amenable subgroup whose soficity is unknown.
  arbitrary-forbidden-seed-hereditary-property-switch: that is the countably generated switch; this is the finite-output compiler it explicitly declines to claim.
  hyperlinear-recognition-undecidable: that concerns hyperlinearity and is equivalent to the existence of a non-hyperlinear group; this concerns soficity, where the negative seed already exists and only the positive branch is at stake.
---

OPEN.  Wanted: a total computable map `e |-> P_e` into finite presentation
codes such that

```text
e in INF  ==>  Carrier(P_e) is sofic,
e in FIN  ==>  a fixed finitely presented nonsofic group E embeds in Carrier(P_e).
```

The negative branch is free: any Higman-type compiler that embeds the
two-generator recursive group `B2(S_e)` of
[[sofic-recognition-two-generator-recursive-is-pi2-complete]] embeds `E` on
`FIN`.  The whole difficulty is the positive branch: on `INF` the compiled
group must be sofic although it is *not* residually finite and its
presentation depends on `e`.

## What is known and where it stops

* The MF compiler [[mf-safe-finite-presentation-compiler]] passes through
  `Gamma_e = <K_e, v | [v, L_e] = 1>` with `K_e` a product of free groups and
  `L_e` containing a Mikhailova subgroup of a non-residually-finite group.
  `Gamma_e = K_e *_{L_e} (L_e x Z)` is an amalgam over a **non-amenable**,
  **profinitely dense-in-the-wrong-way** subgroup: `L_e` is not closed in the
  profinite topology of `K_e` (it would be iff the Higman-embedded group
  were residually finite), so finite quotients cannot separate a pinch
  `v k v^-1 k^-1`, `k in K_e \ L_e`, and the standard sofic closure theorems
  (Elek--Szabo, Paunescu: amalgams and HNN extensions over amenable
  subgroups) do not apply.  Nor can they be expected to be tight: every
  Higman-type benign witness has `L n F = N_e`, a free group of infinite
  rank, so the edge is never amenable.
* The Fell-absorption step of the MF rope has an exact permutation analogue:
  for a finite group `Q` acting on itself by left translation and on any
  finite `Q`-set `Y`, the diagonal `Q`-set `Q x Y` is isomorphic to `|Y|`
  copies of the regular `Q`-set via `(x, y) |-> (x, x^-1 y)`.  So the two
  edge embeddings of the final rope become **exactly conjugate by a
  permutation** after tensoring with the synchronizing finite quotients.
  What is missing is the sofic analogue of Ueda's reduced HNN normal form:
  exact conjugacy of the edges in one sofic approximation of the base does
  not by itself yield a sofic approximation of the HNN extension when the
  edge subgroup is non-amenable (the special case `<B, t | [t, S] = 1>`,
  with `S <= B` arbitrary and `B` sofic, is already open).

## Consequence if established

`SOFIC_fp` becomes `Pi^0_2`-complete
([[sofic-recognition-finite-presentations-is-pi2-complete]]), closing the
one gap left by [[sofic-recognition-finite-presentations-arithmetical-position]].
A sofic-preserving Higman embedding theorem for recursively presented sofic
groups would do it; that theorem is not in the literature and would be of
independent interest, the residually finite version being a known open
question.

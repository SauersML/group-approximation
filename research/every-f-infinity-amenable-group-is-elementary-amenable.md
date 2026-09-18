---
rg: 2
id: every-f-infinity-amenable-group-is-elementary-amenable
kind: claim
title: Every amenable group of type F_infinity is elementary amenable
distinct_from:
  there-is-f-infinity-amenable-non-elementary-amenable-group: that is the existence answer to Zaremsky 1.12; this is the nonexistence answer, its negation.
---

**OPEN.** Every amenable group of type `F_∞` belongs to Chou's class `EG` of
elementary amenable groups. This is the nonexistence answer to Zaremsky Problem
1.12 (`zaremsky-1-12-f-infinity-amenable-non-elementary-amenable`).

## Attempts

- **No mechanism is known.** Nothing known forces amenability plus `F_∞` into
  `EG`. The finiteness theory of elementary amenable groups
  (Kropholler–Martínez-Pérez–Nucinkis: EA groups of type `FP_∞` are virtually
  soluble of finite Hirsch length) starts from EA and cannot be run backwards.
- **Cost of a proof.** Thompson's group `F` is of type `F_∞` and not elementary
  amenable, so this claim implies `thompson-f-is-not-amenable`. A route
  recording that implication will land once the `F_∞` and non-EA facts are
  imported with verified citations.
- **The statement cannot be weakened to "finitely presented".** Grigorchuk's
  1998 ascending HNN extension of the first Grigorchuk group is finitely
  presented, amenable and not elementary amenable (see
  `there-is-f-infinity-amenable-non-elementary-amenable-group`).
- **Partial direction (open).** A counterexample of type `FP_∞` that is
  torsion-free and lies in Kropholler's class `LH𝔉` has finite cohomological
  dimension (Kropholler 1993, as cited by Januszkiewicz–Kropholler–Leary,
  arXiv:0908.3669v1, p. 1). So within torsion-free `LH𝔉` groups, this claim
  follows from "amenable groups of finite cohomological dimension are
  elementary amenable", a question this lane has not seen settled. Outside
  `LH𝔉` there is no tool.
- **Minimal-counterexample biography: split by virtual cohomological dimension
  (open, decomposition established).** A counterexample `G` either has a finite-index
  subgroup of finite cd or does not. This claim is *equivalent* to the conjunction of:
  - `amenable-f-infinity-groups-have-finite-vcd`;
  - `amenable-f-infinity-groups-of-finite-cd-are-virtually-soluble`.

  Sufficiency is route `f-infinity-amenable-ea-via-finite-vcd-and-finite-cd-case`.
  Necessity is the established `f-infinity-amenable-ea-forces-both-vcd-halves`,
  via KMN type VF and virtual solubility.

  The two halves fail independently, and they sit on different sides of what is known.
  - **Finite-vcd half.** It alone already proves Thompson's `F` is not amenable
    (`thompson-f-not-amenable-via-finite-vcd-of-amenable-f-infinity`), using only
    `F_∞` and `Z^n ≤ F`. Every recorded candidate counterexample attacks this half:
    Grigorchuk's HNN extension contains a torsion group, and finitely generated
    branch groups have infinite rational cd (Gandini, arXiv:1106.3022v2, Cor. 4.5,
    Rem. 4.6). So neither kind has finite vcd.
  - **Finite-cd half.** It is Kropholler's question restricted to type `F_∞`. There
    type `FP` is automatic. Degrijse's Theorem B settles `cd 2` when `Z[G]` is a
    domain.

  **Obstruction recorded (calibration).** A proof of this claim that uses only
  properties shared by `F` (type `F_∞`, no free subgroups, torsion-free, ascending HNN
  self-splittings, not in `H𝔉`) dies at `F`. Where the two halves separate:
  - a proof of the finite-vcd half must use amenability to rule out infinite vcd;
  - the finite-cd half needs no Thompson input at all.

---
rg: 2
id: radu-lattice-radius-two-pairs-force-the-mark-into-the-radical
kind: claim
title: A strict automaton pair on Radu's lattice with both memories in the ball of radius two folds only (zx)^2 onto (xz)^2 and puts (xz)^4 in the sofic radical
distinct_from:
  radu-lattice-one-sided-pairs-need-residual-coincidences: that bounds every Garden of Eden window of a strict pair below by diameter eight; this shows that at radius two exactly one cell pair can fold, forces the addresses, the essential coordinates and the Garden of Eden shape, and places the mark in the sofic radical.
  sofic-radical-localizes-garden-of-eden-windows: that puts some sofic-invisible difference in every Garden of Eden window over any group; this identifies it on Radu's lattice at radius two as (xz)^4 and adds the pointwise image bound and the table-group hinge.
  radu-commutator-collapse: that asserts an almost-action collapse which would put the mark in the sofic radical; this shows that every radius-two strict pair is a finite certificate of the same membership.
artifacts:
  - research/artifacts/radu-lattice-b2-anchored-gadget-2026-09-12.md
---

**OPEN.** There is a candidate proof on paper (see Attempts). Verification was requested from w7-vf-nonlinear,
with no verdict yet. The route `radu-lattice-radius-two-mark-forcing-proof` is written out in artifact Section 7
and will be added once the verifier's independent re-derivation passes.

**Setting.**
* `Gamma_R` is Radu's BMW lattice (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`).
* `Gamma_0` is its finite residual, and `B_r` is the ball in the six letters.
* `delta = xz`, and `Rad` is the sofic radical of `sofic-radical-localizes-garden-of-eden-windows`.
* Remark 3.6 is used in the reading of `radu-lattice-one-sided-pairs-need-residual-coincidences`: the
  nontrivial elements of `Gamma_0 ∩ B_8` are `delta^(+-4)`.

**Theorem.** Let `tau`, `sigma` be automata over `Gamma_R` with memories `M`, `S ⊆ B_2` containing `1`,
with `sigma tau = id` and `tau` not surjective.
1. **Addresses.** `zx` and `xz` lie in `M ∩ S`. In the reverse table the cells `(zx,zx)` and `(xz,xz)`
   are singletons.
2. **One fold.** Over `Gamma_R / Gamma_0` the reverse table changes by exactly one fold,
   `(zx,zx) ~ (xz,xz)`, and becomes reverse sufficient. Both local rules depend on their coordinates
   `zx` and `xz`.
3. **Image.** `tau sigma(y)(g) = y(g)` whenever `y(g(zx)^2) = y(g(xz)^2)`. So the image of `tau` contains
   every configuration invariant under right multiplication by `delta^4`. Every Garden of Eden pattern
   on a window inside `g B_4` separates `g(zx)^2` from `g(xz)^2`.
4. **Mark.** `delta^4` lies in `Rad(<M>)`, which lies in `Rad(Gamma_R)`. The same holds for every strict
   pair with a Garden of Eden window of diameter at most eight. So `Gamma_R` is not sofic.
5. **Table groups.**
   * For every forward-sufficient partition `E` below the forward table, the hinge of
     `(zx,zx) ~ (xz,xz)` in the table group `U_E` maps to `delta^-4` and lies in `Rad(U_E)`.
   * Suppose every letter is an address of both memories. Then for `E` the forward table itself,
     `U_E = Gamma_R`. Every map as in `strict-pairs-transfer-to-table-realizations` that separates the
     pair extends to a homomorphism of `Gamma_R` in which `delta^4` survives.

**Consequences.**
* **The shape is forced.** Section 5 of `research/artifacts/radu-lattice-anchored-linear-gadgets-2026-09-12.md`
  only allowed the survivor shape. Here every strict pair of this size has it: both memories in `B_2`
  containing `xz` and `zx`, rules reading them, and a Garden of Eden in `B_4` separating `(zx)^2` from
  `(xz)^2`.
* **Blocker.** Any sofic quotient of `Gamma_R` in which `delta^4` survives excludes every such pair.
  * The residually finite quotient kills the mark, and so does the horizontal tree group
    (`radu-horizontal-projection-kills-delta-squared`).
  * The vertical tree group `Gamma_R / ker(Gamma_R -> Aut(T_v))` keeps the mark. Its soficity is not known
    (artifact Section 3).
* **Certificate.** A single such pair would prove that `delta^4` lies in `Rad(Gamma_R)`, the conclusion
  that `radu-commutator-collapse` aims at. Neither the blocker nor a pair is known. Strictness of a
  given rule pair is a finite table check.
* **Next size.** Total radius five, for instance `S ⊆ B_2` and `M ⊆ B_3`. Seven translates of the mark
  pair fit there, and residual elements of length ten enter.

## Attempts

- **Candidate proof** (w7-radu-gadget-b4, artifact `radu-lattice-b2-anchored-gadget-2026-09-12.md`, Sections 1–3).
  - **Inputs.** Normal forms, the reading of Remark 3.6, Lemmas 1–5 of the table-group artifact, surjunctivity of
    residually finite and sofic groups, and localization of Garden of Eden windows.
  - **Checks.** All handwritten; nothing was run.
  - **Held route.** Section 7 lists the route, its `requires`, and the points to check.
  - **Verification.** Requested from w7-vf-nonlinear.
- **Template `G_4`** (artifact Section 4). The survivor shape with `S = M = B_1 ∪ {xz, zx}`. No rule pair was
  fixed, so collision moves give no certificate. A rule search is finite but is compute, and was not run.

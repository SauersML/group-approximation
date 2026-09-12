---
rg: 2
id: glebsky-verbatim-hs-transport
kind: route
title: Rerun Glebsky's permanence proof with U(n) and normalized HS in place of finite groups
target: hyperlinear-wreath-model
requires: []
artifacts:
  - notes/TRUE_GLEBSKY_HS_TRANSPORT_AUDIT.md
---

# Rerun Glebsky's proof in normalized Hilbert–Schmidt

The attractive reading of `weakly-sofic-not-sofic`: Glebsky's permanence
theorem has no hypothesis on the coset action, which is exactly the hypothesis
Kun–Thom Corollary D denies to every hyperlinear wreath theorem, so transport
the proof to `(U(n), ‖·‖₂)` and get hyperlinearity of `W` directly.

**Dead**, by `glebsky-hs-transport-step-classification`. Four of the six steps
do transport — Kaluzhnin–Krasner, the residual reduction, the locality lemma
and the Tychonov limit are all metric-free and class-free. The two that do not
are the equational characterization (Corollary 19 of arXiv:1506.06940, stated
only for `K ⊆ Fin`) and the universal-solution lemma, which needs the system to
be solvable in a specific **finite** auxiliary group. The system `x²a⁻¹` is
solvable in every `U(n)` and not in `ℤ/2`, so the unitary system class does not
supply what the universal solution consumes.

**What the route is worth even though it is dead.** It relocates the whole
question, and the relocation is the useful output. Glebsky's freedom is not
"metric surgery adapted to the extension" — his permanence proof contains no
metric at all. His freedom is that the class `Fin` is closed under the auxiliary
construction `D_N ⋊ G_N` and admits a length manufactured after the fact
(Lemma 3 of the 2017 paper). Hyperlinearity has neither property. So the
surviving formulation is not "redo the proof" but
`hilbert-embeddable-witness-for-kun-thom-wreath`: take the witnesses Glebsky
already produces and ask whether the length can be chosen conditionally
negative definite. `hilbert-embeddable-length-lp-feasibility` makes that a
finite linear program.

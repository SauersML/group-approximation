---
rg: 2
id: clifford-witness-has-no-hyperfinite-marked-representation
kind: claim
title: The Clifford witness W and the block-commuting quotient of E have no hyperfinite representation with the mark at −1
invalidates: [non-mf-unitary-subgroup-via-clifford-witness]
distinct_from:
  commuting-lamp-quotient-not-mf: that is the operator-norm statement, the sign lies in the MF residual of the witness; this is the Hilbert--Schmidt-exact statement: no finite injective von Neumann algebra receives the witness with the sign at −1, so the witness does not embed in U(R).
  literal-group-embeds-in-hyperfinite-unitary-group: that is the still-open statement for the literal group E itself, whose lamp kernel is a free amalgam; this settles the two quotients in which lamps at distinct blocks commute or anticommute, where the marked lamp algebra is UHF.
  literal-canonical-shift-model-stops-at-r-omega: that excludes only the canonical regular crossed-product realization (a character regular on the telescope quotient V); this excludes every finite injective covariant representation of the two commuting-lamp witnesses whatever the character on V, by proving the action is properly outer and then forcing the regular character through hyperfinite-covariant-obstruction-lemma.
  kazhdan-groups-in-hyperfinite-unitary-group-are-rf: that removes Kazhdan groups from U(R); these witnesses are not Kazhdan-obstructed (Σ is residually finite), and are removed by outerness of the lamp action instead.
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
  - non_mf_group_notes.tex
---

Let `X = Σ/B` be the site set of `non_mf_group_notes.tex`, with
`Σ = Z[1/2]^3 ⋊ (SL_3(Z) × Z)` (the ascending HNN extension of
`B = Z^3 ⋊ SL_3(Z)` along doubling) acting on `X`, and let `ζ` be the
sign.  Consider

* the Clifford witness `W = Cl(X) ⋊ Σ` of Proposition `prop:witness`
  (`sofic-non-mf-witness`): lamps `c_ξ` at all sites, any two distinct
  lamps anticommute up to `ζ`;
* the block-commuting quotient `E_⊗ = C_⊗(𝒢) ⋊ Σ` of the literal group
  `E = C(𝒢) ⋊ Σ` (`literal-lamp-kernel-clifford-block-amalgam`), obtained
  by making lamps in distinct blocks commute.

Then every homomorphism from `W`, or from `E_⊗`, into the unitary group of
a finite injective von Neumann algebra with faithful normal trace sends
`ζ` to `1`.  In particular neither group embeds in `U(R)`, and neither can
witness `non-mf-subgroup-of-hyperfinite-factor-unitary-group`.

Since `ζ` generates the MF residual seen by every operator-norm matrix
model (`commuting-lamp-quotient-not-mf`), this is the Hilbert--Schmidt
counterpart of the manuscript's obstruction: the mark is invisible both to
norm-matrix coronas and to hyperfinite tracial representations.  The two
mechanisms are different — the corona argument uses property (T) of the
base and finiteness of matrix algebras; this one uses uniqueness of the
trace on the marked lamp algebra, outerness of the site permutations on
its hyperfinite completion, and nonamenability of `SL_3(Z) ≤ Σ`.

Soficity of `W` (`sofic-non-mf-witness`) gives `W ↪ U(R^ω)` with `ζ ≠ 1`;
so the sign survives in the ultrapower of `R` but in no finite injective
algebra.  The argument fails in `R^ω` exactly at the last step: `R^ω` is
not injective.

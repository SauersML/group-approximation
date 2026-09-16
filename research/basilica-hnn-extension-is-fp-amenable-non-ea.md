---
rg: 2
id: basilica-hnn-extension-is-fp-amenable-non-ea
kind: claim
title: The Basilica group embeds in a finitely presented ascending HNN extension that is amenable and not subexponentially amenable, hence not elementary amenable
distinct_from:
  grigorchuk-hnn-extension-is-fp-amenable-non-ea: that records Grigorchuk's finitely presented HNN extension of the first Grigorchuk group, which is in SG and has finite subgroups of unbounded order; this records the Bartholdi–Virág extension of the torsion-free Basilica group, which is amenable but outside SG.
  there-is-torsion-free-f-infinity-amenable-non-ea-group: that asks for a torsion-free amenable non-EA group of type F_infinity; this records a finitely presented candidate whose finiteness beyond FP_2 is unknown.
---

**Literature import.** Let `B = ⟨a, b⟩` be the Basilica group, with `a = (1, b)` and
`b = (1, a)ε`, in the right-action convention of Bartholdi–Virág (arXiv:math/0305262v1). Let
`σ : B → B` be the endomorphism induced by the substitution `b ↦ a, a ↦ b^2`. Let

`B~ = ⟨B, t | t^(−1) g t = σ(g), g ∈ B⟩`

be the ascending HNN extension along `σ`. Then:

1. `B` embeds in `B~`.
2. `B~` is finitely presented. Bartholdi–Virág (Theorem 12) give
   `B~ = ⟨a, t | a^(t^2) = a^2, [[[a, t^(−1)], a], a] = 1⟩`, with `x^y = y^(−1) x y` and
   `[x, y] = x^(−1) y^(−1) x y`.
3. `B~` is amenable.
4. `B~` is not in Grigorchuk's class `SG` of subexponentially amenable groups. Since `EG ⊆ SG`,
   `B~` is not elementary amenable.

**Convention-free form of the presentation.** Put `b = t a t^(−1)`. Then
`[a, t^(−1)] = a^(−1) b` and `[[a, t^(−1)], a] = [b, a]`. So the second relator is `[[b, a], a]`,
which is equivalent to `[a, a^b] = 1`. So

`B~ = ⟨a, t | t^(−2) a t^2 = a^2, a commutes with b^(−1) a b, where b = t a t^(−1)⟩`.

This agrees with Lemma 11 of Bartholdi–Virág, `B = ⟨a, b | σ^n([a, a^b]), n ∈ N⟩`: in `B~` the
relator `σ^n([a, a^b])` is the conjugate `t^(−n) [a, a^b] t^n`. With the other commutator
convention, `[x, y] = x y x^(−1) y^(−1)`, the printed relator does not hold in `B`. Both facts are
checked by `experiments/basilica-hnn-2026-09-16/basilica_checks.py` (checks 1–2).

**What the import depends on.**

- Amenability of `B` (Bartholdi–Virág, Theorem 1).
- The infinite presentation of `B` (Grigorchuk–Żuk, IJAC 12 (2002), Proposition 9), which
  Bartholdi–Virág use for Lemma 11.
- `B ∉ SG` (Grigorchuk–Żuk 2002, Proposition 13), again as cited by Bartholdi–Virág.

The Grigorchuk–Żuk paper was not fetched by this lane. See the citation route for what was read.
Injectivity of `σ`, needed for item 1, is proved independently in
`basilica-group-is-torsion-free-and-contains-every-z-n`.

Import route: `basilica-hnn-extension-is-fp-amenable-non-ea-citation`. Finiteness beyond `FP_2`:
`basilica-hnn-extension-is-fp-infinity` (open).

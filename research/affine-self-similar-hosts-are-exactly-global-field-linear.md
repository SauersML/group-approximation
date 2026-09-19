---
rg: 2
id: affine-self-similar-hosts-are-exactly-global-field-linear
kind: claim
title: A finitely generated group embeds in a finitely generated affine self-similar group over Z_p or F_q[[π]] if and only if it is linear over a global field
distinct_from:
  affine-self-similar-groups-are-function-field-linear: that is the forward direction in characteristic p only; this adds the characteristic-zero forward direction and the converse embedding, so the class is characterized exactly.
  positive-char-polynomial-affine-groups-are-self-similar: that realizes affine groups over F_p[s_1..s_k] by FIBERED maps (v,a) -> (g<a>v + b<a>, a), whose linear part depends on parameter digits; those are not affine maps of O^m, which is how they reach transcendence degree k. This node says affine maps alone stop at transcendence degree 1.
  char-p-linear-groups-satisfy-permutational-boone-higman: that is BH for all char-p linear groups via the fibered hosts; this identifies which inputs the plain affine hosts can reach.
---

**ESTABLISHED** by the proof below (lane bh-free-25, 2026-09-18; elementary, not
reviewed). No novelty is claimed. Brunner–Sidki and Kapovich-style arithmetic arguments
cover related ground; they were not checked.

## Setting

- `O` is `Z_p`, or `F_q[[π]]`; `K ⊂ O` is `Q`, or `F_q(π)`.
- The alphabet is `(O/π)^d`, with digits in `{0, …, p−1}^d`, or `F_q^d`.
- An *affine self-similar group* is a group of maps `x ↦ Ax + b` of `O^d`, with
  `A ∈ GL_d(O)` and `b ∈ O^d`, that contains every section of its elements on the
  `π`-adic digit tree.
- For `x = v + πx'`, the section at `v` is `x' ↦ Ax' + (Av + b − c)/π`, where `c` is the
  digit of `Av + b`. The linear part is unchanged.

## Statement

For a finitely generated group `Γ`, the following are equivalent:
1. `Γ` embeds in a finitely generated affine self-similar group over some `O` (any `p`,
   `q`, `d`);
2. `Γ` embeds in `GL_n(E)` for a global field `E`, that is, a number field or a finite
   extension of `F_q(t)`.

The characteristic of `E` equals that of `O`. Groups in either class have word problem in
polynomial time.

## Proof

**(1 ⇒ 2).**
- Let `Z` list the entries of the generators, their inverses and their translation
  parts. Fix words for the sections at `v = 0, e_1, …, e_d`.
- Comparing translation parts gives `Z = C + π·P(Z)`, with `C` a vector of digit
  constants and `P` a polynomial over `Z` or over `F_q`.
- The Jacobian of `Y − C − πP(Y)` at `Z` has determinant in `1 + πO`, so it is nonzero.
- As in `affine-self-similar-groups-are-function-field-linear`, this gives
  `Ω_{K(Z)/K} = 0`, so `E = K(Z)` is finite separable over `K`. In characteristic `0`
  separability is automatic.
- Hence `Γ ≤ AGL_d(E) ≤ GL_{d+1}(E)`.

**(2 ⇒ 1).**
- *Choosing the place.* After a finite constant extension in characteristic `p`, choose a
  place `v` of `E` of degree one at which every entry of the generators of `Γ` and of
  their inverses is integral. Then `E_v = K_v` and `O_v = O`, with `π` a uniformizer; in
  characteristic `0` take `π = p`.
- *The ring.* Let `S` be the finite set of places `w ≠ v` where some entry has a pole or
  `π` has a zero or pole. Enlarge `S` so that `|S| ≥ 2`, and let `B = O_S`.
- *`B` is closed under the digit shift.* For `b ∈ B`, `D(b) = (b − b(0))/π` is integral at
  `v`, because `b ≡ b(0)` there. Its other new poles are at zeros of `π`, which lie in
  `S`. So `D(B) ⊆ B`, and `Γ ≤ GL_n(B)` with inverses.
- *A unit.* By the `S`-unit theorem, together with finiteness of the class group in
  characteristic `0`, there is `u ∈ B^×` whose zeros and poles fill `S`. Then `B` is a
  finitely generated module over `Z[u^{±1}]`, or over `F_q[u^{±1}]`, and `u` is a unit
  at `v`.
- *The host.* Put `G = B^n ⋊ ⟨Γ, uI⟩`, acting by `x ↦ hx + b` on `O^n`.
  - It is finitely generated: `B^n` is finitely generated over the group ring of `⟨u⟩`.
  - It acts faithfully, since affine maps are determined by their linear and
    translation parts.
  - It is self-similar: the section of `(h, b)` at `v` is `(h, D(h)v + D(b))`, which
    lies in `G` because `D(B) ⊆ B`.

**Word problem.** `Γ` embeds in `GL_{d+1}(E)`, so the word problem is decided by exact
arithmetic in `E`. ∎

## Lesson for general BH

- Self-similar hosts come in three strengths, split by what their sections may do:
  - *Affine* hosts (constant linear part): these give exactly the global-field-linear
    groups, which have transcendence degree at most `1` and easy word problems.
  - *Fibered* hosts (linear part varying polynomially over parameter digits,
    `positive-char-polynomial-affine-groups-are-self-similar`): these reach all
    characteristic-`p` linear groups.
  - *Non-algebraic* hosts: only these can reach non-linear or hard inputs.
- So a self-similar route to the complexity root, or to hard residually finite inputs
  (`kms-arbitrarily-hard-fp-rf-groups`), must use sections that are not algebraic
  functions of finitely many coordinates. The section equations have to fail to be
  étale.
- The KMS tops show where fibering stops. By the unit lemma in
  `two-counter-kms-top-has-no-affine-self-similar-action`, a parameter substitution that
  preserves a torus of independent units `s_i, 1 − s_i` is one-variable. So it cannot
  carry the digit shift `s ↦ α + πs` that fibering needs. Localized multi-counter tops
  are exactly where parameter hosts stop. That is an observation, not proved here in
  general.

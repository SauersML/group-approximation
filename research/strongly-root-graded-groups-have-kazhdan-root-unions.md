---
rg: 2
id: strongly-root-graded-groups-have-kazhdan-root-unions
kind: claim
title: A strong grading by an irreducible classical root system of rank at least two makes the union of the root subgroups a Kazhdan subset
distinct_from:
  elementary-linear-semidir-pair-relative-t: that is relative property (T) of one semidirect pair; this is the global spectral criterion that turns root subgroups into a Kazhdan subset, plus the Kazhdan-ratio bookkeeping that combines the two.
---

**ESTABLISHED.** (Ershov–Jaikin-Zapirain–Kassabov.)

**Definitions.** Let `Φ` be a root system and `G` a group.

- A **`Φ`-grading** of `G` is a family of subgroups `{X_α}_(α ∈ Φ)` such that (i) `G = < ∪ X_α >`, and (ii) for
  `α ∉ R_(<0) β`, `[X_α, X_β] ⊆ < X_γ : γ = aα + bβ ∈ Φ, a, b >= 1 >`.
- For a generic linear functional `f`, the **Borel set** is `Φ_f = {γ : f(γ) > 0}`, and `C_f` is its core. The grading
  is **strong** if `X_γ ⊆ < X_β : β ∈ Φ_f, β ∉ R γ >` for every `f` and every `γ ∈ C_f`.
- For `Φ = A_2` the Borel sets are the positive systems `{α, β, α+β}`, each with core `{α+β}`. So an `A_2`-grading
  is strong exactly when `X_(α+β) ⊆ < X_α, X_β >` for every base `{α, β}`.
- A vector `v` is `(S, ε)`-invariant if `||s v - v|| <= ε ||v||` for all `s ∈ S`. `kappa(G, S)` is the Kazhdan
  constant of `S`, the infimum over unitary representations without nonzero invariant vectors. `S` is a
  **Kazhdan subset** if `kappa(G, S) > 0`.

**Statement.**

- **(a)** If `Φ` is an irreducible classical root system of rank `>= 2` and `{X_α}` is a strong `Φ`-grading of `G`,
  then `∪ X_α` is a Kazhdan subset of `G`.
- **(b) Kazhdan ratios.** Let `B, S ⊆ G`.
  - If some `C > 0` makes every `(S, δ)`-invariant vector `(B, C δ)`-invariant, in every unitary representation and
    for every `δ`, then `kappa(G, S) >= kappa(G, B) / C`.
  - If `H` is a normal subgroup and `S` is finite with relative Kazhdan constant `kappa(G, H; S) = mu > 0`, then every
    `(S, δ)`-invariant vector is `(H, 2 δ / mu)`-invariant.

---
rg: 2
id: decoder-defect-chain-repair-proof
kind: route
title: Read decoders as retractions onto the image, overwrite the finite defect components touching a change, and check every window straddling the overwritten set
target: decoders-lift-changes-away-from-infinite-defect-chains
requires: []
artifacts:
  - research/artifacts/gk3-post-surjective-decoders-2026-09-14.md
---

Notation as in the target. Automata have finite memory, so `x ~ x'` implies `F(x) ~ F(x')` for every
automaton `F`.

**1. Decoders are retractions.**
- **Forward.** Let `σ` be a decoder and `r = τσ`.
  - `r` is an automaton with image contained in `Y`.
  - For `z = τ(w) ∈ Y`, `r(z) = τστ(w) = τ(w) = z`.
- **Backward.** Let `r` be a retraction onto `Y` and `σ₀` a decoder.
  - `σ₀ r τ = σ₀ τ = id`, because `r` fixes `τ(A^G) = Y` pointwise.
- **Mutually inverse.**
  - `τσ₀` is the identity on `Y` by the forward computation, so `τ(σ₀ r) = r`.
  - `σ₀(τσ) = (σ₀τ)σ = σ`.

**2. Post-surjectivity transfers.** Let `E = τσ`.
- **Suppose `σ` is post-surjective.** Let `y ∈ Y` with `y ~ E(x)`, and write `y = τ(w)`.
  - `w = σ(y) ~ σ(E(x)) = στσ(x) = σ(x)`.
  - Choose `x' ~ x` with `σ(x') = w`. Then `E(x') = τ(w) = y`.
- **Suppose `E` lifts changes inside `Y`.** Let `y' ~ σ(x)`.
  - `τ(y') ~ τσ(x) = E(x)`, and `τ(y') ∈ Y`.
  - Choose `x' ~ x` with `E(x') = τ(y')`, i.e. `τ(σ(x')) = τ(y')`. Injectivity of `τ` gives `σ(x') = y'`.

**3. Repair lemma.**
- **Center rule on image windows.** For `p ∈ L`, `ε(p) = p(1)`. Indeed `p = z|_W` for some `z ∈ Y`, and `E(z) = z` gives `z(1) = ε(z|_W)`.
- **Consequence.** If `h ∉ D(x)`, then `E(x)(h) = x(h)`.
- **Setup.** Let `C` be as in the target. It is finite by hypothesis, contains `F`, and set `x' = y` on `C`, `x' = x` off `C`. Then `x' ~ x`.
- **Collar.** Let `K = CU \ C`. If `h ∈ K`, then `h = cu` with `c ∈ C` and `u ∈ U`, so `h` is adjacent to `c`. If `h` were in `D(x)`, it would lie in the component of `c` inside `D(x) ∪ F`, hence in `C`. So `K ∩ D(x) = ∅`.
- **On the collar `x = y`.** For `h ∈ K`, `h ∉ F` (as `F ⊆ C`), so `y(h) = E(x)(h) = x(h)` by the consequence above.
- **Windows away from `C`.** Let `g ∉ CW⁻¹`. Then `gW ∩ C = ∅`, so `(g⁻¹x')|_W = (g⁻¹x)|_W` and `E(x')(g) = E(x)(g)`. Since `1 ∈ W`, `g ∉ C ⊇ F`, so `E(x)(g) = y(g)`.
- **Windows meeting `C`.** Let `g ∈ CW⁻¹` and `w ∈ W`. Then `gw ∈ CW⁻¹W = CU`.
  - If `gw ∈ C`, then `x'(gw) = y(gw)`.
  - If `gw ∈ K`, then `x'(gw) = x(gw) = y(gw)` by the collar.
  - So `(g⁻¹x')|_W = (g⁻¹y)|_W`, which lies in `L` because `y ∈ Y`. Hence `E(x')(g) = ε((g⁻¹y)|_W) = y(g)`.
- **Conclusion.** `E(x') = y`.

**4. Corollary.**
- **Finite components.** Suppose every adjacency component of `D(x)` is finite, and `F` is finite.
  - Each site of `F` is adjacent to at most `|U|` sites, so only finitely many components of `D(x)` are adjacent to `F`.
  - A path inside `D(x) ∪ F` from a site of `F` leaves `F` only into a component of `D(x)` adjacent to `F`. So every component of `D(x) ∪ F` meeting `F` lies inside `F` together with those finitely many finite components, and is finite.
  - Parts 2 and 3 then give post-surjectivity of `σ` at `x`.
- **Case `x ~ Y`.** If `x` differs from some `z ∈ Y` on a finite `P`, then every site outside `PW⁻¹` sees a window of `z`. So `D(x) ⊆ PW⁻¹` is finite.
- **Sparse Garden-of-Eden occurrences.** Suppose `x` agrees with some `z ∈ Y` off `⋃_i g_i P`, for finite `P` and translates `g_i`, and the sets `g_i P W⁻¹` are pairwise non-adjacent. Then `D(x) ⊆ ⋃_i g_i P W⁻¹`, and its components are finite.
- **Failure.** If a lift fails at `(x, F)`, then some component of `D(x) ∪ F` meeting `F` is infinite. It contains a site of `F`, so it contains an infinite component of `D(x)` adjacent to `F`.

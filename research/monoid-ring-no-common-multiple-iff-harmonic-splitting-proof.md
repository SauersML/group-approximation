---
rg: 2
id: monoid-ring-no-common-multiple-iff-harmonic-splitting-proof
kind: route
title: Identify the right ideals with annihilators of harmonic configurations, and extend a functional from the direct sum of the two ideals
target: monoid-ring-no-common-multiple-iff-harmonic-splitting
requires: []
artifacts:
  - research/artifacts/hl-f-p22-invariant-2026-09-13.md
---

Notation as in the claim. `E = K[M]` has basis `M`. So linear functionals on `E` are exactly the
configurations `f : M -> K`, through the pairing `⟨u, f⟩ = Σ_m u(m) f(m)`.

**Step 1 (transposes).** For `u ∈ E` and a configuration `f`,
`⟨a u, f⟩ = Σ_{s, m} α_s u(m) f(s m) = ⟨u, a* f⟩`. Hence the annihilator of the right ideal
`U = a E` is `U^⊥ = {f : ⟨a u, f⟩ = 0 for all u} = ker a*`. Likewise, with `V = b E`, `V^⊥ = ker b*`.

**Step 2 (⇐ in item 1).** Suppose every `f` splits as `g + h` with `g ∈ U^⊥` and `h ∈ V^⊥`, and let
`0 ≠ e ∈ U ∩ V`. Choose `f` with `⟨e, f⟩ ≠ 0`: take `f` to be the indicator of one point of `supp e`.
Then `⟨e, f⟩ = ⟨e, g⟩ + ⟨e, h⟩ = 0 + 0`, a contradiction. So `U ∩ V = 0`.

**Step 3 (⇒ in item 1).** Suppose `U ∩ V = 0`, so the sum `U + V` is direct. Given a configuration `f`,
define `λ` on `U ⊕ V` by `λ(u + v) = ⟨v, f⟩`. It is well defined and linear because the sum is direct.
Extend `λ` to a linear functional `Λ` on `E`: choose a complement of `U ⊕ V` in `E` and set `Λ = 0`
there. (If `M` is countable, as for Thompson's `F`, no choice principle is needed.) Let `g` be the
configuration `g(m) = Λ(m)`, so `⟨w, g⟩ = Λ(w)` for all `w ∈ E`. Then:
- `⟨u, g⟩ = λ(u) = 0` for `u ∈ U`, so `g ∈ U^⊥ = ker a*`;
- `⟨v, f − g⟩ = ⟨v, f⟩ − λ(v) = 0` for `v ∈ V`, so `h := f − g ∈ V^⊥ = ker b*`.
Thus `f = g + h` is the required splitting.

**Step 4 (item 2).** If `f = g + h` with `a* g = 0` and `b* h = 0`, then `a* f = a* h` with `h ∈ ker b*`.
Conversely, if `a* f = a* h` for some `h ∈ ker b*`, then `g = f − h` is a-harmonic. So item 1 for all `f`
is equivalent to `a*(K^M) ⊆ a*(ker b*)`, and the reverse inclusion is trivial.

**Step 5 (item 3).** Over `F_2`, `(a* f)(m) = Σ_{s ∈ A} f(s m) mod 2`, which vanishes exactly when an
even number of the values `f(s m)`, `s ∈ A`, equal `1`. The points `s m`, `s ∈ A`, are distinct
whenever `M` is left-cancellative; that isn't needed for the parity reading of `a*`.

**Scope.** No property of `F` is used beyond `M` being a monoid. The claim adds no information about
which pairs of `P_(2,2)` split.

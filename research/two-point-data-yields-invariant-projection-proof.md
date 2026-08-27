---
rg: 2
id: two-point-data-yields-invariant-projection-proof
kind: route
title: Read the invariance off the definition, cut a random level set, tensor with a free quotient action
target: two-point-data-yields-invariant-projection
requires: []
---

# Read the invariance off the definition, cut a random level set, tensor with a free quotient action

**Step 1: what the clauses say.**  Fix a model `(A, φ, S, B, j)` for the
window `F` at precision `ε` and put `f_p(s) := j_s(p)`, `f_q(s) := j_s(q)`
on `S`.  For `γ ∈ Γ ∩ F`: `γ^{-1}·p = p`, so the equivariance clause at
`(γ, x = p)` reads `f_p(φ(γ)s) = f_p(s)` for `s, φ(γ)s ∈ S`.  For `h`:
`h^{-1}·q = h^{-1}hΓ = Γ = p`, so the clause at `(h, x = q)` reads
`f_q(φ(h)s) = f_p(s)` for `s, φ(h)s ∈ S`; combined with distinctness
`f_p(φ(h)s) ≠ f_q(φ(h)s)` this gives

```text
f_p(φ(h)s) ≠ f_p(s)      for every s with s, φ(h)s ∈ S.
```

The `Γ`-invariance is handed over by the definition exactly; nothing
reconstructs it.

**Step 2: the random level set.**  Choose `B₀ ⊆ B` uniformly at random and
set `E := {s ∈ S : f_p(s) ∈ B₀}`.  For each `s` in the density-`(1−2ε)`
set `S ∩ φ(h)^{-1}S` (a bijection image, so that size bound is exact), the
two distinct values `f_p(s) ≠ f_p(φ(h)s)` are separated by `B₀` with
probability exactly `1/2`, so by linearity of expectation some `B₀`
achieves

```text
|{s : 1_E(s) ≠ 1_E(φ(h)s)}| ≥ (1/2)(1 − 2ε)|A|,
```

while for each fixed `γ ∈ Γ ∩ F`,
`|{s : 1_E(φ(γ)s) ≠ 1_E(s)}| ≤ 2ε|A|` by Step 1 (only points with `s` or
`φ(γ)s` outside `S` can differ).

**Step 3: tensor with a free quotient action.**  The assembled ultraproduct
of the `φ_n` alone need not be a sofic representation (it can even be
non-injective — the parity flip models of
`parity-flip-models-satisfy-two-point` have `|A| = 2`).  Repair by
tensoring, not by disjoint union: `G` is residually finite (Theorem E,
`kun-thom-nonsofic-wreath`), so for each `n` there is a finite quotient
`G/N_n` with `N_n ∩ B_n(G) = {1}`; let `ψ_n` be its left-translation
action — exact and free — and set

```text
C_n := A_n × Z_n,   Z_n := G/N_n,   Φ_n(g) := φ_n(g) × ψ_n(g)   (diagonal).
```

Then: (i) multiplicativity defects are unchanged — `ψ_n` is exact, and a
product pair moves iff the first coordinate pair does, so
`d(Φ_n(g)Φ_n(g'), Φ_n(gg')) ≤ ε_n`; (ii) for `g ≠ 1`, eventually
`g ∉ N_n`, the `Z`-factor is fixed-point free, hence `Φ_n(g)` has **no**
fixed points and `d(Φ_n(g), 1) = 1` exactly — no amplification, no case
split on `|A_n|`; (iii) the set `Ẽ_n := E_n × Z_n` has

```text
|Ẽ_n △ Φ_n(γ)^{-1}Ẽ_n|/|C_n| = |E_n △ φ_n(γ)^{-1}E_n|/|A_n| ≤ 2ε_n,
|Ẽ_n △ Φ_n(h)^{-1}Ẽ_n|/|C_n| ≥ (1/2)(1 − 2ε_n),
```

the symmetric differences being computed coordinate-one-wise.

**Step 4: the ultraproduct.**  Run Steps 1–3 along models at `(F_n, ε_n)`
with `F_n ↗ G` and `ε_n ↓ 0`, and set `σ(g) := [Φ_n(g)]_𝒰`,
`a := [1_{Ẽ_n}]_𝒰 ∈ D_𝒰`.  Then `σ` is a homomorphism (defects vanish per
fixed pair) with `d(σ(g), 1) = 1` for every `g ≠ 1` — a sofic
representation in the strongest standard sense, injective with
`tr∘σ = δ_e`, hence admissible under every reading of Kun--Thom's
definition (which the in-repo artifact does not transcribe; flagged for
the next source pass); `σ(γ)a = a` exactly, for every fixed `γ ∈ Γ`
(defect `≤ 2ε_n → 0`); and `τ(a △ σ(h)a) = lim_𝒰 ≥ 1/2`.  ∎

**Remark on where the exact-model difficulty went.**  The fixed-window
theorem `exact-models-cannot-separate-marked-pair` must beat an ε-deleted
set with expansion because its window and precision are fixed.  Here the
`∀F ∀ε` quantifier of the two-point claim is spent on a sequence
`(F_n, ε_n) → (G, 0)`, the deleted sets have vanishing density and vanish
in the ultraproduct, and nothing needs to expand.  The price is
non-constructiveness: no explicit failing `(F, ε)` is produced, so this
lemma complements and does not subsume the exact-model theorem.

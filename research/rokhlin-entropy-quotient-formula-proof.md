---
rg: 2
id: rokhlin-entropy-quotient-formula-proof
kind: route
title: Markers kill the torsor's relative entropy, and an alignment cocycle transports generators down to the quotient
target: rokhlin-entropy-quotient-formula-for-finite-normal-subgroups
requires:
  - alpeev-seward-stabilizer-growth-kills-outer-entropy
  - seward-rokhlin-entropy-subadditivity
artifacts:
  - research/artifacts/rokhlin-finite-kernel-quotient-formula-2026-09-13.md
---

Sections 1 and 2 of the artifact.

1. **Freeness of the quotient (Lemma 1.1).** If `π(w)` fixes `Nx`, then `m^-1 w` fixes `x` for some `m ∈ N`. So
   `Stab_W(Nx) = N` a.e.
2. **Transversal and alignment (Lemma 1.2).** Let `M` be the least points of the `N`-orbits and write
   `x = τ(x) p(x)` with `p(x) ∈ M`. Put `a(x, w) = τ(w p(x))`. Then `w p(x) = a(x, w) p(wx)`, `a(x, m) = m`, and
   `a(x, w_1 w_2) = (w_1 a(x, w_2) w_1^-1) a(w_2 x, w_1)`.
3. **Zero relative entropy (Lemma 1.3).** Let `D` be an `N`-invariant set of measure below `δ`. The partition
   `{X \ D} ∪ {D ∩ mM}` costs `μ(D) log n` relative to `Σ_N`. Read at the first `w_i` with `w_i x ∈ D`, it recovers
   `x = w_i^-1 τ(w_i x) p(w_i x)`.
4. **(2.1).** By Alpeev–Seward (i) with index `n`, `h^Rok_(W,μ)(Σ_N) <= (1/n) h^Rok_Q(X/N)`. Sub-additivity with
   step 3 gives `h^Rok_W(X) <= (1/n) h^Rok_Q(X/N)`.
5. **(2.2).** For a generator `α` of `X`, let `β(x) = (α(m p(x)))_m` and `ã_j(x) = a(x, ŝ_j)`, where the `ŝ_j`
   lift generators of `Q`.
   - **Cost.** `H(β) = H_(μ_M)(α_N) <= H_μ(α_N) <= n H(α)`, where `μ` averages the relabelled measures `μ_(mM)`.
     Each `ã_j` costs at most `log n`.
   - **Generation.** The cocycle identity expresses every `a(·, w)` through translates of the `ã_j`. Then
     `α(w p(x))` is the `a(x, w)`-coordinate of `β(wx)`, so the `α`-name of `p(x)` is measurable for
     `σ-alg_Q(β ∨ ã_1 ∨ ... ∨ ã_r)`, and this partition generates `X/N`.

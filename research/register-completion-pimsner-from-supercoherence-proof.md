---
rg: 2
id: register-completion-pimsner-from-supercoherence-proof
kind: route
title: Take t_+ as the sum of the spine letters, run ABC 3.6 on the corner skew Laurent structure, kill NK by supercoherence and flatness, and telescope the core
target: register-completion-pimsner-from-supercoherence
requires:
  - abc-twisted-laurent-k-theory-fibration
  - eventually-rational-register-ring-is-regular-supercoherent
---

Lane proof, repaired after the referee reports. Notation as in the claim.

## 1. Corner skew Laurent structure (repair of G3, referee a's construction)
`R` is `ℤ`-graded by letter length, and all defining relations are homogeneous. Put
`t_+ = Σ_ρ s_(x_ρ)` and `t_- = Σ_ρ t_(x_ρ)`. The spine letters have distinct ranges, so
`t_- t_+ = Σ_ρ t_(x_ρ) s_(x_ρ) = Σ_ρ p_ρ = 1`. AGGP Lemma 2.4 gives
`R = R_0[t_+, t_-; φ]` with `φ(d) = t_+ d t_-`, and no Morita step is needed. `R_0` is a
unital `Q`-algebra, hence `ℤ`-flat and H'-unital (ABC Remark 2.2).

## 2. The core and its K-theory (repair of G2)
- **Stages.** `R_0 = colim_n R_(0,n)`, where `R_(0,n)` is spanned by `s_μ b t_ν`, with
  `|μ| = |ν| = n` and `b ∈ B⁺`. The transition pads by `b ↦ Σ_x s_x σ_x(b) t_x`.
- **Each stage.** `R_(0,n)` is the corner `q M_(P_n)(B⁺) q`, where `q = diag(α_μ)`
  records path availability. For every type `τ`, the spine path
  `x_(s^(n−1)τ) … x_(sτ) x_τ` ends at `τ` with full availability. So `q` is full, and
  Morita invariance gives `K(R_(0,n)) ≅ G = ⊕_ρ K(B⁺_ρ)`.
- **The colimit.** The transitions induce `[X]`, so `K(R_0) = colim(G →[X] G →[X] …)`,
  because `K` commutes with filtered colimits (ABC, proof of Lemma 3.5).
- **The telescope.** `φ` prepends spine letters, so `φ_*` is the index shift `s` on the
  colimit, with `s ι_n = ι_(n+1)` for the canonical maps `ι_n : G -> K(R_0)`. From
  `ι_n = ι_(n+1)[X]` we get `s^(-1) ι_n = ι_n [X]`. The exact sequence
  `0 -> ⊕_n G -> ⊕_n G -> colim -> 0` of the telescope then gives
  `coker(1 − φ_*) ≅ coker(1 − [X] on G)` and `ker(1 − φ_*) ≅ ker(1 − [X] on G)`.

## 3. The NK terms vanish (repair of G1)
Let `S = φ^(-1)R_0 = colim(R_0 →φ R_0 →φ …)`, with automorphism `φ̂`, and let
`D = S ⊕ Q` be its `Q`-unitization. By the ABC step quoted in the claim,
`NK(R_0, φ)_± = NK(D, φ̂)_±`, so by Lemma 7.2 it suffices that `D` is regular
supercoherent.
- **D is a filtered colimit.** `D = colim_n D_n`, where `D_n = R_(0,n) ⊕ Q ≅ R_(0,n) × Q`,
  since each `R_(0,n)` is unital. The transitions `D_n -> D_(n+1)` are unital.
- **Each `D_n` is regular supercoherent.** `R_(0,n)` is Morita equivalent to a finite
  product of factors of `B⁺`. Those are regular supercoherent by
  `eventually-rational-register-ring-is-regular-supercoherent`, parts 1–3. Coherence and
  finite projective dimension of finitely presented modules are Morita invariant, and so
  are they over polynomial rings, because `M_m(A)[t] = M_m(A[t])`.
- **The transitions are flat, on both sides.**
  - The padding maps are block maps whose blocks are `B⁺` viewed through the substitutions
    `σ_x`, cut down by availability idempotents. These are flat by part 4 of that node.
  - The spine maps `φ` are untwisted corner embeddings. Over the image corner, the
    remaining blocks are standard column modules, which are finitely generated projective.
  - The `Q` factor is a field.
- **Filtered colimits.** A filtered colimit of regular supercoherent rings along flat maps
  is regular supercoherent, by an elementary argument.
  - Coherence: a finitely generated left ideal of `D[t_1..t_p]` comes from some
    `D_n[t…]`. Its syzygies there are finitely generated, and flat base change carries them
    to `D[t…]`.
  - Regularity: a finitely presented module comes from a finite stage. A finite resolution
    by finitely generated projectives there stays exact after the flat base change.
- **Conclusion.** Hence `NK(D, φ̂)_± = 0` by Lemma 7.2.

## 4. The sequence
ABC Theorem 3.6, with `A = ℤ` and §3, gives
`K(R) = hocofiber(K(R_0) →(1−φ_*) K(R_0))`, and §2 identifies its cokernel and kernel.
That is the statement. ∎

## 5. Remark (heuristic)
Without resolvents, and with registers bounded, the same computation is ABC Theorem 7.6
for a row-finite quiver over `k = Q`. Unbounded registers are not literally a quiver
algebra, so this comparison is only heuristic (referee b). The resolvents that make `1/m`
exist are what replace `Q` by `B⁺` as the coefficient ring.

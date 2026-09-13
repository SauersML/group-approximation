---
rg: 2
id: once-punctured-birman-sequence-does-not-virtually-split
kind: claim
title: For genus at least two the Birman sequence that adds a marked point to a once-punctured surface admits no section over a finite-index subgroup
distinct_from:
  birman-exact-sequence-does-not-virtually-split: that is Chen--Salter's theorem for closed surfaces of genus at least four; this is the sequence over a once-punctured base surface, which their theorem does not cover and which feeds the free-group analogue through Dehn--Nielsen--Baer.
  birman-sequence-genus-three-does-not-virtually-split: that adapts Chen--Salter to the closed genus-three sequence; this is the once-punctured base in every genus at least two.
artifacts:
  - research/artifacts/solve-bh-mcg-outfn-2026-09-13.md
---

**OPEN.** Let `g ≥ 2`, and let `x` be a puncture of `Σ_{g,1} = Σ_g ∖ {x}`. There is no
finite-index `Γ ≤ PMod(Σ_{g,1})` with a homomorphism `σ: Γ → PMod(Σ_{g,2})` whose
composite with forgetting the second puncture `∗` is the inclusion of `Γ`.

By `free-group-virtual-sections-give-punctured-birman-sections` (with `k = 1`),
this implies `aut-free-to-out-free-does-not-virtually-split-in-even-rank` in rank
`2g`.

## Attempts

1. **Chen--Salter's Section 3 with the puncture as the handle.** Proposed; not
   carried out as a complete proof. In arXiv:1804.11235v1, TeX l.448--704, the
   contradiction runs on a *handle-pushing* subgroup `π1(UTΣ_p)` and a homomorphism
   `s` into `π1(Σ_p)`. Over a once-punctured base the analogue is the x-pushing
   subgroup `Λ = Γ ∩ π1(Σ_g, x)`, the kernel of forgetting `x`, and there is no
   framing to factor out. So their Lemma `sbar` becomes unnecessary.
   - **What transfers.** For `λ ∈ Λ`, `σ(λ)` lies in `PB_2(Σ_g) = π1 PConf_2(Σ_g)`
     with coordinates `(λ, s(λ))`, where `s := (forget x)∘σ|_Λ`. Their l.669--704
     computation then gives `(i × s)^*[Δ] = 0` in `H^2(Λ; Q)`.
   - **What it needs.** Either `s^* = i^*` or `s^* = 0` on `H^1`. Then the value is
     `χ(Σ_g)·[Σ_g:Λ]` or `[Σ_g:Λ]`, and neither is 0.
   - **The dichotomy.** Their Case A/B dichotomy (Lemmas `BPlifts`, `Ghom`,
     `caseA`, `caseB`) should come from lifts of point-push bounding pairs.
   - **Status of the pieces.**
     - A twist-lift lemma for curves essential in `Σ_g` is written out in the
       artifact for `g ≥ 2`.
     - The based comparison `s(α^k) = α^m` for simple `α`, with a fixed path from
       `x` to `∗`, is the unverified step.
2. **Cohomology alone.** Suppose one only knows `s` is equivariant up to
   conjugacy under the image of `Γ` in `Mod(Σ_g)`.
   - **Decomposition.** Transfer gives `s^* = t·i^* + r` with `t ∈ Q` and `r`
     valued in the kernel of corestriction. Then
     `(i × s)^*[Δ] = [Σ_g:Λ](1 + t² − 2gt) + u`, where `u` is the invariant
     alternating form `⟨r(·) ∪ r(·)⟩` evaluated on a symplectic pair.
   - **When it works.** If `r = 0`, the root `t = g ± √(g²−1)` is irrational, so
     there is a contradiction. That holds when the deck group `π1(Σ_g)/Λ` is
     abelian, because each nontrivial isotypic Prym summand then has dimension
     `2g − 2 < 2g` (Chevalley--Weil).
   - **Where it stops.** For a nonabelian deck group, `r ≠ 0` is not excluded, so
     this needs topological input.

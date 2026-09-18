---
rg: 2
id: v-times-inflation-host-full-groups-are-finitely-presented
kind: claim
title: (OPEN) V times the translation-plus-inflation groupoid of a recognizable primitive aperiodic box substitution has a finitely presented full group; proved (type F_∞) in the fault-free odometer case, and the only missing ingredient is a product engine for rational transformations with lag at fault lines
requires:
  - substitution-inflation-hosts-are-full-contracting-rsgs
  - thumann-operad-groups-need-only-f-infinity-transformations
distinct_from:
  substitution-inflation-hosts-are-full-contracting-rsgs: that proves the inflation host F(𝒢⁺) itself finitely presented, as a full contracting RSG; this asks for the V-stabilized product G_V × 𝒢⁺, which contains the labelled master-route host F(G_V × (Z^d ⋉ X_ω)) as a subgroup.
  v-times-quantum-rigid-sft-full-groups-are-fp: that is P2′ for the labelled host, which needs quantum rigidity; this larger host contains the inflation germs, so the necessity theorem does not apply to it.
---

**OPEN** (lane bh-invent-06b, 2026-09-18). Parts A and B below are lane proofs, not reviewed.

## Statement

Let `ω` satisfy (H1)–(H4) of `substitution-inflation-hosts-are-full-contracting-rsgs`, and let `𝒢⁺` be its
translation-plus-inflation groupoid on `X_ω`. Then `F(G_V × 𝒢⁺)` is finitely presented.

**Why it matters.** `G_V × (Z^d ⋉ X_ω) ⊆ G_V × 𝒢⁺`, so `F(G_V × 𝒢⁺)` contains the labelled master-route host.
- A proof would show that the V factor is compatible with inflation.
- For non-SFT `X_ω`, and for Labbé if E2 fails, the labelled host is not finitely presented. So a proof would
  realize it as a subgroup of a finitely presented V-stabilized group, rather than as one itself.

## A. The fault-free case is F_∞ (proved)

**Setting.** Let `X = Z_k^d` be the `k`-adic odometer. `Z^d` acts freely and minimally by translation, and
inflation is `ι_p(y) = p + k y` for `p ∈ Q = [0,k)^d`. In base-`k` digits, `X = Q^N`, `t_(e_i)` is the adding
machine in coordinate `i` (a tree automorphism), and `𝒢⁺` is the Nekrashevych groupoid of the `d`-dimensional
adding machine.

**Claim.** `F(G_V × 𝒢⁺)` is of type `F_∞`.

**Proof.** Let `𝒪` be the one-colour suboperad of `End(TOP, ⊔)` on `Ω = C × Q^N` defined as follows.
- A degree-`n` operation is a tuple of maps `(x, z) ↦ (u_i x, w_i · a^(v_i)(z))`, where `u_i ∈ {0,1}^*`,
  `w_i ∈ Q^*`, `v_i ∈ Z^d` and `a^v` is the adding machine. The images `[u_i] × [w_i]` must partition `Ω`.
- **Closed under composition.** The adding machine is self-similar: `a^v(w′z) = a^v(w′) a^(v|_(w′))(z)`.
- **Transformations.** The degree-1 operations are the maps `id × a^v`, so `ℐ = Z^d`, which is `F_∞`.
- **Calculus of fractions.**
  - Operations are mono and epi, which gives cancellation and equalization, as in the source's remark.
  - Square filling: two brick partitions have a common brick refinement, and the pull-back of a brick partition
    under `(x, z) ↦ (ux, w a^v z)` is again a brick partition, because `a^v` is a tree automorphism.
- **Classes.** A transformation class is its image brick partition: embeddings onto a fixed brick differ by an
  input transformation.
- **The very elementary classes** are the `C`-halving and the `Q`-split.
  - If some brick of a partition has `u = ∅`, then every brick has `w ≠ ∅`, since two bricks with `u = ∅` and
    `w = ∅` would intersect. So the partition refines the `Q`-split.
  - Otherwise every brick has `u ≠ ∅`, and the partition refines the `C`-halving.
- **The spine** is {halving, `Q`-split, grid}: `M_1` consists of the grid alone, and `S_2 = ∅`. So `𝒪` has finite
  type. It is color-tame, since it has one colour and higher operations.
- **Conclusion.**
  - The relaxed Thumann theorem (`thumann-operad-groups-need-only-f-infinity-transformations`) gives
    `π_1(𝒪)` of type `F_∞`.
  - `π_1(𝒪)` is the group of homeomorphisms that act piecewise on a brick partition by
    (prefix replacement) × (prefix replacement ∘ `a^v`). That is `F(G_V × 𝒢⁺)`, because the germs of `𝒢⁺` are
    exactly (prefix replacement) ∘ `a^v`. ∎

## B. Where faults obstruct the known engines (proved)

- **BBMZ fails in the product coding.** In the synchronous product coding `C × Σ_Γ = Σ_(Γ_2 × Γ)`, the elements of
  `V × 1` that change prefix lengths by `m` have, as local actions at every deep cone of a piece, the delay maps
  `(a_0 a_1 …, e_0 e_1 …) ↦ (s a_0 a_1 …, e_0 e_1 …)` with pending bits `s ∈ {0,1}^m`.
  - These are distinct for distinct `m`, and they recur.
  - So the nucleus of `F(G_V × 𝒢⁺)` in that coding is infinite: it is not a contracting RSG there. This already
    happens for `2V ≤ F(G_V × G_Γ)`.
- **Thumann/Li fail because of faults.** In the collared coding, the deep local actions of translations are
  `strip(y ↦ ι_q t_c y)` with `c ≠ 0` (proof of `substitution-inflation-hosts-are-full-contracting-rsgs`,
  Step 3).
  - They are rational with one level of lookahead. They map a cone onto a union of cones, not onto a cone.
  - So they are neither transformations nor operations of a dissection operad.
  - In the odometer there are no letters, `c` never needs lookahead, and translations are tree automorphisms,
    which is why part A works.

**The missing ingredient** is a product theorem: *if `𝒢_1` has a full contracting RSG full group and `𝒢_2` is an
irreducible SFT groupoid, then `F(𝒢_1 × 𝒢_2)` is finitely presented.* This would be a 2V-type (Brin) extension
of BBMZ's `thrm:fin_pres`, and it would settle the node.

## Lesson for general BH

Inflation hosts are one-dimensional contracting RSGs, and multiplying by V makes them two-dimensional. Every known
two-dimensional engine (Brin, Li, relaxed Thumann) needs the transformations to be tree automorphisms. The fault
lines of a hierarchical SFT, where rigidity lives, are exactly the points where translations become rational maps
with lag instead. So faults are the entire content of V-stabilizing an inflation host. The fault-free (odometer)
case is `F_∞`, and the general case waits on a product theorem for contracting RSGs. That theorem is also the
engine that products of boundary codings with inflation codings would need.

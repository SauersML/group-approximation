---
rg: 2
id: commensurated-witnesses-survive-browder-but-die-when-linear
kind: claim
title: "Every finite subgroup Q of F/N is E_Q/Sigma_Q for the Q-core Sigma_Q of any benign witness, so Browder bounds the part of Q acting trivially on H_*(Sigma_Q) by 2 cd Sigma; the full exponent kill does not extend to commensurated witnesses (fixed Sigma = F_2 carries every (Z/p)^r), but commensurated witnesses cut out by a p-adic representation or by a locally finite tree force bounded ranks, so U, V and Z/2 wr Z have none"
distinct_from:
  type-f-weyl-groups-have-bounded-elementary-abelian-ranks: That bounds ranks when F normalizes Sigma, with a constant depending only on Sigma; this shows that constant cannot survive commensuration (a fixed Sigma = F_2 realizes every (Z/p)^r), keeps the Sigma-independent part of the bound for every witness via the Q-core, and replaces the lost constant by p-adic analytic or tree geometry.
  separable-benign-witness-forces-rf-quotient: That kills witnesses with profinitely closed Sigma and forces F/N residually finite; this kills a different class (Sigma cut out by a p-adic compact open subgroup, as SL_2(Z) in SL_2(Z[1/p]), which is not profinitely closed) and forces bounded finite-subgroup ranks, which also excludes the residually finite Z/2 wr Z.
  thompson-f-commensurated-subgroups-are-trivial-or-normal: That classifies commensurated subgroups of Thompson's F; this is about witnesses Sigma commensurated by a free subgroup of a type F host, for the benign root.
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome).** Setting as in
`two-occurrence-realizability-is-type-f-benignness`: `F = F(A)` free,
`N ⊴ F`, `P = F/N`, and a witness `Σ ≤ Λ ⊇ F` with `Σ ∩ F = N`. Say the
witness is **commensurated** if every `f ∈ F` has `[Σ : Σ ∩ fΣf^{-1}] < ∞`.

1. **Q-cores (every witness, no hypothesis on `Σ`).** Let `Q ≤ P` be finite,
   `H ≤ F` its preimage, and `h_q` coset representatives. Put
   `Σ_Q = ∩_{q ∈ Q} h_q Σ h_q^{-1}` and `E_Q = Σ_Q H`. Then `Σ_Q ⊴ E_Q`,
   `E_Q ∩ Σ = Σ_Q ⊇ N`, and `E_Q/Σ_Q ≅ Q`. If the witness is commensurated,
   `[Σ : Σ_Q] < ∞`, so `Σ_Q` is of type `F_m` when `Σ` is.
2. **What survives of Browder (every witness).** If `Λ` is torsion-free and
   `n = cd Σ < ∞`, then for every finite `Q ≤ P` and prime `p`, the subgroup
   of `Q` acting trivially on `H_{≥1}(Σ_Q; Z)` has `p`-rank at most `2n`.
   No finiteness of `H_*(Σ_Q)` is needed. So in any torsion-free finite-`cd`
   witness for `N_U`, every elementary abelian `(Z/2)^r ≤ U` acts on
   `H_*(Σ_Q; Z)` with kernel of rank `≤ 2n`.
3. **The Σ-only constant dies (obstruction).** The rank bound of
   `type-f-weyl-groups-have-bounded-elementary-abelian-ranks` has the form
   `2n + c_p(Σ)`. No bound depending only on `Σ` holds for commensurated
   witnesses. For every prime `p` and `r ≥ 2`, the amalgam
   `Λ_r = F_r *_{M_r} F_2`, with `M_r = ker(F_r -> (Z/p)^r)` identified with
   a subgroup of index `p^r(r-1)` in `F_2`, is a torsion-free type `F`
   commensurated witness with `Σ = F_2` for `N = M_r ⊴ F = F_r`, and
   `P = (Z/p)^r`. So applying Browder to `Σ_Q` gives `r ≤ 2 + c_p(Σ_Q)`,
   where `c_p(Σ_Q) ≥ ⌊p^r(r-1)/(p-1)⌋` is available. **The normalized kill
   does not extend to commensurated witnesses by passage to finite index.**
   Any bound for a single witness must use the host `Λ`, not `Σ` alone.
4. **Linear kill.** Suppose `N = F ∩ ρ^{-1}(K)` for a homomorphism
   `ρ : F -> G = ∏_{j=1}^{s} GL_{d}(Q_{p_j})` and a compact subgroup `K`
   that is open in some closed subgroup `G_0 ⊇ ρ(F)` of `G`.
   (For example, `Σ = Λ ∩ ρ^{-1}(K)` for a representation `ρ` of `Λ`; this
   covers S-arithmetic congruence witnesses and vertex stabilizers in
   Bruhat–Tits buildings over characteristic-0 local fields, via restriction
   of scalars.) Then every finite `Q ≤ P` is a quotient `L/L_0` of a compact
   subgroup `L ≤ G` by an open normal subgroup, and for each prime `ℓ`
   `rk_ℓ Q ≤ c(d, p_1, ..., p_s, ℓ) < ∞`, with `c = 0` for `ℓ` large.
   No torsion-freeness or finiteness type is assumed.
5. **Tree kill.** If `F` acts on a locally finite tree with a vertex `v`
   such that `Stab_F(v) = N` (for example, `Σ = Stab_Λ(v)` for an action of
   `Λ`; every witness in which `Σ` is a vertex group of a graph of groups
   with finite-index edge inclusions), then `P` is finite or virtually free.
6. **Consequences.** Groups whose finite subgroups have unbounded
   `ℓ`-rank for some `ℓ` (`U`, `V`, `Z/2 ≀ Z`, Grigorchuk's group) admit no
   witness of the kinds in items 4 and 5, of any finiteness type and with or
   without torsion in `Λ`. Since `Z/2 ≀ Z` is residually finite, this is not
   covered by `separable-benign-witness-forces-rf-quotient`.

**Surviving shape.** A type `F` commensurated witness for `N_U` must have
`Σ ∩ F` cut out by neither a characteristic-0 `p`-adic representation nor a
locally finite tree, and every finite `Q ≤ U` must act on `H_*(Σ_Q; Z)` with
kernel of `p`-rank at most `2 cd Σ`. In completion terms (proof, Step 6), the
relative Schlichting completion `F̂` of `F` in `Sym(⟨F, Σ⟩/Σ)` has a compact
open normal subgroup `M` with `F̂/M ≅ U`, and its compact subgroups must have
finite quotients of unbounded rank: `F̂` is not isomorphic, as a topological
group, to a closed subgroup of a finite product of groups `GL_d(Q_p)` (item 4
applies to such a completion).
Candidates left: non-linear totally disconnected completions such as
characteristic-`p` groups or Neretin-type groups, with a geometry that is not
a tree.

Proof: route `commensurated-witnesses-browder-survives-linear-kill-proof`.

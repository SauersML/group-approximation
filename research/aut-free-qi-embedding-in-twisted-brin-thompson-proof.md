---
rg: 2
id: aut-free-qi-embedding-in-twisted-brin-thompson-proof
kind: route
title: Kill the normal closure of V to retract Aut_V(V*F_n) onto Aut(F_n), then quasi-retract SV_Γ onto Aut_V(V*F_n)
target: aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups
requires:
  - aut-free-groups-satisfy-permutational-boone-higman
  - twisted-brin-thompson-groups-quasi-retract-onto-acting-group
---

Notation as in the target. Word lengths use fixed finite generating sets.

1. **The BFFHZ inputs** (arXiv:2503.21882v2, read from the arXiv HTML on 2026-09-18).
   - Proposition 1.1: "If G is finitely presented and has trivial center, then Aut_G(G∗F_n) is finitely
     presented." `V` is finitely presented with trivial center, so `Γ` is finitely presented.
   - Lemma 2.2: "Suppose that G is MIF. Then the action of Aut_G(G∗F_n) on Hom_G(G∗F_n,G) is faithful."
     The action is by precomposition, and `V` is MIF, so `Γ` acts faithfully on `S`.
   - Theorem A is proved with the twisted Brin--Thompson group `SV_Γ` of this action, which is finitely
     presented and simple. `Aut(F_n)` sits in `Γ` as the automorphisms `α̂ = id_V * α`.

2. **Aut(F_n) is a retract of Γ.** Let `N` be the normal closure of `V` in `V * F_n`, so that
   `(V * F_n)/N = F_n` canonically. Each `γ ∈ Γ` fixes `V` pointwise, so `γ(N) = N`, and `γ` induces an
   endomorphism `ρ(γ)` of `F_n`. Then `ρ(γγ') = ρ(γ)ρ(γ')` and `ρ(1) = 1`, so each `ρ(γ)` is an
   automorphism, and `ρ: Γ → Aut(F_n)` is a homomorphism. Also `ρ(α̂) = α`, because `α̂` acts as `α` on
   the free factor `F_n`, which maps isomorphically onto `(V * F_n)/N`.

   Put `L = max |ρ(s)|_{Aut(F_n)}` over the generators `s` of `Γ`. Then `|ρ(γ)| <= L |γ|_Γ`, so
   `|α|_{Aut(F_n)} = |ρ(α̂)| <= L |α̂|_Γ`. The inclusion `α ↦ α̂` is a homomorphism of finitely generated
   groups, so it is Lipschitz. So `Aut(F_n)` is undistorted in `Γ`. More generally, for `h` in a finitely
   generated `H <= Aut(F_n)`, `|h|_{Aut(F_n)} <= L |ĥ|_Γ <= L M |h|_{Aut(F_n)}`, where `M` bounds the
   `Γ`-lengths of the images of the generators of `Aut(F_n)`.

3. **Γ is undistorted in SV_Γ.** `Γ` and `SV_Γ` are finitely generated (step 1). So by
   `twisted-brin-thompson-groups-quasi-retract-onto-acting-group` (Belk--Zaremsky, `thm:quasi-retracts`), there are
   `A, B` with `|γ|_Γ <= A |γ|_{SV_Γ} + B` for all `γ ∈ Γ`. The inclusion is Lipschitz, so `Γ` is
   undistorted. The label-length lemma `full-group-label-length-bounds-distortion` (form 2) gives the same
   conclusion independently.

4. **Conclusion.** For `h ∈ H <= Aut(F_n)`, steps 2 and 3 give
   `|h|_{Aut(F_n)} <= L |ĥ|_Γ <= L(A |ĥ|_{SV_Γ} + B)`. Conversely `|ĥ|_{SV_Γ} <= M' |h|_{Aut(F_n)}` for a
   constant `M'`. So word length in `SV_Γ`, restricted to `Aut(F_n)`, is equivalent to word length in
   `Aut(F_n)`. That is part 2 of the target, and `H = Aut(F_n)` gives part 1. ∎

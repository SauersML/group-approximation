---
rg: 2
id: persistent-hosts-build-the-input-from-its-carries-proof
kind: route
title: States of centralizing elements differ from the element by a carry, carries multiply because the element commutes with K, and trivial carries at level one force the identity
target: persistent-hosts-build-the-input-from-its-carries
requires: []
---

Lane proof, 2026-09-18 (bh-free-17). Notation as in the target.

**Part 1.**
- **Carries lie in `K`.** Let `c ∈ C_1` and `x ∈ X`. Then `c^x ∈ Γ` and `r(c^x) = r(c) = c` by
  persistence, so `κ_x(c) = c^x c^{-1} ∈ ker r = K`.
- **Homomorphism.** For `c, d ∈ C_1`, the state rule gives `(cd)^x = c^{d(x)} d^x = c^x d^x`, since
  `d` fixes `x`. Hence
  `κ_x(cd) = c^x d^x d^{-1} c^{-1} = c^x κ_x(d) c^{-1} = κ_x(c) · c κ_x(d) c^{-1} = κ_x(c) κ_x(d)`.
  The last step uses that `c` centralizes `K`.
- **Injective.** If `κ_x(c) = 1` for all `x`, then `c^x = c` for all `x` and `c` fixes every letter.
  By induction on length, `c(x_1 x_2 ⋯ x_m) = x_1 c^{x_1}(x_2 ⋯ x_m) = x_1 c(x_2 ⋯ x_m) = ⋯ = x_1 ⋯ x_m`.
  So `c` is the identity of `T_X`, and `c = 1` because `Γ ≤ Aut(T_X)`.

**Part 2.** The kernel of `H → Aut(K)`, `h ↦ (k ↦ h k h^{-1})`, is `C` by definition. ∎

**Corollary.** Let `B ≤ H` be abelian, and let `s` be the rank of `K/M`.
1. **The part in `C_1`.** `K` has finite Prüfer rank, at most `rank(M) + s`, and so do `K^X` and all of
   its subgroups. So `B ∩ C_1` has finite torsion-free rank by part 1. `C_1` has finite index in `C`, so
   `B ∩ C` has finite torsion-free rank too.
2. **The part outside `C`.** `BC/C` is an abelian subgroup of the finitely generated group
   `L = H/C ≤ Aut(K)` from part 2.
   - `M` is characteristic, so restriction gives `ρ: Aut(K) → Aut(M) × Aut(K/M) ≤ GL(M ⊗ Q) × GL_s(Z)`.
   - **Kernel of `ρ`.** If `α ∈ ker ρ`, then `α(t) = t·d(t)` with `d(t) ∈ M`. The map `d` is a
     derivation `K/M → M` for the conjugation action, and it is determined by its values on a basis of
     `K/M ≅ Z^s`. So `ker ρ` embeds in `M^s`, which is abelian of finite rank.
   - **Image of `L`.** `ρ(L)` is a finitely generated subgroup of `GL_R(Q)` with `R = rank(M) + s`, so
     it lies in `GL_R(Z[1/N])` for some `N`. Its abelian subgroups have finite rank: they sit in unit
     groups of `Z[1/N]`-orders of commutative `Q`-algebras (the argument written out in
     `non-fp2-groups-are-quasi-retracts-of-simple-groups`).
   - Hence `BC/C` has finite torsion-free rank.
3. **Conclusion.** `B` is an extension of `B ∩ C` by `BC/C`, so `B` has finite torsion-free rank. ∎

**Why `M` is characteristic in `K_{n,N}`.** An element `t^j v` with `j ≠ 0` acts on `M` by `N^j ≠ 1`.
So a normal subgroup containing it also contains `(N^j − 1)M`, which does not commute with `t^j v`.
Hence `M` is the unique maximal abelian normal subgroup.

**Check against LISW.** There `Γ = Z[1/N]^n ⋊ (G × ⟨N⟩)`, `H = G ≤ GL_n(Z[1/N])` and
`K = K_{n,N}`. `G` acts faithfully on `Z[1/N]^n`, so `C = 1`, and part 2 is the given faithful
action. This is consistent with the corollary: abelian subgroups of `GL_n(Z[1/N])` have finite rank.

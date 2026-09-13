---
rg: 2
id: subshift-crossed-product-k0-is-coinvariant-group-proof
kind: route
title: Algebraic Pimsner–Voiculescu for the regular supercoherent ring LC(X,F_q), then K_0 of a directed union of finite products of fields
target: subshift-crossed-product-k0-is-coinvariant-group
requires:
  - abc-twisted-laurent-k-theory-fibration
artifacts:
  - research/artifacts/un-orbit-equivalence-2026-09-13-part2.md
---

Put `A = LC(X,F_q)` and `σ(f) = f ∘ T^(−1)`, a unital ring automorphism, so that `R_X = A[t,t^(−1);σ]` with `t = u`.

**Step 1: A is a directed union of finite products of fields.** For each finite clopen partition `P`, the functions
constant on the atoms of `P` form `A_P ≅ F_q^P`. `A` is the directed union of the `A_P` under refinement.

**Step 2: A is regular supercoherent.** Every module over a finite product of fields is projective, hence flat, so
each `A[t_1..t_p] = colim_P A_P[t_1..t_p]` is a directed union with flat transition maps.
- Each stage `A_P[t_1..t_p]` is a finite product of polynomial rings over `F_q`: Noetherian and regular.
- A finitely presented module over the colimit is induced from a finitely presented module `M_P` at some stage.
  `M_P` has a finite resolution by finitely generated projectives, and flat base change keeps it exact. So every
  finitely presented `A[t_1..t_p]`-module has a finite resolution by finitely generated projectives.
- Kernels of maps between finitely presented modules are computed at a finite stage and stay finitely presented
  after flat base change. So finitely presented modules form an abelian subcategory.
Hence `A[t_1..t_p]` is regular coherent for every `p`, and `A` is regular supercoherent in the sense quoted in
`abc-twisted-laurent-k-theory-fibration`.

**Step 3: the fibration.** `A` is unital, hence H-unital, and `σ` is a unital isomorphism. Theorem 3.6 with `A = Z`
(Step 1 of its proof) and Lemma 7.2 give
`K_0(A) →(1−σ_*) K_0(A) → K_0(R_X) → K_(−1)(A) →(1−σ_*) K_(−1)(A)`.
The map `K_0(A) → K_0(R_X)` in the fibration is induced by the ring inclusions `A ⊆ A[t_±;σ] ⊆ R_X`.

**Step 4: K_0 and K_{−1} of A.** K-theory preserves filtered colimits (quoted). `K_0(A_P) = Z^P`, compatibly with
refinement, so `K_0(A) = C(X,Z)`, with `[χ_U] ↦ χ_U`. For the negative group, `K_(−1)(F_q) = 0`, since negative
K-theory vanishes for regular Noetherian rings. This is Bass's theorem, recalled and not re-read. Hence
`K_(−1)(A_P) = 0` and `K_(−1)(A) = 0`.

**Step 5: conclusion.** The sequence gives `K_0(R_X) ≅ coker(1 − σ_* on C(X,Z))`. Since `σ_*^(−1) = T_*^{±1}` is
bijective and `(1 − σ_*^(−1)) = −σ_*^(−1)(1 − σ_*)`, the image of `1 − σ_*` equals the image of `1 − T_*`. The unit
`[1] = [χ_X]`. ∎

**Model test.** For `T = id`, `R_X = A[t,t^(−1)]`, and the result says `K_0(A[t,t^(−1)]) = K_0(A) = C(X,Z)`. That
agrees with the Bass fundamental theorem, `K_0(A[t,t^(−1)]) = K_0(A) ⊕ K_(−1)(A)` with `K_(−1)(A) = 0`.

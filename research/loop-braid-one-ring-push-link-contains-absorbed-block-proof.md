---
rg: 2
id: loop-braid-one-ring-push-link-contains-absorbed-block-proof
kind: route
title: "Certify non-adjacency by a Stallings-graph rank invariant of free factors; build the absorbed-block homomorphism by a McCool relator check and transport it through cabling"
target: loop-braid-one-ring-push-link-contains-absorbed-block
requires:
  - pure-loop-braid-group-is-colimit-of-cabling-stabilizers
artifacts:
  - research/artifacts/zp-loop-braid-one-ring-push-absorbed-block-2026-09-17.md
  - research/artifacts/zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md
  - experiments/loop-braid-one-ring-push-2026-09-17/one_ring_push.py
  - experiments/loop-braid-one-ring-push-2026-09-17/orbit_check.py
---

The complete hand proof is in the artifact, §§1–3. It is unreviewed. The inputs are:
- the strict fundamental domain, the cabling-stabilizer generators (Cor 5.2) and the McCool
  presentation, all from `pure-loop-braid-group-is-colimit-of-cabling-stabilizers`;
- (F1)–(F2) of the w8 artifact.

1. **Invariant (Lemma 1.1, Cor 1.2).**
   - `P_(a,b)` maps `C_(a,b) = ⟨x_a x_b, x_k⟩` onto itself, as checked on the Cor 5.2 generators.
   - So `I(pP_u, qP_z) = rank(p C_u ∩ q C_z)` is a P-invariant of pairs of vertices.
   - Strictness of Q forces adjacent pairs to the standard value.
2. **Literal (★) fails (Prop. 2.1).**
   - `A_ca ∈ P_vw`, so `A_ca[(a,b)] ∈ lk(b0)`.
   - At n = 5 the Stallings pullback of `A_ca(C_ab) = ⟨x4x5, x1, x2, x4x3x4^{-1}⟩` and
     `A_vc(C_vw) = ⟨x3x1x3^{-1}x2, x3, x4, x5⟩` has rank 2, with basis `x4x5`, `x5^{-1}x3x5`,
     against the standard rank 3.
   - For n > 5, extra base loops raise both ranks by n − 5.
3. **θ is a homomorphism with π∘θ = id (Lemma 3.1).**
   - Relators without an `A_kc` are images under the pure cabling map that fattens c into
     {c, v, w}.
   - The one remaining case is `[A_ij A_cj, A_ic] ↦ [XY, Z]` with `[X,Z] = [Y,Z] = 1`, by (M3) and
     (M1).
   - π kills `x_v, x_w`.
4. **Image in `P_vw ∩ C(A_vc, A_wc)` (Lemma 3.2).** The key relation is
   `[A_vj A_cj, A_vc] = 1`, which is (M3).
5. **Cabling compatibility (Lemma 3.3).**
   - `θ∘κ''_Γ = κ_Γ∘θ'` and `π∘κ_Γ = κ''_Γ∘π'`, checked on generators. The only reordering uses
     (M1) and (M2).
   - Hence `θ(P''_σ) ⊆ P_σ` and `π(P_σ) ⊆ P''_σ`.
6. **Embedding (Thm 3.4).**
   - `Φ(p''σ) = θ(p'')σ` is well defined by step 5.
   - It is injective by strictness of Q and applying π.
   - It lands in `lk(b0) ∩ lk(h b0)`, because `h ∈ ⟨A_vc, A_wc⟩` lies in `P_σ` and commutes with
     `θ(P'')`.

Machine checks:
- `one_ring_push.py` (the certificate, and the invariant's stabilization and calibration,
  n = 5–8);
- `orbit_check.py` (all McCool relator images under θ, and the commutation, n = 6, 7).

The hand proof does not depend on them.

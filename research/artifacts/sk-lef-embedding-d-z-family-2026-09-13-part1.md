# sk-lef-embedding-d: subgroups of the Z-family G_X (part 1)

Lane sk-lef-embedding-d, 2026-09-13. Notation: `X` is an infinite minimal Z-subshift, `R_X = LC(X,F_2) ⋊ Z`, and
`G_X = EL_3(R_X)`. Question: is every f.g. LEF group a subgroup of some `G_X`?

## 1. Reduction to unit groups of matrix rings

**Proposition A.** The following are equivalent.
- (i) Every f.g. LEF group is a subgroup of `G_Y` for some infinite minimal Z-subshift `Y`.
- (ii) Every f.g. LEF group is a subgroup of `GL_m(R_X)` for some infinite minimal Z-subshift `X` and some `m ≥ 1`.

*Proof.* (i) ⇒ (ii): `G_Y ≤ GL_3(R_Y)`.

(ii) ⇒ (i). Let `Γ` be f.g. and LEF.
1. By `rf-groups-lie-in-derived-subgroups-of-rf-groups` (part 2), there are a f.g. LEF group `Δ` and an injective
   homomorphism `Γ -> [Δ,Δ]`.
2. By (ii), there is an injective homomorphism `ρ : Δ -> GL_m(R_X) = S^×`, where `S = M_m(R_X)`.
3. By `tower-subshift-elementary-group-is-el-3k-of-base` (items 1–2), `S ≅ R_(X^(m))` with `X^(m)` again an infinite
   minimal Z-subshift. So `EL_3(S) ≅ G_(X^(m))`.
4. Whitehead's lemma holds over every unital ring: for `c ∈ S^×`,
   `diag(c,c^{-1}) = e_12(c) e_21(-c^{-1}) e_12(c) · e_12(-1) e_21(1) e_12(-1) ∈ E_2(S)`. For `a,b ∈ S^×`,
   `diag(a,a^{-1},1) · diag(b,b^{-1},1) · diag((ba)^{-1},ba,1) = diag(aba^{-1}b^{-1},1,1)`,
   so `diag([a,b],1,1) ∈ EL_3(S)`.
5. The map `c ↦ diag(c,1,1)` is an injective homomorphism `S^× -> GL_3(S)`. It sends `[S^×,S^×]` into `EL_3(S)`,
   since products of commutators go to products of elements of `EL_3(S)`.
6. So `g ↦ diag(ρ(g),1,1)` embeds `[Δ,Δ]`, hence `Γ`, in `EL_3(S) ≅ G_(X^(m))`. ∎

**Remarks.**
- The overgroup is needed. `diag(a,a^{-1},1)` is a homomorphism only on commuting units, and
  `diag(u,1,1) ∉ EL_3(R_X)` (`shift-unit-of-subshift-crossed-product-is-not-elementary`).
- The same argument shows that the family `{G_Y}` is closed under passing to f.g. subgroups of
  `[GL_m(R_X), GL_m(R_X)]`, for every `X` and `m`.

**Known subgroups of the family.** Each of the following is a subgroup of some `G_Y`:
- every f.g. subgroup of `EL_n(F_2[t^{±1}])` with `n ≥ 3`, or of `[GL_m(F_2[t^{±1}]), GL_m(F_2[t^{±1}])]`, because
  `F_2[u^{±1}] ⊆ R_X`. This includes free groups and `SL_3(F_2[t^{±1}])`.
- every finite group, since `GL_d(F_2)` sits inside a tower corner.
- every f.g. subgroup of the derived topological full group `[[σ]]'` of an infinite minimal subshift, embedded as
  units of `R_X`.
- every `G_Y`, and every f.g. subgroup of `EL_(3k)(R_Y)`.

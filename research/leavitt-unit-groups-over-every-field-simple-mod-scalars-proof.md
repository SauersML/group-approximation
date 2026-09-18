---
rg: 2
id: leavitt-unit-groups-over-every-field-simple-mod-scalars-proof
kind: route
title: Run the Lean root detection without the trivial-centre hypothesis; its only exceptional case is a central scalar
target: leavitt-unit-groups-over-every-field-are-simple-mod-scalars
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
  - leavitt-center-is-coefficient-field
  - leavitt-units-embed-in-their-scalar-quotient
---

Every Lean theorem used below is stated for an arbitrary field `k` (or an arbitrary
ring). The assembly is on paper and no new Lean instance is built. The same reading
of the root-detection proof is step 4 of `prime-field-leavitt-tensor-hosts-proof`,
there for central simple `F_p`-algebras.

**Inputs, all for every field `k`.**
- **Leavitt family:** `BinaryLeavitt.family k` (`Leavitt/UniversalLeavittOver.lean`).
- **Two-sided division:** every nonzero `x` in `R` has `a, b` with `a x b = 1`
  (`BinaryLeavitt.exists_mul_mul_eq_one`, `Leavitt/LeavittSimplicity.lean`, where the
  section variable is `(k : Type) [Field k]`).
- **Centre:** every central element of `L_k(1,d)` is a scalar
  (`Leavitt/LeavittCenter.lean`; `leavitt-center-is-coefficient-field`). So the
  central units of `R` are exactly `k^x`.
- **GL = EL and perfectness:** `glAll_eq_elementary n` for `n >= 2` and
  `binaryLeavittUnits_perfect` (`KOne/AllRanksElementary.lean`, `variable (k : Type)
  [Field k]`; `leavitt-gl-equals-el-and-perfect-unit-group`).
- **Leaf coordinates:** the complete prefix code `{0, 10, 11}` gives a unital
  `k`-algebra isomorphism `φ: M_3(R) -> R`, `φ(M) = Σ s_(c_i) M_ij t_(c_j)`, hence
  `U ≅ GL_3(R)` (`prefixUnitsEquiv (leftCombCode 2)`). Since `φ` is `k`-linear and the
  code is complete, `φ(λ I) = λ`.

**Step 1 (root detection modulo the centre).** Let `N` be a normal subgroup of
`EL_n(R)`, `n >= 3`, containing some `g` that is not of the form `λ I` with `λ` a central
unit. Then `N` contains a root `e_ij(x)` with `x != 0`. The proof is
`rootDetection_of_leavittFamily` in `Leavitt/RootDetectionBinary.lean`, with one change:
- **Off-diagonal branch.** If `g^-1` has a nonzero off-diagonal entry,
  `exists_elGen_mem_of_offDiag_inv` applies. Its ring obligation comes from
  `exists_split_annihilator`, which needs only the Leavitt family and division. No
  hypothesis on the centre is used.
- **Diagonal branch.** Otherwise `g` is diagonal (`elMat_inv_offDiag`). In
  `exists_elGen_mem_of_diagonal`, either some commutator `[g, e_uv(a)]` is a nonzero
  root in `N` (the second case of the proof), or `g` commutes with every root. In the
  latter case `exists_unit_elMat_eq_diagonal_of_commute_elGen` and
  `elMat_diag_central_unit_of_commute_elGen` show `g = λ I` with `λ` a central unit.
  The hypothesis `hcentral` is used only after this point, to turn `λ` into `1`. Here
  that case is excluded by the choice of `g`.

**Step 2 (a root generates everything).** `elementaryGroup_normal_eq_top_of_elGen_mem`
(`Leavitt/ElementaryNormalGeneration.lean`, used inside `isSimpleGroup_of_rootDetection` of
`Leavitt/ElementarySimplicity.lean`) takes
`3 <= n`, a nonzero root in `N`, and division, and gives `N = EL_n(R)`. It makes no
assumption on the centre.

**Conclusion.**
- **Part 4.** By Steps 1–2, a normal subgroup of `EL_n(R)` either consists of central
  scalar matrices or is everything. The central scalar matrices in `EL_n(R)` are
  `λ I`, `λ ∈ k^x`, by the centre input. So `EL_n(R)` modulo them is simple, and it
  is nontrivial because `e_12(1)` is not scalar.
- **Part 2.** Transport through `U ≅ GL_3(R) = EL_3(R)`: under `φ`, `λ I` corresponds to
  `λ ∈ k^x`. A normal subgroup of `U` not inside `k^x` pulls back to a normal subgroup
  of `EL_3(R)` containing a non-scalar element, hence equal to `EL_3(R)`.
- **Part 1** is `binaryLeavittUnits_perfect`.
- **Part 3.** Simplicity of `U/k^x` follows from part 2. The unit
  `w = s_0 t_1 + s_1 t_0` is not scalar, so the quotient is nontrivial.
  `leavitt-units-embed-in-their-scalar-quotient` embeds `U` in `U/k^x`. `U` contains
  the roots `e_12(s_0^j)`, `j >= 0`, which are pairwise distinct, so the quotient is
  infinite. It is nonabelian because `[e_12(1), e_23(1)] = e_13(1)` is not scalar.

QED

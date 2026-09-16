---
rg: 2
id: sl2-root-triangle-tensor-reps-iff-zero-holonomy
kind: claim
title: A semilinear Kazhdan SL_2 root triangle has a representation that is a twisted tensor module at all three vertices if and only if its Frobenius holonomy is zero
distinct_from:
  sl2-root-triangle-tensor-vertex-reps-force-2hol-zero: that assumes only a tensor model at one vertex and the commutation pattern at the other two, and needs 2·hol ≠ 0; this assumes tensor modules at all three vertices, uses the exact commutator scalars, and also covers hol = f/2
  sl2-root-triangle-2dim-iff-zero-frobenius-holonomy: that characterizes two-dimensional representations; this characterizes the tensor-type representations of dimension up to 2^f, whose spectra can be all of Z/f
artifacts:
  - research/artifacts/sl2-root-triangle-frobenius-holonomy-2026-09-16.md
---

**Setting.** Take the data and notation of `sl2-root-triangle-tensor-vertex-reps-force-2hol-zero`:
- `q = 2^f >= 8`, `k = F_q ⊂ F = F_{q^2}`, `s ∈ F \ k`;
- all three relative twists semilinear, `φ_e(x) = λ_e x^{2^{a_e}}`;
- Frobenius holonomy `hol = a_12 + a_23 - a_13 ∈ Z/f`.

For `T ⊆ Z/f`, let `L(T) = ⊗_{c ∈ T} V^{(c)}` as a module of `SL_2(k)`. For `T ⊆ Z/2f`, let
`L_F(T) = ⊗_{t ∈ T} V^{(t)}` as a module of `SL_2(F)`.

Call a representation `ρ: Λ -> GL(M)` over a field `K ⊇ F` **tensor-type** if:
- `ρ|_{A_1} ≅ L(T_1)` and `ρ|_{A_2} ≅ L(T_2)` for nonempty `T_1, T_2 ⊆ Z/f`;
- `ρ|_{A_3} ≅ L_F(T_3)` for a nonempty `T_3 ⊆ Z/2f` on which `t ↦ t mod f` is injective.

The Steinberg-type restrictions of section 5 of the artifact are the case `T_1 = T_2 = Z/f`.

**ESTABLISHED (unreviewed).** A semilinear member has a tensor-type representation if and only if `hol = 0`.

**Proof sketch.**
- **`hol = 0`.** Compose the vertex-injective map `Λ -> SL_2(q^2)` of
  `sl2-root-triangle-2dim-iff-zero-frobenius-holonomy` with `L_F(T_3)`.
- **`2·hol ≠ 0`.** This is `sl2-root-triangle-tensor-vertex-reps-force-2hol-zero`, because tensor-type
  restrictions at `A_2` and `A_3` satisfy its pairing condition (P).
- **`2·hol = 0 ≠ hol`** (`f` even, `hol = f/2 = h`).
  - In that argument the commutant step still confines the edge-23 operator `z_d` to
    `span{1, x_{c_1}} ⊗ span{1, y_{c_1 + h}}`.
  - The restrictions at `A_2` and `A_3` now fix the commutators exactly. At `A_2`,
    `[X^u_e, X^v_e] = 1`; at `A_3`, `[X^u_e, X^{v(s·)}_e] = s^{2^{t_e}}`, with `t_e ∈ T_3` the lift of `e`. So
    `z_d = β x_{c_1} + γ y_{c_1 + h}`, and `β`, `γ` are determined.
  - Then `[z_d, z_{d+h}]` is a scalar, and it vanishes only if `s^{2^{t}}` and `s^{2^{t'}}` differ by a factor
    in `k^*`, where `t' - t ∈ {h, h + f}`.
  - With `w = s^{2^t} ∉ k` and `r = 2^h = sqrt(q)`, this says `w^{r-1} ∈ k^*` or `w^{rq-1} ∈ k^*`. Both
    exponents are coprime to `q + 1`, so this forces `w ∈ k`, a contradiction.

**Consequence for the candidates.** Two constructions of finite quotients have been examined in this series:
- vertex-injective maps onto `SL_2(q^2)`;
- tensor-type representations.

For semilinear twists each exists exactly when `hol = 0`. For `q = 16` the new case `hol = 2` accounts for
54,000 of the 162,000 semilinear triples with `hol ≠ 0`. The count of triples with `hol = h` is
`f^2 (q-1)^3` for each `h`.

**Calibration.**
- For `hol = f/2` the commutation pattern alone does not obstruct: the pair `x_0 + y_2`, `x_2 + y_0`
  commutes (`tensor_gluing.py`, part (3)). The obstruction comes from the scalar `s ∉ k` in the
  commutator at `A_3`.
- For `hol = 0` the same scalar equations are solvable inside one slot. The commutators with `E_12` and `E_21`
  prescribe the off-diagonal entries `b, a` of `z = [[p, a], [b, p]]`, and `z` is square-zero once `p^2 = ab`.

**What it does not say.**
- Nothing about non-semilinear members.
- Nothing about representations that are not tensor-type at some vertex: reducible or non-split
  restrictions, `L_F(T_3)` with `T_3` meeting a residue class twice, or restrictions like `S^2 V`.
- It does not exclude finite quotients.

Proof: `sl2-root-triangle-tensor-reps-iff-zero-holonomy-proof`.

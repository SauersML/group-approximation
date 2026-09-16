---
rg: 2
id: sl2-root-triangle-tensor-vertex-reps-force-2hol-zero
kind: claim
title: A semilinear Kazhdan SL_2 root triangle with 2·hol ≠ 0 has no representation that is an irreducible twisted tensor module at one vertex and slot-diagonal at the other two, so Steinberg-type gluings do not exist
distinct_from:
  sl2-root-triangle-2dim-iff-zero-frobenius-holonomy: that excludes two-dimensional representations by the spectrum count; this excludes a class of representations of dimension up to q whose spectra are all of Z/f, where the spectrum count gives nothing
  sl2-root-triangle-char2-frobenius-spectrum-transport: that constrains only the Frobenius spectra; this uses the commutation pattern between the coefficient operators of different edges together with the tensor structure at one vertex
artifacts:
  - research/artifacts/sl2-root-triangle-frobenius-holonomy-2026-09-16.md
---

**Setting.** Take the data and notation of `sl2-root-triangle-char2-frobenius-spectrum-transport`:
- `q = 2^f >= 8`, `k = F_q ⊂ F = F_{q^2}`, `s ∈ F \ k`, standard parametrizations `p_i^e`;
- coefficient operators `X_c^p`, and spectra `S_i ⊆ Z/f`.

Assume all three relative twists are semilinear, `φ_e(x) = λ_e x^{2^{a_e}}`, with Frobenius holonomy
`hol = a_12 + a_23 - a_13 ∈ Z/f`. Let `K ⊇ F` be a field of characteristic 2 and `ρ: Λ -> GL(M)` a
representation.

**Two vertex conditions.**
- **(T) Twisted tensor at `A_1`.** `ρ|_{A_1}` is isomorphic to `L(T_1) = ⊗_{c ∈ T_1} V^{(c)}` for some
  nonempty `T_1 ⊆ Z/f`. Here `V` is the natural module of `SL_2(k)` and `V^{(c)}` its twist by `y ↦ y^{2^c}`.
- **(P) Slot-diagonal pairing at `A_2` and `A_3`.** At vertex `i ∈ {2, 3}`, let `p` and `p'` be its two
  parametrizations: `u, v` at `A_2`, and `u, v(s·)` at `A_3`. For `c, d ∈ S_i`, the operators `X_c^{p}` and
  `X_d^{p'}` commute iff `c ≠ d`.

Condition (P) holds at `A_2` when `ρ|_{A_2}` is a direct sum of modules `L(T)`, `T ⊆ Z/f`. It holds at `A_3`
when `ρ|_{A_3}` is a direct sum of modules `⊗_{t ∈ T} V^{(t)}` of `SL_2(F)`, each with `T ⊆ Z/2f` mapping
injectively to `Z/f`.

**ESTABLISHED (unreviewed).** If `2·hol ≠ 0` in `Z/f`, then no representation satisfies both (T) and (P).

In particular, for such a member no representation has Steinberg-type restrictions:
- the Steinberg module `St = L(Z/f)` of dimension `q` at `A_1` and `A_2`;
- a module `⊗_{t ∈ T_3} V^{(t)}` at `A_3`, with `T_3` a transversal of `Z/2f -> Z/f`.

For `f` odd the hypothesis is just `hol ≠ 0`. For `q = 8` it covers all 6174 semilinear triples with
`hol ≠ 0`.

**Mechanism.** Write `x_c = X_c^{v}` and `y_c = X_c^{u}` at `A_1`. In the tensor model these are
`E_21` and `E_12` in slot `c`.
- (P) at `A_2` and `A_3`, transported along the edges, says that the edge-23 operator with label `d` fails
  to commute with exactly one `y` (label `c_1 = d + a_12`) and exactly one `x` (label `c_1 - hol`).
- If `hol ≠ 0`, it commutes with all of slots `≠ c_1, c_1 - hol`, with `x_{c_1}` and with `y_{c_1 - hol}`. So
  it lies in `span{x_{c_1}, y_{c_1-hol}, x_{c_1} y_{c_1-hol}}`.
- The edge-23 operators with labels `d` and `d + hol` then have commutator
  `A ⊗ B ⊗ [x_{c_1}, y_{c_1}]` in the three distinct slots `c_1 - hol`, `c_1 + hol` and `c_1`, with `A, B ≠ 0`.
  That is nonzero, but operators of one edge group commute.

**Calibration.**
- If `hol = 0`, the two labels coincide and the edge-23 operator can be the slot-`c_1` root element. This
  is realized by composing the two-dimensional configuration of
  `sl2-root-triangle-2dim-iff-zero-frobenius-holonomy` with `L(T)`.
- If `2·hol = 0 ≠ hol` (`f` even, `hol = f/2`), the local obstruction disappears. For `f = 4`, `hol = 2`, the
  pair `x_0 + y_2`, `x_2 + y_0` commutes and has the required non-commutations
  (`experiments/sl2-root-triangle-frobenius-holonomy-2026-09-16/tensor_gluing.py`, part (3)). So the
  hypothesis `2·hol ≠ 0` cannot be dropped from this argument.

**What it does not say.**
- Nothing about non-semilinear members: their transport mixes labels modulo `𝔞^2`, and the argument
  needs exact transport.
- Nothing about representations that are not twisted-tensor at any vertex, such as non-split extensions.
- It does not exclude finite quotients. It removes the most natural candidate construction of `q`-dimensional
  representations, the open sub-question of section 5 of the artifact, when `2·hol ≠ 0`.

Proof: `sl2-root-triangle-tensor-vertex-reps-force-2hol-zero-proof`.

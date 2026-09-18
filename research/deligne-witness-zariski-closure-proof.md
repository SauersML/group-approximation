---
rg: 2
id: deligne-witness-zariski-closure-proof
kind: route
title: Classify connected Q-subgroups of Sp4 with a faithful symplectic 4-space and send each non-Hilbert, non-dense case to a Maslov pruning or to the virtually Fuchsian vanishing theorem
target: deligne-witness-packets-are-zariski-dense-or-hilbert-type
requires:
  - virtually-fuchsian-coefficients-have-zero-schur-kernel
  - deligne-schur-witness-needs-maslov-carrying-packet
  - amenable-coefficients-have-zero-schur-kernel
artifacts:
  - research/artifacts/sp4-schur-zariski-closure-packets-2026-09-17.md
  - experiments/sp4-schur-zariski-closure-packets-2026-09-17/verify.py
---

The full case analysis is in the artifact, Section 3. The exact packet is in
Section 4, with Parts A--B of
`experiments/sp4-schur-zariski-closure-packets-2026-09-17/verify.py`.

**Standard facts recalled.**

- (F-alg) The unipotent radical and the derived group of a connected `Q`-group
  are `Q`-groups.
- The identity component of the Zariski closure of `B` is normalized by `B`
  and meets `B` in finite index.
- Weyl's classification of low-dimensional representations.
- (F-Sel) Selberg's lemma.

**Packet reductions** (from `deligne-schur-witness-needs-maslov-carrying-packet`,
applicable to a finite-index `B_0`):

- P2: a proper nonzero rational invariant subspace kills.
- P3: a real Lagrangian invariant subspace kills.
- P4: containment in a connected closed subgroup of zero winding, such as a
  simply connected one, kills.

**Steps.**

1. **C0.** `V^{R_u(H)}` is nonzero, proper and rational, and `B` preserves it:
   P2.
2. **C1.** `B` is virtually abelian:
   `amenable-coefficients-have-zero-schur-kernel`.
3. **C2**, types. A faithful symplectic 4-space admits only `A1`
   (`[2,1,1]`, `[2,2]`, `[4]`), `A1 x A1` on `W_1 + W_2`, or `Sp_4`.
   - `G2` needs dimension at least 7.
   - `A2` has no self-dual 4-dimensional representation.
   - `V1 (x) V1` is orthogonal.
   - `V_2 + V_0` is not symplectic.
4. **[2,1,1].** `V^{H'}` is a rational symplectic plane: P2.
5. **[4].** The centralizer is `{±1}`, so `H = H'`.
   - `H(R) = SU(2)`: `B_0` is finite.
   - `H(R) = SL_2(R)`: `B_0` is discrete, and by (F-Sel) `B` is virtually a
     torsion-free Fuchsian group. By `virtually-fuchsian-coefficients-have-zero-schur-kernel`,
     `K_2(Gamma, w) = 0`.
6. **[2,2].** `V = W (x) U`, and `H = H'T` with `T <= SO(U, g)`.
   - `T` R-split: the weight space `W (x) u_+` is isotropic by weight count,
     hence a real Lagrangian: P3.
   - `T` compact or trivial: modulo the compact normal subgroup, `B_0` is
     finite-by-(Fuchsian or finite). The image of a discrete group is
     discrete, with finite kernel. So `B` is finite or virtually a
     torsion-free Fuchsian group, and the vanishing theorem or amenability
     applies.
7. **A1 x A1.** The centralizer is finite, so `H = H'`. Galois permutes
   `{W_1, W_2}`.
   - Both planes fixed: P2.
   - `K` imaginary quadratic: `H(R) = SL_2(C)` is simply connected: P4.
   - `K` real quadratic with a compact factor: as in step 6.
   - `K` real quadratic with two noncompact factors: this is the survivor.
8. **Not virtually Fuchsian.** This is
   `virtually-fuchsian-coefficients-have-zero-schur-kernel` applied to `B_c`.

In every dead case `alpha_H(K_2(Gamma, w)) = 0`. Either `K_2` vanishes, or the
Maslov pairing `<e, K_2>` vanishes by (MP2).

---
title: Research attack on a hyperlinear non-sofic group (user notebook, 2026-08-26)
provenance: user-supplied research notebook, pasted 2026-08-26; audited the same day
---

Audit summary (2026-08-26). Verdicts against the graph: the presentation-double /
intertwiner program (Sections 4-8, 13A, 16, 17) is new and its proofs check;
wired as `normal-kernel-restriction-rigidity-for-map-free-quotients`,
`leavitt-presentation-double-forces-restriction-instability`,
`intertwiner-retention-makes-leavitt-quotient-hyperlinear`,
`leavitt-presentation-double-positive-rank-retention` (open) and the route
`hyperlinear-nonsofic-from-leavitt-retention`. Section 2 (MAP iff RF for
finitely generated groups) is classical (Mal'cev) and recorded once as
`finitely-generated-map-groups-are-residually-finite`. Section 3 (fermionic
amplifier) is a new concrete functor exhibiting the rate obstruction the graph
already carries (`adaptive-tensor-amplification`, `mf-implies-hyperlinear-via-rank-profile`);
recorded as `exterior-power-amplifier-needs-dimension-defect-rate`. Sections
9-10 (free-lamp HNN) reuse the graph's `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`
object; the graph's verbatim reading of Alekseev--Bradford (2026-08-14) is that
their permanence needs a sofic set action, refuted by Kun--Thom Corollary D, so
Certificate B is recorded as the open claim `kt-free-lamp-hnn-group-is-hyperlinear`
with that caveat. Section 14's warning matches
`shulman-symmetric-double-has-no-stable-trace-upgrade`. The last step of
Theorem 7.1 (injective homomorphism into a tracial ultraproduct implies
hyperlinear) is `abstract-unitary-embedding-upgrades-to-hyperlinear`.

The notebook follows verbatim.

---

# Research attack on a hyperlinear non-sofic group

**Date:** 2026-08-26
**Target:** exhibit a discrete group that is hyperlinear but not sofic.
**Status after this attack:** **NO COMPLETE PROOF SURVIVED VERIFICATION.**

This file is intentionally written as a research notebook rather than as a polished survey. It separates established inputs, deductions proved here, conditional reductions, and failed ideas. I will not label a conditional implication as the requested theorem: the existence of a hyperlinear non-sofic group is still open in the sources checked through 2026-08-26.

The main genuinely useful additions of this attack are:

1. a clean **MAP obstruction** showing that no finitely generated non-sofic candidate can be separated by honest finite-dimensional unitary representations;
2. a quantitative **fermionic/exterior-power rank amplifier**, together with an exact calculation showing why it *does not* turn operator-norm MF approximations into hyperlinear approximations without a dimension-versus-defect rate;
3. a new **presentation-double / intertwiner transform** for the simple Kazhdan Leavitt quotient, which converts Shulman's weak-MF symmetric-double models into an explicit instability problem for restrictions of finite-dimensional representations;
4. an **exact restriction-rigidity theorem**: for a finitely generated minimally almost periodic quotient `Q=F/K`, two finite-dimensional representations of `F` that agree on `K` must agree everywhere;
5. a corresponding **approximate restriction-instability theorem** forced by Shulman's symmetric-double MF theorem when `Q` is the known non-sofic Leavitt quotient;
6. a precise **positive-rank intertwiner-retention criterion** which, if proved for those unstable pairs, gives an actual hyperlinear model of `Q` and therefore the desired hyperlinear non-sofic group;
7. a rederivation of the Kun--Thom double inside a **free-lamp centralizing HNN extension**, followed by an audit against the 2026 Alekseev--Bradford hyperlinear-action permanence theorem. This identifies a second very sharp finish: prove that the induced free-lamp automorphism action is a sofic-hyperlinear action even though the underlying coset action is non-sofic.

The strongest unresolved point is not algebraic existence of matrix models. It is **trace-visible rank retention**.

## 1. Ground truth and candidates

### 1.1 What is already known externally

- **Sofic implies hyperlinear.**
- Explicit **non-sofic groups now exist** (OpenAI, August 2026).
- Kun--Thom, *Nonsofic wreath products of residually finite groups*, arXiv:2608.06222, gives explicit residually finite Kazhdan groups `Gamma < G` with `Gamma` infranormal but nonnormal, and proves non-soficity of the generalized wreath construction; the current 2026-08 version also treats the symmetric double `G *_Gamma G`.
- Shulman, *The MF property for amalgamated free products*, arXiv:2603.13564, proves in particular that if `A` is MF and `C <= A`, then the symmetric full amalgam `A *_C A` is MF in the **operator norm** sense.
- Alekseev--Bradford, *Sofic actions, halo products, and metric approximations of groups*, arXiv:2601.18742, proves closure of hyperlinear groups under semidirect products whose action is a suitable **sofic hyperlinear action**; for free/graph wreath products their directly stated criterion still assumes the underlying action on the index set is sofic.

The distinction between the two approximation topologies is load-bearing: **weak/operator MF** (multiplication and injectivity in operator norm) versus **hyperlinear** (multiplication and separation in normalized Hilbert--Schmidt norm). Operator norm can detect a defect supported on one coordinate; normalized `2`-norm can erase it.

### 1.2 Two concrete non-sofic targets

**Candidate A: the Kun--Thom double** `D = G *_Gamma G`. Known: `D` is non-sofic; `D` is weak/operator-MF (Shulman's symmetric amalgam theorem, RF vertex group). Unknown: is `D` hyperlinear?

**Candidate B: the simple Leavitt quotient** `Q = EL_4(L_{F_2}(1,2))`. The repository records: `Q` is finitely generated, simple, Kazhdan, and non-sofic. If `Q` is hyperlinear, the problem is solved immediately.

## 2. First no-go theorem: finitely generated MAP is the same as residually finite

**Theorem 2.1.** Let `H` be finitely generated. If finite-dimensional unitary representations separate the points of `H` (MAP), then `H` is residually finite.

*Proof.* Fix `1 != h in H`; MAP gives `rho : H -> U(d)` with `rho(h) != I`. `rho(H)` is a finitely generated linear group over `C`, hence residually finite by Mal'cev; a finite quotient `psi` of `rho(H)` separates `rho(h)`, and `psi o rho` separates `h`. ∎

**Corollary 2.2.** For finitely generated groups, MAP iff residually finite. **Corollary 2.3.** No finitely generated non-sofic group is MAP. Any hyperlinear model of a finitely generated non-sofic group must be genuinely asymptotic.

## 3. Why weak MF does not automatically become hyperlinear: an attempted rank amplifier

`U_d = diag(-1,1,...,1)` has `||U_d-I||_op = 2` and `||U_d-I||_2 = 2/sqrt(d)`.

**3.1 Exterior-power character formula.** For `U in U(d)` with eigenvalues `lambda_j`, `Lambda^* U = (+)_k Lambda^k U` on the `2^d`-dimensional exterior algebra has `Tr(Lambda^* U) = prod_j (1+lambda_j)`, normalized character `chi_F(U) = 2^{-d} det(I+U)`. If `|lambda_j - 1| >= delta` for one `j`, then `|(1+lambda_j)/2| = sqrt(1-|lambda_j-1|^2/4) <= sqrt(1-delta^2/4)`, so `|chi_F(U)| <= sqrt(1-delta^2/4) < 1`: operator-norm separation from `I` becomes dimension-independent tracial separation.

**3.2 The fatal multiplicativity calculation.** For `W = exp(i epsilon) I_d`, `Lambda^k W` is multiplication by `exp(i k epsilon)`. With the phase-neutral `R(U) = Lambda^* U (x) conj(Lambda^* U)`, `chi_R(U) = |det(I+U)/2^d|^2`, and `chi_R(W) = cos(epsilon/2)^(2d)`, so `||R(W)-I||_2^2 = 2 - 2 cos(epsilon/2)^(2d) = 2 - 2 exp(-(1+o(1)) d epsilon^2/4)`. A necessary scale for `R(W) -> I` in normalized `2`-norm is `d epsilon^2 -> 0`.

**Theorem 3.1.** Exterior/Fock amplification converts a fixed operator-norm spectral gap into a fixed normalized-trace gap, but preserves asymptotic multiplicativity only under `d_n epsilon_n^2 -> 0`. Weak MF supplies only `epsilon_n -> 0`. There is no dimension-free black-box argument `operator-MF => hyperlinear` by exterior amplification.

## 4. A presentation-double transform for the Leavitt quotient

Let `Q` be the simple non-sofic Leavitt quotient, `q : F -> Q` a surjection from a finite-rank free group, `K = ker q`. Form `P = F *_K F`. Since `C*(F)` is MF, Shulman gives `C*(P) = C*(F) *_{C*(K)} C*(F)` operator-MF.

**4.1 Exact left-right intertwiner representation.** For finite-dimensional `u,v : F -> U(H)`, define `Pi(f)(T) = u(f) T v(f)^*` on `HS(H)` and `V = Hom_K(v,u) = {T : u(k)T = T v(k), k in K}`.

**Lemma 4.1.** `V` is `Pi(F)`-invariant and `Pi|_V` factors through `Q = F/K`. *Proof.* For `T in V`, `f in F`, `k in K`: `u(k)u(f)Tv(f)^* = u(f)u(f^{-1}kf)Tv(f)^* = u(f)Tv(f^{-1}kf)v(f)^* = u(f)Tv(f)^*v(k)`, so `Pi(f)T in V`; and `Pi(k)T = u(k)Tv(k)^* = T`. ∎

## 5. Exact restriction rigidity for minimally almost periodic quotients

**Lemma 5.1.** A finitely generated, infinite, simple, non-sofic `Q` has no nontrivial finite-dimensional unitary representation (a faithful one would make `Q` linear, hence residually finite by Mal'cev, hence sofic).

**Theorem 5.2 (restriction rigidity).** If `u,v : F -> U(d)` agree on `K`, they agree on `F`. *Proof.* `I in V`; by Lemma 4.1 `Pi|_V` is a representation of `Q`, trivial by Lemma 5.1, so `I = Pi(f)(I) = u(f)v(f)^*`. ∎

**Corollary 5.3.** Restriction `Hom(F,U(d)) -> Hom(K,U(d))` is injective for every `d`.

## 6. Shulman forces a strong approximate failure of that rigidity

**Theorem 6.1 (approximate restriction instability).** There are exact `u_n,v_n : F -> U(d_n)` and `c > 0` with (1) `||u_n(k)-v_n(k)||_op -> 0` for every fixed `k in K`, (2) `||u_n(f_0)-v_n(f_0)||_op >= c` along an infinite tail, for a fixed `f_0 notin K`. *Proof sketch.* Lift the generator images of an injective norm-corona representation of `P` to unitaries; the vertex groups are free, so they extend to exact `u_n, v_n`; `i_0(k) = i_1(k)` in `P` gives (1); the reduced word `w_0 = i_0(f_0)i_1(f_0)^{-1} != 1` and injectivity give (2). ∎

The exact restriction map is injective in every dimension but has no dimension-uniform modulus of continuity in pointwise operator norm.

## 7. Positive-rank intertwiner retention would finish the problem

`Pi_n(f)(T) = u_n(f)Tv_n(f)^*` on `H_n = HS(C^{d_n})`; `xi_n = I/sqrt(d_n)` satisfies `||Pi_n(k)xi_n - xi_n|| = ||u_n(k)-v_n(k)||_2 -> 0`. The defect at `f_0` may live on one singular direction.

**7.1 Criterion.** For subspaces `W_n <= H_n` with projections `P_n`, `r_n = dim W_n`, normalized HS norms `||.||_{2,r_n}` on `W_n`: (IR1) `||(I-P_n)Pi_n(f)P_n||_{2,r_n} -> 0` for fixed `f`; (IR2) `||(Pi_n(k)-I)P_n||_{2,r_n} -> 0` for fixed `k in K`; (IR3) `liminf ||(Pi_n(f_0)-I)P_n||_{2,r_n} > 0` for some `f_0 notin K`.

**Theorem 7.1.** (IR1)-(IR3) imply `Q` hyperlinear, hence a hyperlinear non-sofic group. *Proof.* Compress and polar-decompose to `sigma_n(f)`; (IR1) gives asymptotic multiplicativity; (IR2) makes `sigma_n` descend asymptotically to `Q`; the resulting `Theta : Q -> prod_omega U(r_n)` is nontrivial by (IR3), and simplicity makes it injective. ∎

**7.2** An exactly `K`-trivial, exactly `F`-invariant sector would be a finite-dimensional representation of `Q`, trivial by Lemma 5.1; so any successful sector is genuinely asymptotic.

## 8. A spectral form of the retention problem

With `K_m = {k_1..k_m}` exhausting `K` and `A_{n,m} = sum_j (Pi_n(k_j)-I)^*(Pi_n(k_j)-I)`, `<A_{n,m}xi_n, xi_n> -> 0`. **Target Lemma 8.1:** find `m(n) -> infinity`, `eta_n -> 0` with `r_n = rank 1_[0,eta_n](A_{n,m(n)}) -> infinity` such that the sector almost reduces `Pi_n(F)` and retains a fixed displacement of `f_0`. A single low-energy direction has zero normalized profile inside `d_n^2`; the kernel `K` (a subgroup of a free group) has no property (T) to supply a spectral gap.

## 9. Kun--Thom double inside a free-lamp HNN extension

`H = <G, s | s gamma s^{-1} = gamma, gamma in Gamma> = G *_Gamma (Gamma x Z)`. **Lemma 9.1:** `G cap sGs^{-1} = Gamma` (Britton), so `<G, sGs^{-1}> ~= G *_Gamma G = D`. The retraction `H -> G`, `s |-> 1`, has kernel free on `s_x = g s g^{-1}`, `x = g Gamma`, so `H ~= F(G/Gamma) x| G`.

## 10. Audit against Alekseev--Bradford

If `G -> Aut(F(G/Gamma))` is a sofic hyperlinear action in their sense, `H` is hyperlinear and contains the non-sofic `D`. Their convenient theorem derives such an action from a sofic action on the set `G/Gamma`, which Kun--Thom Corollary D refutes. A universal statement ("every basis-permuting action of a sofic group on a free group is sofic hyperlinear") cannot be justified by the obvious free-group charts, or the embedded double would be sofic.

## 11-12. Fock covariance, exact separation

Finite Fock truncations have exact covariance but the wrong trace; random-matrix microstates have the right trace but no coherent implementers of the non-sofic quasi-regular action. `D` is finitely generated and non-sofic, hence not MAP: some `1 != w in D` is trivial in every finite-dimensional unitary representation.

## 13. Three certificates

**A** (Leavitt presentation-double retention): prove Target Lemma 8.1. **B** (Kun--Thom free-lamp action): prove the free-lamp action is sofic hyperlinear. **C** (reduced MF for the double): prove `C_r^*(D)` MF; with the unique canonical trace (repository note `notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md`, `q = 2`), an MF embedding pulls the matrix trace back to the canonical trace and embeds `L(D)` in `R^omega`.

## 14-16. Failed attempts

"Weak MF + unique reduced trace => hyperlinear" is false as written (Shulman embeds the full amalgam, not `C_r^*(D)`). "Operator gap -> exterior power -> hyperlinear" fails at the `d epsilon^2` rate. "Use exact `K`-intertwiners" destroys the defect (Section 7.2).

## 17-18. Next technical attacks

Two-scale spectral windows `1_[a_n,b_n](A_{n,m(n)})` retaining the unstable mass just above zero; the needed commutator estimate `||[A_{n,m}, Pi_n(f)]||_2 <= C kernel_error` requires approximately conjugation-invariant weights on `K`, a Folner-type request with no reason to hold; property (T) of `Q` may substitute. For the free-lamp gate: fibered/projective orbit models absorbing forced coset collisions as unitary holonomy controlled by cocycles of the Kazhdan stabilizer `Gamma`.

## 19-21. Verdict

Every route returns to one requirement: the non-permutation information must occupy positive normalized trace after the multiplicative error is renormalized. No complete proof; the sharpest single missing theorem is positive-rank intertwiner retention for the Shulman microstates of `F *_K F`, `Q = EL_4(L_{F_2}(1,2))`.

## 22. Sources checked

Kun--Thom arXiv:2608.06222; Shulman arXiv:2603.13564; Alekseev--Bradford arXiv:2601.18742; the OpenAI non-sofic construction; Mal'cev's theorem. Repository inputs: `hyperlinear-nonsofic-group`, `binary-leavitt-unit-group-hyperlinear`, `symmetric-double-weak-mf`, `reduced-amalgam-canonical-trace-is-mf`, `kt-pair-group-double-is-nonsofic`, `kun-thom-wreath-weak-mf`, `notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md`, `notes/FALSE_KAZHDAN_CORNER.md`, `notes/NOTEPAD.md`.

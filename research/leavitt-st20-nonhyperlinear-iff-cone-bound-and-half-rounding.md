---
rg: 2
id: leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding
kind: claim
title: St_20 of the binary Leavitt algebra is non-hyperlinear iff a quantitative head bound holds for genuine representations of its residually finite Cuntz-cone cover and asymptotic representations round flexibly on one Kazhdan cone half
distinct_from:
  leavitt-cone-cover-kernel-is-dense-in-every-compact-model: that shows exact finite or compact models of the cone cover never separate the head from the kernel, and names the quantitative head bound as the surviving next step; this proves that bound is one of exactly two prerequisites of non-hyperlinearity of Delta, the other being flexible rounding on a cone half, and that its failure makes Delta hyperlinear.
  leavitt-cuntz-cone-halves-have-rf-amalgam-cover: that builds the cover and decomposes the MF radical through MF representations of Gamma trivial on the relators; this is the tracial (normalized Hilbert--Schmidt) decomposition with the relators only approximately trivial, and it adds the half-rounding prerequisite that the exact MF statement does not see.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that forbids strict HS stability of the infinite, residually finite Kazhdan halves; this needs only flexible rounding on a half, and only of restrictions of asymptotic representations of Delta.
  non-hyperlinear-group: that is the flagship; this is an equivalent split of the flagship-level statement for the one group Delta, not a proof of it.
artifacts:
  - research/leavitt-st20-cone-bound-half-rounding-proof.md
  - research/flexible-rounding-glues-across-finite-edge-amalgams.md
---

**ESTABLISHED** (route `leavitt-st20-cone-bound-half-rounding-proof`; lane proof
swarm-0917-w16-w16-ptm-pull, obstruction-miner, stability-approximation; unreviewed).

**Setting** (`leavitt-cuntz-cone-halves-have-rf-amalgam-cover`).
- `R = L_(F_2)(1,2)` and `Delta = St_20(R) = GL_20(R)`, which is simple, infinite and finitely generated.
- `z = x_13(s_1 t_1)`.
- `Delta_+-` are the Cuntz-cone halves, and `Delta_0 = Delta_+ ∩ Delta_- = SL_20(F_2)^2` is finite and
  contains `z`.
- `Gamma = Delta_+ *_(Delta_0) Delta_-` is residually finite, `p : Gamma -> Delta` is onto, and
  `K = ker p` is the normal closure of `k_1, ..., k_r`.

Norms are normalized Hilbert–Schmidt. An *asymptotic representation* of `Delta` is a sequence of maps
`σ_n : Delta -> U(d_n)` with `||σ_n(gh) - σ_n(g)σ_n(h)||_2 -> 0` for all `g, h`.

**The two prerequisites.**

```text
(QC)   For every eps > 0 there is delta > 0 such that every genuine finite-dimensional unitary
       representation rho of Gamma with  max_i ||rho(k_i) - 1||_2 <= delta  has  ||rho(z) - 1||_2 <= eps.

(HR)   For every asymptotic representation σ_n of Delta, the restriction σ_n|Delta_+ is flexibly
       roundable on Delta_+: there are genuine λ_n : Delta_+ -> U(D_n), D_n >= d_n, D_n/d_n -> 1, with
       ||σ_n(x) - P λ_n(x) P*||_2 -> 0 for every x in Delta_+.
```

**Theorem.**
1. **Split.** `Delta` is not hyperlinear **iff** `(QC)` and `(HR)` both hold.
2. **Refutation side.** If `(QC)` fails, then `Delta` is hyperlinear. Consequently `(LNC3)` of
   `agent-leavitt-not-bcs-negative-root-corner` fails.
3. **Halves-exact form of (QC).** `(QC)` holds iff every asymptotic representation of `Delta` whose
   restrictions to `Delta_+` and to `Delta_-` are genuine homomorphisms has `||σ_n(z) - 1||_2 -> 0`.
4. **Mirror.** `(HR)` for `Delta_+` is equivalent to the same statement for `Delta_-`, by the
   automorphism `g -> (g^*)^(-1)`. Only one half is needed.
5. **Stable halves.** If `Delta_+` is flexibly HS-stable, then `(HR)` holds, `Gamma` is flexibly
   HS-stable, and `Delta` is non-hyperlinear iff `(QC)`.
6. **Strict rounding is not available.** `Delta_+` is infinite, residually finite (hence hyperlinear) and
   Kazhdan. By `infinite-hyperlinear-kazhdan-group-is-not-hs-stable`, it is not even locally strictly
   HS-stable. So `(HR)` can hold only in the flexible, relative form stated: for restrictions of
   asymptotic representations of `Delta`, with dimension change.

## What this settles and kills

- **The w16 next step is flagship-level, and only half of it.**
  - `leavitt-cone-cover-kernel-is-dense-in-every-compact-model` left the quantitative bound `(QC)` as
    the next step, for the stability-approximation family.
  - `(QC)` is **necessary** for this hole, since `(LNC3)` implies non-hyperlinearity, which implies
    `(QC)`. It is **not sufficient** even for non-hyperlinearity of `Delta` without `(HR)`.
  - With `(HR)`, `(QC)` **is** non-hyperlinearity of `Delta`.
  - So no proof of `(QC)` can be cheaper than the flagship `non-hyperlinear-group` restricted to
    `Delta`, unless `(HR)` fails.
- **Class killed: cone-cover correction arguments.** These are arguments that prove non-hyperlinearity
  of `Delta`, or the MF-radical collapse, by correcting approximate representations of `Delta` to
  genuine representations of the residually finite cover `Gamma`, and then bounding the head through
  the relators `k_i`.
  - *Invariant:* property (T), infinitude and residual finiteness of the halves.
  - *Death step:* the correction of a half.
    - It cannot be strict (item 6), because the halves are Kazhdan, infinite and hyperlinear.
    - The gluing across `Delta_0` is never the obstacle (`flexible-rounding-glues-across-finite-edge-amalgams`).
    - So every member must prove `(HR)`: flexible rounding of a Kazhdan residually finite group,
      relative to `Delta`.
    - No input already on the graph (finite models, compact models, charges on `K`, twist or holonomy
      invariants) bears on `(HR)`.
- **Both prerequisites can fail on their own.**
  - `(HR)` concerns non-genuine approximations of one half. `(QC)` concerns genuine representations
    of `Gamma` only.
  - A counterexample to `(QC)` is a sequence of pairs `(ρ_+, ρ_-)` of genuine representations of the
    residually finite halves that agree on the finite group `SL_20(F_2)^2`. The pairs must make every
    `k_i` almost trivial while the `(-1)`-eigenspace of `ρ(z)` keeps positive normalized dimension.
    Such a sequence refutes `(LNC3)` outright.
  - A failure of `(HR)` with `(QC)` true would make `Delta` hyperlinear through approximations that no
    genuine cover representation shadows.

Derivation: `leavitt-st20-cone-bound-half-rounding-proof`.

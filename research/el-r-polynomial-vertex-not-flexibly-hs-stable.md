---
rg: 2
id: el-r-polynomial-vertex-not-flexibly-hs-stable
kind: claim
title: The Kun--Thom vertex EL_r(F_q[x_1..x_d]) is not flexibly HS-stable, with no extension to the actor required
distinct_from:
  hs-stable-vertex-rounding-for-every-model: that is (H1), rounding of the vertex at every actor-extendable model, the positive side; this is the existence of some non-roundable asymptotic representation of the vertex alone, the negative side without the extension constraint.
  kt-hyperlinear-coset-wreath-forces-nonroundable-vertex: that derives a non-roundable actor-extendable vertex model from a hyperlinear coset wreath; this asks for a non-roundable vertex model outright, which is necessary for that conclusion but weaker.
  rf-kazhdan-group-not-flexibly-hs-stable: that proves instability for Z^2g x| Sp_2g(Z) through a non-torsion H^2 class; this asks for it at the vertex, where finite H_2 voids that mechanism.
---

**OPEN.** Let `Γ = EL_r(F_q[x_1..x_d])` with `r, d >= 3`. The claim is that for some such
`(q, r, d)` there is an asymptotic representation `α_n : Γ -> U(d_n)` (normalized HS) with no
flexible rounding. Here flexible rounding means genuine `π_n : Γ -> U(D_n)` with `D_n >= d_n`,
`D_n/d_n -> 1` and `||α_n(g) - P_nπ_n(g)P_n*||_2 -> 0` for all `g`. No extension of `α_n` to the
actor `G` is required.

**Why it matters.** Every route to Pestov's Question 3.4 through a Kun--Thom coset wreath or
double needs this, in the stronger actor-extendable form
(`kt-hyperlinear-coset-wreath-forces-nonroundable-vertex`). Its failure at every
actor-extendable model is (H1) (`hs-stable-vertex-rounding-for-every-model`), which makes the
wreaths non-hyperlinear.

## Attempts

- **Class-wide stability does not block it (2026-09-13, lane `ex-hs-instability-kazhdan`).**
  `rf-kazhdan-group-not-flexibly-hs-stable`: property (T), residual finiteness and a regular
  limit trace do not force flexible rounding. So no argument using only those features can prove
  the negation of this claim.
- **Scalar cocycles: dead wherever `H_1` and `H_2` of the vertex are finite**
  (`finite-multiplier-projective-models-round-strictly`).
  - `Γ` is perfect for `r >= 3`, and projective models whose cocycles tend to 1 round strictly.
  - This kills the Ioana--Spaas--Wiersma Theorem A and Dogon Theorem 1.3 mechanisms at the vertex.
  - Finiteness of the multiplier is expected for `r` in the stable range, where it should be
    `K_2(F_q[x]) = 0`. This is not source-verified.
- **Reduction to one variable (elementary).**
  - `x_1 -> t`, `x_j -> 0` for `j >= 2` retracts `Γ` onto `EL_r(F_q[t]) = SL_r(F_q[t])`.
  - Flexible stability descends to retracts: round the composite with the retraction, then
    restrict to the section.
  - So instability of `SL_r(F_q[t])` gives the claim for every `d`.
- **Kazhdan covers (`kazhdan-cover-models-round-iff-kernel-fixed-mass-one`).** Models pulled back
  from a Kazhdan cover round exactly when the kernel's fixed subspace has full normalized
  dimension. Two covers were examined.
  - **Rank 3, truncated covers: open, route recorded.**
    - `SL_3(F_q[t])` is Kazhdan and not finitely presented. Dogon arXiv:2211.10492v3 names
      `SL_3(F_p[X])` as an infinitely presented property (T) group. The rank warning in
      `approximate-collapse-for-kt-compressor` records Krstić--McCool for `E_3`, `St_3` over
      rings onto `F[t]`.
    - The corollary of the criterion applies once some finitely presented cover sequence has
      extra finite quotients (`sl3-polynomial-covers-have-extra-finite-quotients`).
    - Route: `el-r-vertex-instability-via-rank-three-covers`.
  - **Rank 3, central extension of a congruence subgroup: open, route recorded.**
    - `flexible-hs-stability-descends-to-retracts-finite-index` lets instability pass up
      from a finite-index subgroup `Δ` of `SL_3(F_q[t])`.
    - At such a `Δ`, the scalar mechanism can come back to life. It needs a real degree-two class
      whose Kazhdan central `Z`-extension keeps its centre visible at unbounded orders in finite
      quotients (`sl3-polynomial-finite-index-z-extension-center-survives`).
    - Route: `el-r-vertex-instability-via-congruence-central-extension`.
    - The Deligne cover of `Sp_(2g)(Z)` is the failure model.
  - **Noncommutative cover `EL_r(F_q⟨x_1..x_d⟩)`: screened, not proved dead.** The kernel
    contains the shallow elements `e_ij([x_a, x_b])`.
    - In congruence-type irreducibles of finite quotient rings, (KC1) at these finitely many
      elements seems to force the representation level below the depth of the commutator ideal.
      There the kernel acts trivially.
    - This is a Clifford-orbit heuristic, not a proof.
- **Stable range `r >= 5`: no handle.**
  - `Γ` is expected to be finitely presented there. The synthesis in the rank warning above
    verified Tulenbaev only from the abstract.
  - So the truncated-cover corollary is unavailable, and the scalar mechanism is void.
  - No instability mechanism is known.
- **Where content must live.** Any non-roundable model has asymptotically regular-type
  congruence mass only at escaping levels (`theorem-e-congruence-projections-vanish-at-regular-trace`).
  The truncated-cover models are exactly of that kind: exact on larger and larger balls, and
  nontrivial only on relators of growing index.
- **Actor extension (2026-09-13, lane `ex-hs-instability-extension`).** Retract-based witnesses never reach
  `hs-stable-vertex-rounding-for-every-model`.
  - **The torus argument.** Let `σ : G -> U(M)` be any homomorphism with `σ(e_ij(x_2 f)) = 1` for all `f`,
    as for `α∘r`.
    - Then `σ(e_12(x_2^2)) = 1`. The torus element `t = diag(x_2, x_2^(-1), 1, ...) ∈ EL_r(L)` conjugates
      `e_12(1)` to `e_12(x_2^2)`, so `σ(e_12(1)) = 1`.
    - Then `e_ij(f) = [e_ik(f), e_kj(1)]` makes `σ|Γ` trivial.
  - **Consequence.** The model `α∘r` equals, in `M`, the vertex restriction of an actor model only when `α` is
    trivial. The same holds for the congruence-central-extension route, whose final models are again pulled back
    through `r`.
  - **Trace-preserving models.** They are never pulled back from a proper quotient of `Γ`.
  - **What an actor-extendable witness must be instead.** It must be totally non-roundable, at intertwining distance
    at least the Kazhdan constant from every genuine-coordinate model
    (`compressor-extension-makes-roundable-vertex-part-invariant`).

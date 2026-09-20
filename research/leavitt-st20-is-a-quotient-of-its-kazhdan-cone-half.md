---
rg: 2
id: leavitt-st20-is-a-quotient-of-its-kazhdan-cone-half
kind: claim
title: St_20 of the binary Leavitt algebra is a quotient of its residually finite Kazhdan cone half, the kernel obeys a head bound with linear modulus, and so Delta is non-hyperlinear iff pullbacks of its asymptotic representations round flexibly on the half
distinct_from:
  leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding: that splits non-hyperlinearity of Delta into the amalgam-cover head bound (QC) and half-rounding (HR) of restrictions; this replaces the amalgam cover by a surjection Delta_+ ->> Delta, proves the matching head bound (QN) outright, and leaves one prerequisite (PR) about pullbacks, not restrictions.
  flexibly-hs-stable-kazhdan-kernel-quotient-rf-or-nonhyperlinear: that needs the kernel itself to have property (T); here the kernel N is not known to be Kazhdan, and the bound comes from property (T) of E_20 of the fibre-product ring R_+ x_R R_+ instead.
  hyperbolic-kazhdan-cover-of-leavitt-unit-group: that covers the Leavitt unit group by a hyperbolic Kazhdan group; this covers St_20(R) by the residually finite linear-type group E_20(R_+), with no hyperbolicity.
  leavitt-cone-cover-hamming-head-bound-holds: that proves (QC) for monomial representations of the amalgam cover; this proves the analogous bound for all finite-dimensional unitary representations of the quotient cover.
  non-hyperlinear-group: that is the flagship; this reduces it, for the one group Delta, to a single rounding statement on a residually finite Kazhdan group.
artifacts:
  - research/leavitt-st20-quotient-of-cone-half-proof.md
---

**ESTABLISHED** (route `leavitt-st20-quotient-of-cone-half-proof`; lane swarm-0917-w22-w22-nh-last1,
reframing; unreviewed).

**Setting** (`leavitt-cuntz-cone-halves-have-rf-amalgam-cover`).
- `R = L_(F_2)(1,2)`, with `t_i s_j = δ_ij` and `s_1 t_1 + s_2 t_2 = 1`. Put `q = s_1 t_1`.
- `Delta = St_20(R) = GL_20(R)`, which is simple, infinite and Kazhdan.
- `R_+ = <s_1, s_2, q>` and `Delta_+ = <x_ij(a) : a in R_+> = E_20(R_+)`.
  - `Delta_+` is residually finite and Kazhdan.
- `Delta_0 = E_20(F_2 q + F_2(1-q)) = SL_20(F_2)^2`.

Norms are normalized Hilbert–Schmidt.

**Theorem.**

1. **The half is a free path algebra.**
   - `R_+` is the path algebra `F_2 Q` of the quiver with two vertices `e, f`, a loop at each vertex
     and one arrow each way.
   - The isomorphism sends `e -> q` and `f -> 1-q`. It sends the loops and arrows to
     `q s_1 q`, `q s_1 (1-q)`, `(1-q) s_2 q` and `(1-q) s_2 (1-q)`.
2. **R is 2-generated.** `R` is generated as an `F_2`-algebra by `X = Θ(P)` and `Y = Θ(D)`.
   - `Θ : M_16(R) -> R` is the ring isomorphism `A -> sum s_μ A_μν t_ν` over words of length 4.
   - `P` is the cyclic shift.
   - `D = diag(1, 1, 0, s_1, 0, s_2, 0, t_1, 0, t_2, 0, 0, 0, 0, 0, 0)`.
3. **Surjection fixing the edge.** There is a surjective unital ring homomorphism `φ : R_+ ->> R`
   with `φ(q) = q`. It is given by:
   ```text
   q s_1 q -> s_1 X t_1,   q s_1 (1-q) -> s_1 t_2,   (1-q) s_2 q -> s_2 t_1,   (1-q) s_2 (1-q) -> s_2 Y t_2.
   ```
   - So `φ(s_1) = s_1 (X t_1 + t_2)` and `φ(s_2) = s_2 (t_1 + Y t_2)`.
   - Entrywise, `φ_* : Delta_+ ->> Delta` is onto and is the identity on `Delta_0`.
   - `I = ker φ` is a finitely generated two-sided ideal, say by `a_1, ..., a_m`.
   - The mirror `φ_-(r) = φ(r^*)^*` gives `Delta_- ->> Delta`, also the identity on `Delta_0`.
4. **(QN): kernel head bound with linear modulus.** Let `N = ker φ_*` and
   `F = {x_ij(a_k) : i != j, k <= m}`, a subset of `N`. There is `κ > 0`, a Kazhdan constant of
   `E_20(D)` with `D = R_+ x_R R_+`, such that every finite-dimensional unitary representation `λ`
   of `Delta_+` satisfies:
   ```text
   max_(x in F) ||λ(x) - 1||_2 <= δ   ==>   codim(V^(Delta_+))/dim V <= (δ/κ)^2
                                        ==>   ||λ(g) - 1||_2 <= 2δ/κ   for every g in Delta_+.
   ```
   Moreover `V^N = V^(E_20(R_+, I)) = V^(Delta_+)` for every such `λ`, because
   `Delta_+ / E_20(R_+, I)` has no nontrivial finite quotient.
5. **Single-prerequisite split.** Let `(PR)` be the statement that for every asymptotic
   representation `σ_n` of `Delta`, the pullback `σ_n ∘ φ_*` is flexibly roundable on `Delta_+`.
   Then `Delta` is not hyperlinear **iff** `(PR)` holds.
6. **Stable half suffices.** If `Delta_+` is flexibly HS-stable, then `Delta` is not hyperlinear. So
   `non-hyperlinear-group` follows. Along the way `(QC)` and `(HR)` hold, by
   `leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding`. No separate proof of `(QC)` is
   needed on the stability route.

## What this settles and kills

- **(QC) leaves the stability route.**
  - Through the amalgam cover `Gamma = Delta_+ *_(Delta_0) Delta_-`, the route needed both `(QC)`
    and `(HR)`. `(QC)` is a bound for the free kernel `K`, and waves 16 to 21 found it open.
  - Through the quotient cover `φ_* : Delta_+ ->> Delta`, the matching bound `(QN)` is a theorem
    (item 4), with linear modulus and explicit finite test set `F`. What remains is the single
    rounding statement `(PR)`.
- **Dichotomy.** Either `Delta` is not hyperlinear, or `E_20(F_2 Q)` is not flexibly HS-stable.
  - `E_20(F_2 Q)` is residually finite, Kazhdan and perfect.
  - In the second case the witness is explicit: `σ_n ∘ φ_*` for any hyperlinear approximation `σ_n`
    of `Delta`.
- **Class killed: pullback-near-genuine hyperlinear approximations.** Let `σ_n` be an asymptotic
  representation of `Delta` whose pullback to `Delta_+` is close to genuine representations of
  `Delta_+`, in the flexible sense. Then `σ_n -> 1` pointwise.
  - *Invariant:* property (T) of `E_20(R_+ x_R R_+)`, together with simplicity and infinitude of `R`.
  - *Death step:* the intertwiner `T` of item 4 fixes `V^N`, and `V^N` carries a representation of
    the group `Delta_+ / E_20(R_+, I)`, which has no finite quotients.
- **Why the Kazhdan-kernel lemma was not enough.**
  - `flexibly-hs-stable-kazhdan-kernel-quotient-rf-or-nonhyperlinear` needs `N` itself to be
    Kazhdan. Here only the relative bound for the normal subgroup `E_20(R_+, I)` is used.
  - That relative bound holds because `E_20(R_+, I)` is the image of `ker p_2` in the Kazhdan group
    `E_20(D)`.
- **Survivor.** `(PR)`, recorded as `leavitt-cone-half-pullback-rounding`.
  - It holds if `Delta_+` is flexibly HS-stable.
  - The cheap instability mechanism is absent: the non-torsion `H^2` classes of
    `rf-kazhdan-group-not-flexibly-hs-stable` do not occur. `H_1(Delta_+) = 0`, and
    `K_2(F_2 Q) = K_2(F_2 x F_2) = 0` stably (Gersten; Dicks for hereditary tensor algebras). That
    `K_2` value is cited, not needed.

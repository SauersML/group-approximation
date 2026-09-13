---
rg: 2
id: ternary-leavitt-units-have-no-weakly-finite-representation
kind: claim
title: The ternary Leavitt unit group has no nontrivial homomorphism into the unit group of any weakly finite F_3-algebra
refuted_by:
  - ternary-leavitt-units-have-a-nontrivial-char-three-rank-model
distinct_from:
  ternary-anti-central-summand-has-no-weakly-finite-image: that is the ring-level statement about quotients of S_-; this is the same content read as a statement about group homomorphisms into units, equivalent by ternary-weakly-finite-representations-give-anti-central-images.
  sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one: that is absence of Sylvester rank functions moving z, weaker in general; this is absence of every weakly finite host algebra, which refutes Gottschalk outright.
artifacts:
  - research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md
---

**OPEN.** Let `G = L_(F_3)(1,2)^x`. Every group homomorphism from `G` into the unit group of a weakly finite
`F_3`-algebra (one where `AB = I_n` implies `BA = I_n`) is trivial.

**Status of the equivalences.**
- **Equivalent to** `ternary-anti-central-summand-has-no-weakly-finite-image` (routes
  `no-weakly-finite-representation-from-summand-obstruction` and
  `summand-no-weakly-finite-image-from-no-representation`), and to
  `ternary-weakly-finite-representations-kill-two-root-defect`.
- **Refutes Gottschalk on `G`.** The quotient `F_3[G] -> S_-` has no weakly finite image, so `F_3[G]` is not
  stably finite (artifact Corollary 1.2).

**What refutes it.**
- any overgroup `H` of `G` with `F_3[H]` stably finite;
- any nontrivial characteristic-three rank model of `G`.

## Attempts

- 2026-09-12 `w5-wf-obstruct`: opened as the group form of the target (artifact Section 3).
  - **Stage one.** A certificate must start with an exact one-sided pair over `S_-`. The natural isometry
    lifts are left zero divisors, and their cross term squares to the indicator of a nonempty set of odd
    measures (artifact Section 4).
  - **Firewalls.** Every landed anti-central model (sofic subgroups containing `z`, locally finite bases with
    HNN letters, Fock local letters) lives in a weakly finite algebra. An obstruction must use multi-letter
    relations with overlapping supports, or non-level Steinberg commutators.
  - **E⋊V.** An obstruction using only `E⋊V` would show that `V` has no nontrivial weakly finite
    representation over `F_3`, hence that `V` is not sofic.
  - **No mechanism found.**
- 2026-09-12 `w6-mismatch-c3`: the mismatched pair is not an escaping configuration
  (`research/artifacts/depth-monotone-leavitt-firewall-2026-09-12.md`).
  - **Stably finite side algebras.** For every letter weight, the span of the `s_μ t_ν` with
    `ω(μ) <= ω(ν)` is stably finite, and its units over `F_3` are locally residually finite
    (`depth-monotone-leavitt-subalgebras-are-stably-finite`).
  - **Firewall.** `T_(0,1)`, `T_(1,00)`, their product (of infinite order), all level roots at every depth, `E`,
    level `V` and the depth-decreasing transvections lie in one such unit group. With all its relations, that
    group has a weakly finite model with `z -> -1` (`depth-monotone-configurations-cannot-force-ternary-minus-one`).
    So the relations in `W` give neither a one-sided pair nor a contradiction.
  - **Where it must go.** The group elements of a certificate must generate a subgroup that no conjugation puts
    inside any weighted unit group. Candidates: elements of `V` that are weight-level for no weight, and sets like
    `{T_(0,1), T_(1,0), T_(1,00), T_(00,1)}`. These escape without conjugation only, and no conjugation invariant
    is proved. The models kill `D`, so the defect form is not firewalled.
- 2026-09-12 `w7-escape-set`: the conjugation invariant, and the four-transvection set tested
  (`research/artifacts/four-transvection-escape-set-2026-09-12.md`).
  - **Invariant.** The span of `S4 = {T_(0,1), T_(1,0), T_(1,00), T_(00,1)}` contains `x`, `y` with
    `yx = 1 != xy`. So no conjugate of `<S4>` lies in any weighted unit group, and every three of the four lie in
    one. Local finiteness on cylinder functions excludes `x_0` and every group containing it
    (`four-transvection-set-escapes-depth-monotone-units`).
  - **Not the candidate.** Code `(0,1)` puts `<S4>` inside `EL_2(J_(F_3))` with `z in <S4>`. The symbol onto
    `SL_2(F_3[ζ, ζ^(-1)])` is a weakly finite model with `z -> -1`. Every five-transvection set `S4 ∪ {T}` has a
    character model into `GL_2(F_3)`. Six transvections span `R`, and from there on no algebra-level firewall applies
    (`four-transvection-units-have-a-weakly-finite-symbol-image`).
  - **Defect form.** Algebra-level models kill `D`. Sofic subgroups containing `z` and the frame have weakly finite
    models with `D != 0`, and so has `H^ω_≤` for `ω(0) <= ω(1)` (`depth-monotone-units-carry-weakly-finite-nonzero-defect`).
    The smallest open input is `Γ_5 = <S4, x_23(1)>` (`four-transvections-and-x23-force-defect-vanishing`).

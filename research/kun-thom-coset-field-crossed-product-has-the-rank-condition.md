---
rg: 2
id: kun-thom-coset-field-crossed-product-has-the-rank-condition
kind: claim
title: The characteristic-p generalized Bernoulli rational function field over the Kun-Thom coset space has a skew group ring with the rank condition
distinct_from:
  some-field-crossed-product-fails-the-rank-condition: that asks for any witness over any group; this is one explicit skew group ring that every certificate in the graph misses and whose failure would give a free-action Rokhlin deficit.
  profinitely-closed-linear-coefficients-rank-condition: that proves the rank condition for permutation modules of separable subgroups; the Kun-Thom subgroup is not separable, and this is the non-closed permutation module left open there.
  kun-thom-binary-wreaths-stably-finite-in-characteristic-two: that is stable finiteness of the group ring of the lamp group over the coset space; this localizes the Laurent lamp algebra to its fraction field, which a group-ring statement does not reach.
  bernoulli-field-rank-failure-gives-rokhlin-deficit: that covers free Bernoulli fields, where the question is settled for sofic groups; this is the coset-indexed field over a residually finite group, where it is open.
---

**OPEN.** Let `Γ < G` be the Theorem E pair of `kun-thom-free-nonsofic-action` over `F_ℓ` (for example `ℓ = 2`),
`H = G/Γ`, and `p` a prime. Is the rank condition true for

    R_p = F_p(x_c : c ∈ H) ⋊ G,    σ_g x_c = x_(gc),

that is, does `AB = I_d` with `A` of size `d x r` force `r >= d`? The same question applies to `m` variables
per coset and to every `G`-stable subfield.

**Where it sits.**
- **Implied by Seward.** Seward's direct-product conjecture at `(X_(Q,d), Y^(Q,m)_Γ)` implies it. So does the
  `Q`-ary variant of test (a) in `kun-thom-nonsofic-action-carries-full-bernoulli-entropy`, for every `p`
  (`coset-field-rank-failure-gives-relative-bernoulli-deficit`).
- **Implied by entropy-profile proofs** of Bernoulli maximality at `G`
  (`twisted-linear-profile-deficits-are-rank-condition-failures`).
- **Characteristic 0 is settled.** `Q(x_c) ⋊ G` has the rank condition through the invariant iid complex
  measure (Corollary 3 there). Every failure over any field reduces to some `R_p`.

**Every certificate in the graph misses it.**
- **Amenable, algebraic, char-0 measure** (`field-crossed-product-rank-condition-survival-cases`). `G` is
  Kazhdan, the field is transcendental, and the characteristic is `p`.
- **Finite-field point models, in every form.** Random models along sofic approximations, exact periodic
  models and projective models all fail, by `kun-thom-coset-field-has-no-finite-field-point-models` (Theorem C).
- **Bi-orderable or virtually Hughes-free groups.** `G` has `p`-torsion and no torsion-free finite-index
  subgroup (`kun-thom-actors-have-no-torsion-free-finite-index-subgroups`).
- **Finitely generated or rational coefficient fields.** The orbit field has infinite transcendence degree.
- **Embedding in a sofic Bernoulli field.** The `Γ`-fixed field of `k'(x_g : g ∈ G)` is `k'`. An invariant
  rational function has a canonical finite variable support, which would be `Γ`-invariant, while `Γ` is infinite
  and acts freely on `G`. So no equivariant embedding `x_Γ -> K_G` exists.

**Why it is informative in both directions.**
- **A proof** would be a characteristic-`p` stable-finiteness theorem for a coefficient field whose only
  invariant point measures are nonsofic (Corollary D). It needs a mechanism other than points and other than
  complex measures.
- **A disproof** would be an explicit free p.m.p. action of a residually finite Kazhdan group whose Rokhlin
  entropy is below that of its Bernoulli factor. It would refute Seward's direct-product conjecture and answer
  need `f489b4fe` of `some-field-crossed-product-fails-the-rank-condition`.

## Attempts

- **2026-09-18, swarm-0917-w10-w10-gs-pull (linear-characteristic, obstruction). Result: a reduction plus a
  class kill. The node stays OPEN.**
  - **Reduction.** `coset-field-rank-condition-is-lamp-factorization` shows that the rank condition of `R_p` is
    equivalent to: no `w I_d`, for nonzero `w in F_p[x_c^(+-1)]` and `r < d`, factors through `T^r`, where
    `T = F_p[Z wr_(G/Gamma) G]`. So the question is about the lamp group ring. That ring is stably finite by
    `rf-lamps-preserve-stable-finiteness-for-arbitrary-actions`, but stable finiteness does not control these
    scalar matrices.
  - **Kill.** `invariant-background-certificates-miss-difference-units` covers two further certificate types:
    - the marked-site tensor maps `Phi_r`;
    - augmentation-adic and Frobenius-lamp quotients.

    Neither type can make the difference unit `w = x_c - x_c'` full. Under `Phi_r`, the image of `w I_d`
    factors through `M^r` at every `d`, with rank 0. In the quotients the image is nilpotent.
  - **Dying step.** Off a finite union of wandering site idempotents, these maps fall back to a `G`-invariant
    background (`lambda = 1`), and there the background cancels `w`. This is the same invariant as the point-model
    kill at `x_(g Gamma) - x_(gamma g Gamma)`. The kill also occurs for `G = Z`, where the rank condition holds, so
    it limits these methods and carries no evidence about the answer.
  - **What a proof now needs.** A rank function on `T` under which every nonzero lamp polynomial is full, with a
    diffuse invariant background such as iid Haar on `F_p[[t]]^H`. One candidate source is a characteristic-`p` Sylvester
    rank function on `L^0(Omega, F_p((t))) semidirect G`, which is a dimension theory for a nonsofic orbit relation.
- **Lamp group ring and Ore localization (swarm-0917-w13-w13-gs-pull, stability-approximation, 2026-09-17).
  Reduction established; the positive route dies at idempotent dilution; the node stays OPEN.**
  See `coset-field-rank-certificates-need-base-faithful-lamp-ranks` (ESTABLISHED, unreviewed).
  - **Reduction.** `R_p` is the Ore localization of `F_p[W]`, where `W = Z wr_H G`, at `S = F_p[⊕_H Z] \ {0}`.
    - Clearing denominators shows that `R_p` fails the rank condition iff some `diag(s_1..s_d)` with `s_i ∈ S`
      factors through `F_p[W]^r` with `r < d`.
    - A rank-function proof is exactly a **base-faithful** Sylvester rank function on `F_p[W]`, meaning
      `rk(s) = 1` on `S`.
  - **Class kill (idempotent dilution).**
    - **Invariant:** the rank of a site idempotent.
    - **Dying step:** its `G`-conjugates are orthogonal and indexed by the infinite coset space, so its rank is 0.
    - **Consequence:** every rank function on the marked-site targets `T_r` of the stable-finiteness proofs
      (`diagonal-tensor-orbit-corner-induction-proof`) factors through the lamp augmentation to `F_p[G]`, and
      so does every rank function on first-order jets `O/I^2`. So `rk(x_c - 1) = 0`.
    - **Belief change:** the mechanism that proved `F_p[W]` stably finite cannot reach `R_p`.
  - **Remaining suppliers.**
    - A sofic rank function. It would need `Z wr_H G` to be sofic, and would then give the rank condition for
      every `p`, by the Følner rank on the amenable lamp group (literature not in the graph). Nonsoficity is
      recorded only for binary lamps. `lamp-charts-recover-set-action` suggests it also fails for integer
      lamps, but this is not checked.
    - A linear-sofic model that is base-faithful. Group-faithfulness does not suffice: on `F_p[Z^2]`, the rank
      over the curve `x + y + 1 = 0` is group-faithful but kills `x + y + 1`.
- **Matrix-model barrier (swarm-0917-w14-w14-gs-follow, stability-approximation, 2026-09-19). The class is
  converted: every approximable supplier either dies or yields a new group. The node stays OPEN.**
  See `approximable-base-faithful-lamp-ranks-force-linear-sofic-defects` (ESTABLISHED).
  - **Answer to wave 13's question.** `W = Z wr_H G` is not sofic. `z = x_o` centralizes `Gamma`, and
    `[u z u^(-1), gamma] = x_(uo) x_(gamma u o)^(-1) != 1`, so no sofic rank function exists.
  - **Invariant:** the rank `rk(x_(uo) - x_(gamma u o))` of a lamp difference. Under any matrix model it is
    the rank distance from `1` of the rigid defect in the image group `Q`.
  - **Where it dies or converts.** Let `rk` be any rank function on `F_p[W]` that is approximable over
    characteristic `p` and gives that difference positive rank. Then `Q` is an `F_p`-linear sofic,
    nonsofic group with defect distance `rk(x_(uo) - x_(gamma u o))`, which equals `1` if `rk` is
    base-faithful. The step to `F_p` is specialization by Zariski's lemma followed by restriction of
    scalars.
  - **Consequences.**
    - If `DD(F_p-linear sofic)` holds, which for `p = 2` is the open row
      `f2-linear-sofic-groups-kill-rigid-compression-defects`, then `R_p` has no matrix model and a proof
      of the rank condition needs a non-approximable rank function.
    - Monomial and permutation models kill the lamp difference unconditionally.
    - A matrix model of `R_p` would prove the rank condition and separate sofic from `F_p`-linear sofic at
      once.
  - **What is left.**
    - A non-approximable characteristic-`p` dimension, for example on `L^0(Omega, F_p((t))) x| G`.
    - On the other side, a diagonal factorization in `F_p[W]`.
- **Rigid-defect rank length (swarm-0917-w14-w14-gs-follow, stability-approximation, 2026-09-19).
  Both remaining suppliers settled as a class kill plus a transfer; the node stays OPEN.**
  See `kun-thom-lamp-rank-certificates-force-linear-sofic-defects` (ESTABLISHED, unreviewed).
  - **The sofic supplier does not exist.** With `t` a strict compressor and `γ ∈ Γ \ tΓt^-1`, the element
    `κ = [x_(to), γ] = x_(to) x_(γto)^-1` is a nontrivial rigid compression defect in `W = Z wr_H G`. So `W` is
    nonsofic by `sofic-groups-kill-rigid-compression-defects`. So is every quotient of `W` in which `κ` survives,
    because quotients of Kazhdan groups are Kazhdan and infranormality passes to images.
  - **Invariant.** The defect lamp difference `δ = x_(to) - x_(γto) = (κ - 1) x_(γto) ∈ S` has
    `rk(δ) = ℓ_rk(κ)`, the rank length of the rigid defect. Base-faithfulness forces `ℓ_rk(κ) = 1`.
  - **Dying step (unconditional).** `ℓ_rk(κ) = 0` in each of these cases:
    - limits of convex combinations of ranks of finite-dimensional representations
      (`compression-defect-dies-in-finite-dimensions`);
    - rank functions pulled back from sofic quotients of `W`;
    - any ring map sending `κ` to 1.
  - **Transfer (the linear-sofic supplier).** Suppose `rk` is matrix-approximable over fields of characteristic `p`
    and `rk(δ) > 0`.
    - Then `W/ℓ_rk^-1(0)` embeds in `∏_ω GL_m(F_p)` with the rank metric and is nonsofic. The embedding uses three
      steps: units of the ultraproduct lift to `GL`, Nullstellensatz specialization, and restriction of scalars.
    - So a matrix-approximable rank function on `R_p` would refute `DD(F_p-linear sofic)`, which for `p = 2` is
      `f2-linear-sofic-groups-kill-rigid-compression-defects`. It would also separate sofic from `F_p`-linear sofic.
    - Conversely, if that row holds, no such rank function on `R_p` exists.
  - **Calibration.** Over `C`, `L(W) = L^∞(T^H) ⋊ G` supplies a base-faithful rank function that does not come from
    an approximation. So the kill limits approximation methods and is no evidence against the rank condition.
  - **What a proof now needs.** One of the following:
    - a non-approximable characteristic-`p` dimension theory, an analogue of `L(W)` for a nonsofic orbit relation;
    - a proof of the rank condition for `R_p` that yields no rank function.
    A matrix model would itself be a counterexample to the `F_p`-linear sofic defect row.

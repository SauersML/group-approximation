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

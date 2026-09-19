---
rg: 2
id: jacobson-el-sofic-if-haar-relation-lifts-into-bilateral
kind: claim
title: If the Haar orbit relation of EL_n(J) is a class-bijective factor of a subrelation of the sofic two-sided Laurent affine relation, then EL_n(J) is sofic and its Haar orbit-relation algebra is Connes embeddable
distinct_from:
  jacobson-haar-relation-is-laurent-affine-restriction: that reduces soficity of EL_n(J) to soficity of a restricted relation on an infinite-measure space, whose soficity is open; this reduces it to a placement question (class-bijective lift) into a relation already proved sofic, so no approximation of the one-sided relation has to be built.
  jacobson-haar-character-restricts-to-orbit-relation-summand: that shows CE of L(R_n) is forced by, and implies, CE of the Haar characters, and records that the Haar route died at amenable-by-sofic permanence for the cocycle crossed product; this replaces that permanence step by a measurable lifting problem into a sofic ambient.
  bilateral-envelope-fuses-the-mirror-kernel-with-the-head: that shows group characters of H_bi restrict head-blind to EL_n(J); this passes through the full semigroup of the Haar relation of H_bi, whose trace mu(Fix) is 1/2 at the head and is not pulled back along P -> E_+, so the fusion obstruction does not apply.
  finitary-extension-ce-iff-action-lifts-to-normalizer: that is the general II_1 lifting criterion for crossed products of R into R^omega; this is a measured-relation embedding criterion into one explicit sofic relation, and it gives soficity, not only CE.
  ce-relation-full-group-subgroups-are-hyperlinear: that transfers CE from a relation to subgroups of its full group; here EL_n(J) is not a subgroup of the full group of the sofic relation, only of the full group of a class-bijective factor of a subrelation.
artifacts:
  - research/jacobson-el-sofic-bilateral-lift-proof.md
  - research/bilateral-laurent-haar-relation-is-sofic.md
---

**ESTABLISHED** (route `jacobson-el-sofic-bilateral-lift-proof`, swarm-0917-w15-w15-nh-pull, 2026-09-19,
unreviewed).

**Setup.**
* `J`, `E = EL_n(J)` (`n >= 2`), `(X_+, μ_+) = ((F_2^n)^N, Haar)`, and the orbit relation `R_n = R_E` are as in
  `jacobson-haar-relation-is-laurent-affine-restriction`.
* For `N >= 1`, `R'_N` is the orbit relation of `A^N x| SL_N(A)` on `(F_2^(Z x {1..N}), μ)`
  (`bilateral-laurent-haar-relation-is-sofic`).

**(BL_N) Bilateral lift.** There are:
* a Borel subrelation `S ⊆ R'_N`, defined off a null set;
* a measure-preserving Borel map `r : (F_2^(Z x N), μ) -> (X_+, μ_+)`;

such that for `μ`-a.e. `y`, `r` restricts to a bijection from the class `[y]_S` onto the class `[r(y)]_(R_n)`.

**Theorem.** If `(BL_N)` holds for some `N`, then:
1. `R_n` is a sofic equivalence relation;
2. `EL_n(J)` is sofic, hence hyperlinear;
3. `L(R_n)` embeds trace-preservingly in `L(S) ⊆ L(R'_N)` and is Connes-embeddable, so the Haar fixed-point character
   `φ_1` of `EL_n(J)` is CE.

For `n = 20`, `(BL_N)` for any `N` kills the Toeplitz survivor class of `agent-leavitt-not-bcs-negative-root-corner`.

**Contrapositive (what a non-approximability proof must do).** A proof that `EL_n(J)` is not sofic, or not
hyperlinear, must show that `R_n` is *not* a class-bijective factor of any subrelation of any `R'_N`. This is a
measured statement about a relation that is itself sofic.

**The open prerequisite.** `(BL_N)` is `jacobson-haar-relation-lifts-into-bilateral-relation`. It needs no
approximation of `R_n` and no permanence theorem. It is a measurable placement problem inside a relation that is
already sofic.

Proof: [[jacobson-el-sofic-bilateral-lift-proof]].

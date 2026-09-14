---
rg: 2
id: fp-simple-groups-have-no-gapped-finite-unitary-models
kind: claim
title: A finitely presented infinite simple group has no hyperlinear approximation through unitary representations of finite groups with a uniform character-ratio gap
distinct_from:
  gap-sofic-approximations-are-local-embeddings: that is the permutation version for any countable group (a fixed-point gap makes a sofic approximation a local embedding); this is the unitary version, with the gap on irreducible character ratios at noncentral elements only, and it concludes directly for finitely presented infinite simple groups
  fp-simple-groups-escape-soft-hyperlinear-permanence: that kills marked limits and residual amenability as certificates; this kills hyperlinear approximations that factor through gapped finite groups
---

**ESTABLISHED (lane sk-fp-sofic-c, 2026-09-13, unreviewed).** Proof: `fp-simple-groups-have-no-gapped-finite-unitary-models-proof`.

**Definition.** Let θ < 1. A family of finite groups `Q_k` is *θ-gapped* if for every `k`, every nontrivial irreducible
complex character `χ` of `Q_k`, and every noncentral `q ∈ Q_k∖Z(Q_k)`, we have `|χ(q)| ≤ θ χ(1)`. Central elements are not
constrained.

**Theorem.** Let `S` be a finitely presented infinite simple group, and let `ω` be a nonprincipal ultrafilter. Suppose:
- `φ_k : S → Q_k` are arbitrary maps (not assumed multiplicative) into a θ-gapped family;
- `ρ_k : Q_k → U(d_k)` are unitary representations.

Then `π_k = ρ_k ∘ φ_k` never induces an injective homomorphism `S → ∏_ω (U(d_k), ‖·‖_2)`, where `‖A‖_2² = τ(A*A)` is the
normalized Hilbert–Schmidt norm. In words: a hyperlinear approximation of `S` cannot factor through representations of
gapped finite groups, even when the maps into the groups are arbitrary.

**Special cases.**
- **Sofic.** A sofic approximation through actions of a θ-gapped family on finite sets is such a factorization, through the
  permutation representations. So `S` has no sofic approximation through actions of a θ-gapped family.
- **Abelian targets.** Every element is central, so the family is vacuously gapped. The theorem then says that a nonabelian
  `S` has no hyperlinear models through representations of abelian groups.
- **Classical groups.** Larsen–Shalev–Tiep give θ = 2^{−1/481} for finite simply connected classical groups, uniformly in
  rank and field. Applying the theorem there is `fp-simple-groups-have-no-classical-group-unitary-models`.

**Hypotheses are needed (model tests).**
- `SL_3(Z)` is finitely presented and infinite, but not simple. It has hyperlinear, even sofic, approximations through its
  congruence quotients `SL_3(F_p)` acting on `F_p^3`, which are gapped.
- The subshift group `G_X` (`simple-kazhdan-lef-group-from-minimal-subshift`) is simple, but not finitely presented. Its LEF
  models `SL_{3N}(F_2)` acting on vectors are gapped.
- The trivial group is not infinite.
- Alternating groups on points are not gapped: a 3-cycle has character ratio `(n−4)/(n−1) → 1` in the standard module. The
  theorem says nothing about symmetric-group targets, which is where the permutation models of sofic groups live.

**What it removes.**
- On `hyperlinear-fp-infinite-simple-kazhdan-group` and `hyperlinear-fp-infinite-simple-group`: every hyperlinear or sofic
  certificate built from representations or actions of a gapped family of finite groups.
- For the ring route `sofic-fp-simple-kazhdan-group-from-fp-simple-ring`: combined with the classical-group corollary, rank
  models into `M_N(F_q)` cannot be upgraded through the representation theory of quasisimple classical groups.

---
rg: 2
id: nontrivial-higman-quotients-are-not-locally-elementary-amenable
kind: claim
title: No nontrivial quotient of Higman's group maps nontrivially to, or locally embeds into, residually finite or elementary amenable groups
distinct_from:
  nontrivial-higman-quotients-keep-all-four-bs-subgroups: that shows every nontrivial quotient keeps the four Baumslag--Solitar subgroups; this shows that no such quotient can be seen inside residually finite or elementary amenable targets, even locally.
artifacts:
  - research/artifacts/solve-higman-sofic-2026-09-13.md
---

**ESTABLISHED** by `higman-quotient-local-embedding-obstruction-proof`
(elementary; no novelty claimed).

**Statement.** Let `D` be the class of groups `Gamma` such that every nontrivial
finitely generated subgroup of `Gamma` has a nontrivial finite quotient.

1. **`D` is large.** It contains every residually finite group and every
   elementary amenable group. Here elementary amenable means Chou's class: the
   smallest class containing finite and abelian groups and closed under
   subgroups, quotients, extensions and directed unions.
2. **No nontrivial homomorphisms.** Let `Q` be a quotient of Higman's group `H4`.
   Every homomorphism from `Q` to a group in `D` is trivial. So a nontrivial `Q`
   is not elementary amenable, not residually finite, and not residually
   elementary amenable.
3. **No local embeddings.** A nontrivial `Q` is not locally embeddable into `D`.
   In particular it is not LEF, and not locally embeddable into elementary
   amenable groups.

**Consequences for soficity.**
- A nontrivial sofic quotient of `H4`, which by
  `base-two-exponential-permutations-iff-sofic-higman-quotient` is what the
  base-two Helfgott--Juschenko question asks for, must be sofic for a reason
  other than LEF or local elementary amenability.
- Kassabov--Kuperberg--Riley obtain soficity of their variations from residual
  solvability (Theorem `ressolvable`, arXiv:1712.07191). That method cannot
  reach any quotient of `H4`.

**Still open.** Amenable quotients that are not elementary amenable. Finitely
generated infinite simple amenable groups lie outside `D`, so this claim says
nothing about them.

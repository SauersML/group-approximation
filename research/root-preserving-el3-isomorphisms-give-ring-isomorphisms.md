---
rg: 2
id: root-preserving-el3-isomorphisms-give-ring-isomorphisms
kind: claim
title: An isomorphism of elementary groups E_3 that carries root subgroups to root subgroups comes from a ring isomorphism, provided the target ring is directly finite
artifacts:
  - research/artifacts/sk-rigidity-f2-2026-09-13.md
distinct_from:
  zelmanov-standard-isomorphisms-linear-groups-with-half: that proves root preservation and standardness for GL_n over rings with 1/2; this assumes root preservation and needs no 1/2, only direct finiteness of the target
  subshift-el3-isomorphisms-are-standard-over-f2: that asks whether every isomorphism of the note's groups is standard; this supplies the second half of such a proof, so only root preservation is left
---

Let `R` and `S` be unital associative rings with `S` directly finite, and let `α: E_3(R) → E_3(S)` be a group
isomorphism with `α(A_ij(R)) = A_ij(S)` for all `i ≠ j`, where `A_ij = {e_ij(r) : r ∈ R}`. Then there is a ring
isomorphism `ψ: R → S` and a unit `a ∈ S^×` with `α(e_12(r)) = e_12(a ψ(r))`. In particular `R ≅ S`.

The hypothesis may be weakened to `α` carrying the SET of six root subgroups onto the set of six root subgroups:
the commuting graph on the six is a hexagon whose 12 automorphisms are all realized on `E_3(S)`, by conjugation by
permutation matrices (which gives the simply transitive relabelling `A_ij ↦ A_{σ(i)σ(j)}`) and, when `S` carries a
ring anti-automorphism, by the graph automorphism `g ↦ (τ(g)^t)^{-1}`, which sends `A_ij` to `A_ji`.

Direct finiteness of `S` is used exactly once and cannot be dropped from this argument: it is what turns the
one-sided inverses produced by surjectivity into units.

**Review (sk-verify-5, 2026-09-13): PASS. The relation φ_ij(rs) = φ_ik(r)φ_kj(s), units from direct finiteness, ψ = a^{-1}φ_12, and the 12-element hexagon count were re-derived.** See `research/artifacts/sk-review-5-2026-09-13-part2.md` §4.

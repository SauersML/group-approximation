---
rg: 2
id: va-singular-point-germ-groups-are-t-bar
kind: claim
title: The germ group of VA at each of its singular points is a copy of T-bar whose centre is the V-shift
distinct_from:
  aff-q-does-not-embed-in-aut-thompson-f: that works inside T-bar and Aut(F) as groups of homeomorphisms of R; this identifies the local germ groups of VA on the Cantor set at every admissible singular point.
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding question; this is a structural lemma about one known host, used to locate Q inside VA.
  rational-slope-germ-groups-have-bs-but-no-heisenberg: that studies a larger germ group with rational asymptotic slopes; this computes the germ groups VA actually has.
artifacts:
  - research/artifacts/gq-gq-q-in-germs-anatomy.md
---

**ESTABLISHED** through `va-singular-point-germ-groups-are-t-bar-proof`. Lane proof from
the verbatim definition of VA; not independently reviewed. No priority is claimed.

**Setting.** `C = {0,1}^ω`. For a point `p = α0̄` (resp. `α1̄`) let `L_p` be the germ at `p`
of the prefix replacement `α0ψ ↦ αψ` (resp. `α1ψ ↦ αψ`). Belk–Hyde–Matucci,
arXiv:2407.03149v1, define `VA` as the set of `f ∈ Homeo(C)` such that, verbatim:
"(1) The singular set sing(f) is finite, and each point of sing(f) ends in either 0̄ or
1̄. (2) If p is a point in sing(f), then there exists a neighborhood of p on which f is
order-preserving and L_{f(p)}∘f agrees with f∘L_p". Singularity is relative to `V`.

**Statement.** Let `p ∈ C` end in `0̄` or `1̄`, and let `G_p` be the group of germs at `p`
of the elements `f ∈ VA` with `f(p) = p`.
1. `G_p` is exactly the set of germs at `p` of order-preserving homeomorphisms `φ` between
   clopen neighbourhoods of `p` with `φ(p) = p`, locally in `V` at every point other than
   `p`, and commuting with `L_p`.
2. The germs in `G_p` of elements of `V` are exactly `⟨L_p⟩ ≅ Z`, and `L_p` is central in
   `G_p`.
3. `G_p ≅ T̄`, the group of Belk–Hyde–Matucci (arXiv:2005.02036v4), by an isomorphism
   sending `L_p` to the centre generator `z = (x ↦ x+1)`. So `G_p / ⟨L_p⟩ ≅ T`.

**Where Q sits (consequence).** By Belk–Hyde–Matucci, arXiv:2005.02036v4, Proposition 13
("Every subgroup of T̄ isomorphic to ℚ contains the center of T̄"), quoted in
`research/artifacts/gq-gq-lit-q-embeddings.md` §1.3:
- every copy of `(Q,+)` inside a germ group `G_p` contains the V-shift `⟨L_p⟩`;
- its image in `G_p/⟨L_p⟩ ≅ T` is a copy of `Q/Z`.

So divisibility at a singular point of `VA` is torsion of Thompson's `T` lifted over the
central V-shift. In particular (Lemma C of the artifact) no germ in `G_p` normalizes such
a copy of `Q` and acts on it nontrivially. This is the germ form of item 2 of
`aff-q-does-not-embed-in-aut-thompson-f`.

**Scope.** This is about germ groups only. The global statement that no subgroup of `VA`
has a distorted cyclic subgroup is Burillo–Felipe, arXiv:2605.09763v1, Theorem 1 and
Corollary 5, recorded as obstruction O4 in `gl-n-q-embeds-in-fp-simple-group`.

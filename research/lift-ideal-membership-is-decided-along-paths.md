---
rg: 2
id: lift-ideal-membership-is-decided-along-paths
kind: claim
title: A relator lies in a lift ideal as soon as, along every infinite path, one of its sections does
distinct_from:
  polynomial-automata-reduce-to-cycling-relators: that proves lift-generation for automata satisfying (P1) by induction on a complexity that drops except at special letters; this is the path-by-path principle behind such inductions, with no activity hypothesis, so it applies to exponential-activity automata.
  rover-nekrashevych-fp-iff-finite-lift-presentation: that characterizes finite presentation of V_d(G) by finite generation of the relator kernel as a lift ideal; this is a working criterion for proving that a given finite set generates it.
---

**ESTABLISHED** by `lift-ideal-membership-is-decided-along-paths-proof` (lane proof by bh-free-02,
elementary, not independently reviewed; no priority claimed, and the principle is likely implicit
in earlier arguments).

## Statement

Notation of `rover-nekrashevych-fp-iff-finite-lift-presentation`: `S <= Aut(X^*)` is finite and
closed under sections and inverses, `F = F(S)`, and `N = ker(F -> G)`. Word-level sections `w|_u`
are taken for `u ∈ X^*`.

**Theorem.** Let `M` be a lift ideal of `F` and `w ∈ N`. Suppose that for every infinite word
`ξ ∈ X^ω` some prefix `ξ[0,n)` has `w|_{ξ[0,n)} ∈ M`. Then `w ∈ M`.

**Corollary (working criterion).** Let `R ⊆ N` be finite. Then `N = ⟨⟨R⟩⟩_lift` if and only if, for
every relator `w` and every `ξ ∈ X^ω`, some section of `w` along `ξ` lies in `⟨⟨R⟩⟩_lift`.

**Typical use.**
- Find a potential on words, such as a count of letters of given types, that sections never
  increase.
- The potential is then eventually constant along each path.
- Show that words whose potential never drops along a path are fixed points of the section map
  along an eventually periodic path.
- Show that those fixed-point relators lie in the normal closure of finitely many relators.

No bound on activity is needed.

## Lesson for general BH

Finite presentation of `V_d(G)`, which is what the automaton route to Boone–Higman consumes, is
decided by the recurrent behaviour of relators along individual infinite paths. Exponential activity
is harmless when letters die or reset at separators. What matters is which letter types survive along
which rays: persistence along a ray is the only obstruction. The first application is
`single-configuration-check-mark-group-is-lift-presented`, an exponential-activity, non-contracting
group lift-presented by two relators.

DERIVATION
lift-ideal-membership-is-decided-along-paths-proof

---
rg: 2
id: adelic-deck-lifts-exclude-affine-q-n-and-fp-bases
kind: claim
title: Lift groups through the adelic covering A^n -> (A/Q)^n cannot carry Aff_n(Q) through the deck group, and over a finitely presented base they are never finitely generated
distinct_from:
  piecewise-commutative-linear-hosts-miss-linear-gl-n-q: that covers the finitely-piecewise natural adelic models; this covers lift groups through a covering whose deck group is Q^n, whose elements have infinitely many pieces.
  fg-groups-with-normal-q-n-have-non-fp-quotients: that is the group-theoretic lemma; this is its application to the adelic covering.
  germ-extensions-omit-standard-gl-n-q: that is about groups locally in a finitely generated piecewise base off a nowhere dense set; this needs no piecewise structure, only the deck group.
artifacts:
  - research/artifacts/gq-gq-solenoid-adelic-models.md
---

**ESTABLISHED (2026-09-17)** through `adelic-deck-lifts-exclude-affine-q-n-and-fp-bases-proof`.
Not independently reviewed. This is an obstruction for the adelic family of `gl-n-q-embeds-in-fp-simple-group`.
No priority is claimed.

**Setting.** Let `A = R × A_f` be the adeles of `Q`, with `Q^n ⊂ A^n` embedded diagonally. It is discrete, with
compact quotient `Σ_n = A^n/Q^n`, the solenoid, whose continuous automorphism group is `GL_n(Q)`. The quotient
map `π: A^n -> Σ_n` is a covering map with deck group `D = {τ_q : q ∈ Q^n}`, the translations. It is the adelic
analogue of `R -> R/Z` behind `Q <= T̄` (Belk–Hyde–Matucci), with deck group `Q^n` in place of `Z`. It is spark
S1 of `research/artifacts/gq-gq-solenoid-adelic-models.md` in its deck-`Q^n` form.

**Statement.** Let `L̃ <= Homeo(A^n)` contain `D` and normalize it. For example, `L̃` may be the group of all
lifts of a group `L <= Homeo(Σ_n)` of liftable homeomorphisms. Put `L = L̃/D`. If `L̃` is finitely generated,
then:
1. the monodromy `μ: L̃ -> Aut(D) = GL_n(Q)`, defined by `f τ_q f^{-1} = τ_{μ(f) q}`, has image in
   `GL_n(Z[1/m])` for some `m >= 1`;
2. `L` is not finitely presented.

**Consequences.**
- **No finitely presented base.** Let `L` be a finitely presented group of solenoid homeomorphisms, such as a
  Thompson-type group of `Σ_n`. Its full lift group through `π` is never finitely generated. This is unlike
  `T` and `T̄` for `R -> S^1`, whose deck group `Z` is finitely generated.
- **No natural affine part.** No finitely generated lift group contains a copy of `Aff_n(Q) = Q^n ⋊ GL_n(Q)` whose
  translation subgroup is the deck group `D`. This is the natural choice, since the lifts of the automorphisms of
  `Σ_n` are the linear maps of `A^n`. As `Aff_n(Q) <= GL_{n+1}(Q)`, the deck group of `π` cannot supply the
  divisible unipotent radical of that parabolic subgroup of `GL_{n+1}(Q)`, with its natural Levi action, inside
  a finitely generated lift group. For `n = 1` it cannot supply the translations of `Aff(Q)`.
- **What is not excluded.**
  - Coverings with finitely generated deck group, for example the mapping torus
    `R^n × Ẑ^n -> Σ_n` of the `Ẑ^n`-odometer, with deck group `Z^n`. There the divisibility would have to come
    from genuinely piecewise lifts, as in `T̄`, and this claim says nothing.
  - Finitely generated lift groups over a base that is not finitely presented.
  - Divisible subgroups of a lift group that are not contained in `D`.

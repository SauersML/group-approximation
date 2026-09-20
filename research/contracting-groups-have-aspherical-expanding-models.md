---
rg: 2
id: contracting-groups-have-aspherical-expanding-models
kind: claim
title: Every finitely generated contracting self-similar group is the iterated monodromy group of an expanding partial self-covering of a compact orbi-complex whose universal cover is contractible and whose finite local groups inject into the group; this would settle the Skipper-Zaremsky question, and the limit orbispace itself never serves as the model when it is not semi-locally simply connected
distinct_from:
  contracting-rover-nekrashevych-groups-are-f-infinity: that is the Skipper-Zaremsky question; this is a stronger geometric statement that implies it through the expanding-model criterion below.
  contracting-groups-have-dying-kernel-covers-of-type-fn: that asks only for an F_n cover with dying kernel; this asks for a geometric model, which supplies such a cover of type F_infinity for every n at once.
  pcf-rational-nekrashevych-groups-are-f-infinity: that builds the model for PCF rational maps, as Thurston's orbifold minus Böttcher discs; this asks for it in general.
---

**OPEN.** Posed by lane bh-sz-vdg, 2026-09-19, as the geometric form of the remaining exponential-activity case of
the Skipper–Zaremsky question. It is not in print as far as this lane knows.

## The expanding-model criterion (lane proof; unreviewed)

An **expanding model** for a self-similar group `G ≤ Aut(T_d)` is a tuple `(M, M_1, f, ι)` with:
- `M` a compact, connected, developable orbi-complex. Equivalently, `B = π_1^orb(M)` acts properly, cocompactly and
  cellularly on a proper geodesic complex `Y`, the universal cover, with finite stabilizers.
- `f : M_1 → M` a degree-`d` orbi-covering and `ι : M_1 → M` a map of orbi-complexes.
- **Expansion:** some `λ < 1` with `length(ι γ') ≤ λ length(γ)` for every path `γ` and every `f`-lift `γ'`.
- **IMG:** the faithful quotient of the lifting recursion `B → B ≀ S_d` is `G`, with its given action.
- **(T):** every finite subgroup of `B` meets the kernel `K` trivially.

**Criterion.** If `G` has an expanding model, the recursion on `B` has dying kernel. If moreover `Y` is contractible,
then `B` has type `F_∞`, and `V_{d,r}(G)` has type `F_∞` for every `r`. The second part uses
`wreath-recursion-thompson-groups-inherit-fn` (refereed PASS, ca350037cb).

**Proof.**
- **Dying kernel.** This is Lemmas 1 and 2 of `pcf-rational-nekrashevych-groups-are-f-infinity`, whose proofs use
  only:
  - the proper cocompact isometric action on `Y`, for Lemma 1;
  - expansion, to shorten lifts;
  - (T), to exclude elliptic sections.

  None of them uses the dimension or the manifold structure of `Y`.
- **Type `F_∞`.** A proper cocompact cellular action on a contractible complex with finite cell stabilizers gives
  `F_∞`, by Brown's criterion. ∎

## Why the limit orbispace is not the model

- **The natural candidate.** For contracting self-replicating `G`, Nekrashevych shows that `G` is the IMG of the shift
  on its limit orbispace `𝒥_G` (*Self-similar groups*, §4.6 and Ch. 5; recalled, not re-read).
- **Why it fails.** The underlying limit space is usually not semi-locally simply connected. Examples:
  - the basilica Julia set, the limit space of `IMG(z^2 − 1)`;
  - the Sierpiński gasket, the limit space of the Hanoi towers group.

  Its fundamental group is then uncountable, and there is no proper cocompact universal cover. So Lemma 1 has no
  space to act on.
- **What the dynamical cases use instead.** They use a **thickening**: a compact good orbi-surface `M ⊇ J` with
  `f^{−1}(M) ⊂ M`, whose attractor is the limit space. The question above asks for an aspherical thickening in
  general.

## Remarks

- **Consistency with the torsion obstruction.** A model must carry the torsion that recurs along rays
  (`contracting-groups-have-dying-kernel-covers-of-type-fn`). (T) says that torsion must also survive in `G`. For the
  Grigorchuk group, the known virtually free cover `C_2 ∗ (C_2 × C_2)` has exactly this shape. Whether it comes from an
  expanding graph-of-groups model was not checked.
- **Finite presentation.** Nekrashevych's finitely presented dying-kernel cover `U(N)` shows that the `F_2` shadow
  of the question always has a positive answer. Whether his presentation 2-complex, with the recursion, is itself an
  expanding model, and whether it can be made aspherical, is the natural first test. Bartholdi's non-positively-curved
  contracting covers (arXiv:1107.5339, abstract only) look like the relevant idea.
- **Direction.** The question is stronger than Skipper–Zaremsky. A contracting group with no aspherical expanding
  model would not refute Skipper–Zaremsky.

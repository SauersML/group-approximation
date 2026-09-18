---
rg: 2
id: amenable-groups-of-finite-cd-are-virtually-solvable
kind: claim
title: Every amenable group of finite cohomological dimension is virtually solvable (Kropholler's question)
root: true
distinct_from:
  every-f-infinity-amenable-group-is-elementary-amenable: that asks whether amenability plus type F_infinity forces elementary amenability; this asks whether amenability plus finite cohomological dimension forces virtual solvability, with no finiteness of type assumed.
---

**OPEN.** Every amenable group of finite cohomological dimension is virtually
solvable.

*Marked `root` because it is a named open question.* D. Degrijse, "Amenable
groups of finite cohomological dimension and the zero divisor conjecture"
(arXiv:1609.07635), introduction, read from the arXiv HTML render on
2026-09-13:

- the question: "Is every amenable group of finite cohomological dimension
  virtually solvable?", "brought to the authors attention by Peter
  Kropholler";
- the evidence: "as far as we are aware none of the currently known examples
  of amenable but not elementary amenable groups are known to have finite
  cohomological dimension over any field";
- the elementary amenable case is settled: elementary amenable groups of finite
  cohomological dimension are torsion-free of finite Hirsch length (Hillman,
  J. Austral. Math. Soc. Ser. A 50 (1991), Lemma 2), hence virtually solvable
  (Hillman–Linnell, J. Austral. Math. Soc. Ser. A 52 (1992), Corollary 1).

Virtually solvable groups are elementary amenable, so the question is
equivalent to "every amenable group of finite cd is elementary amenable".

Link to Zaremsky 1.12: a torsion-free amenable non-EA group of type `F_∞` with
finite cd would answer this question negatively; see
`there-is-torsion-free-f-infinity-amenable-non-ea-group`.

## Attempts

- 2026-09-13 (lane z1-12-amen-nonea): deferred. It is recorded here to wire
  Zaremsky 1.12 to it. Degrijse's paper relates the question to the zero
  divisor conjecture; this lane has not read those results.
- 2026-09-17 (lane w3-112, inverter, family minimal-counterexample): attacked the dimension-2 step
  "`H_1(G; U(G)) = 0` for every fg amenable cd-2 `G`". Not resolved.
  - **Landed, forced structure of a counterexample.**
    `amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical`: a fg amenable cd-2 group with a
    nontrivial EA normal subgroup, or with a commensurated infinite cyclic subgroup, is `BS(1,m)`
    (Kropholler 1990 / Margolis splitting plus the amenable tree alternative). A two-dimensional
    counterexample is EA-radical-free. It has no commensurated `Z`, and every nontrivial normal
    subgroup is non-EA of cd 2.
  - **Dead, Σ¹ descent.** If a counterexample is an ascending HNN extension `K*_φ` with fg base,
    then `K` is again a counterexample. With `U(G)` coefficients, Mayer--Vietoris gives
    `H_1(G; U(G)) ≅ coker(1 − tφ_*)` on `U(G) ⊗_{U(K)} H_1(K; U(K))`, where `1 − tφ_*` is
    injective and the module has dimension 0. Nothing makes this cokernel vanish, and nothing
    makes the descent terminate. Worse, the splitting itself is not available. The dichotomy
    `Σ¹ ∪ −Σ¹ = S(G)` for groups without `F_2` goes through the Bieri--Strebel splitting, which
    needs finite presentability, and it fails for amenable fg non-fp groups (`Z≀Z`). A
    counterexample is not `FP_2`.
  - **Dead, dimension shift along a character.** Descent through `N = ker χ` using
    `hd N = hd G − 1` fails for fg non-FP_2 kernels: `SB_2 = ker(F_2×F_2 → Z)` has cd 2, equal
    to its ambient group. Any descent must use amenability at exactly this step.
  - **Følner / rank remark.** The truncated Jacobian ranks `rk J_k` increase to `d − 1`. In a
    counterexample they never attain it, so the `Z`-rank spectrum of `Z[G]` accumulates at an
    integer from below. This is a strictly weaker failure than the strong Atiyah conjecture, but
    no Følner argument gives a gap below an integer for general amenable groups (lamplighter rank
    spectra are dense), so this route needs a torsion-free-specific input.
  - **Next.** Rule out a counterexample with a nontrivial normal subgroup `N` of infinite index
    that is finitely generated (Bieri 1976 handles `FP` normal subgroups). Then combine with the
    EA-radical-free constraint to force a just-infinite-type counterexample.
- 2026-09-18 (lane w5-112, inverter, family cohomology-index): attacked "a finitely generated
  normal subgroup `N` of infinite index in a two-dimensional counterexample has cd 1, without
  assuming `FP_2`". Not resolved. The step is reduced to one precise case.
  - **Landed, exact vanishing.** `ascending-hnn-quotients-have-vanishing-affiliated-first-homology`
    covers any group `G = ⟨K, t⟩` with `K` finitely generated, `tKt⁻¹ ⊆ K`, and a character
    killing `K` that sends `t` to 1. For every such group, `H_1(G; U(G)) = 0` exactly, not merely
    in dimension 0, with no finiteness assumption on `G`.
    - The proof uses Lück's mapping-torus theorem in degree 2, not degree 1. On the finite
      mapping torus of the rose, the `d` HNN relators then span all 1-cycles over `U(G)`.
    - Consequence: `Σ¹(G) ≠ ∅` implies `H_1(G; U(G)) = 0`.
    - This refutes the w3-112 reading that "nothing makes" `coker(1 − tφ_*)` vanish: it always
      vanishes.
  - **Landed, consequences in dimension 2.** `amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar`:
    - An amenable cd-2 group with that structure is `BS(1,m)`.
    - In an amenable group of cd at most 2, a finitely generated `N` normal in `H` with `H/N ≅ Z`
      is `1` or `Z`.
    - A counterexample has `Σ¹ = ∅`, so the Σ¹ descent never starts. For every nontrivial finitely
      generated normal `N`, `G/N` is torsion. There is no infinite EA quotient by a finitely
      generated normal subgroup.
    - If `[G : N] = ∞`, then `N` is itself a counterexample.
  - **Precise obstruction.** The only open case is `G/N` an infinite finitely generated amenable
    torsion group, where `N` is again a counterexample. There `H_0(N; U) = 0`, and `H_1(G; U)` is a
    quotient of the `G/N`-coinvariants of `H_1(N; U)`. With a `Z` quotient the mapping torus kills
    them, but with a torsion quotient there is no `Z`-direction.
  - **Calibration, dimension 3.** `Z[1/6] ⋊ Z²` is metabelian of cd 3. It has a finitely generated
    normal subgroup `Z[1/6] ⋊_{2/3} Z` with quotient `Z` and cd 3, so there is no cd drop. The
    step is genuinely two-dimensional.
  - **Next.** Show that a finitely generated amenable group of cd 2 has no finitely generated
    normal subgroup with infinite torsion quotient. Alternatively, build a minimal counterexample
    along a chain `G ⊃ N ⊃ N' ⊃ …` of such subgroups and find a termination invariant.  No
    candidate invariant, for example a Fox-Jacobian rank deficit, is yet known to be monotone
    along such a chain.

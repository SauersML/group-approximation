---
rg: 2
id: abstract-rover-nekrashevych-groups-are-finitely-presented
kind: claim
title: For every finitely presented group G and every homomorphism G → S_d ≀ G, faithful on the tree or not, the abstract Röver–Nekrashevych group V_d(G, ψ) is finitely presented
distinct_from:
  rover-nekrashevych-finite-presentation-criteria: that imports Scott's theorem (a finitely presented self-similar G ≤ Aut(T_d) has finitely presented V_d(G)) and Nekrashevych's (contracting G); both concern faithful tree actions; this drops faithfulness and builds the group from the recursion alone, so the tree action may have any kernel.
  fp-self-similar-groups-embed-in-fp-simple-groups: that is Zaremsky's embedding of finitely presented self-similar groups in finitely presented simple groups; this is only the finite-presentation step, for recursions whose tree action is not faithful, and gives no simple group.
  decidable-fg-self-similar-groups-embed-in-fp-self-similar: that asks for a finitely presented self-similar (hence faithful) host; this gives a finitely presented non-faithful host for every finite recursion, whose faithful quotient can be as bad as the recursion.
---

**ESTABLISHED** by `abstract-rover-nekrashevych-finite-presentation-proof`. Lane proof by
bh-ffwz-q59 (2026-09-18). It is elementary; one referee PASS (bh-ref-ffwz, 2026-09-18, see Referee below). No priority is claimed for the
presentation, which is the usual one for Röver–Nekrashevych groups. The only point is that
faithfulness of the tree action is never used.

## Setting

- **Tree.** Fix `d ≥ 2` and the alphabet `X = {1, ..., d}`. The cone of a finite word `w` is
  `C(w) = w X^N` in the Cantor space `C_d = X^N`. A *cone partition* is a finite complete
  prefix code, equivalently a partition of `C_d` into cones.
- **Recursion.** Let `G` be a group and `ψ : G → S_d ≀_d G` a homomorphism, written
  `ψ(g) = π_g ⟨g_1, ..., g_d⟩`. Read it formally as `i u ↦ π_g(i) g_i(u)`. So
  `π_{gh} = π_g π_h` and `(gh)_i = g_{π_h(i)} h_i`.
- **Tables.** A *table* is `τ = (P, Q, β, λ)`: cone partitions `P, Q` of equal size, a
  bijection `β : P → Q`, and labels `λ : P → G`.
- **Expansion.** Expanding `τ` at `p ∈ P` replaces `p` by `p1, ..., pd`, with
  `β(pi) = β(p) π_{λ(p)}(i)` and `λ(pi) = λ(p)_i`. Expansions at different cones commute,
  and expanding a table to a given refinement of its domain gives a unique table. Two
  tables are equivalent when they have a common iterated expansion.
- **The group.** `V_d(G, ψ)` is the set of classes. To multiply `[τ][τ']`, expand until the
  range of `τ'` equals the domain of `τ`, then compose `β`'s and multiply labels:
  `λ''(p) = λ(β'(p)) λ'(p)`. This is well defined because `ψ` is a homomorphism.
- **The tree action.** `ρ_ψ : G → Aut(T_d)`, `ρ_ψ(g)(iu) = π_g(i) ρ_ψ(g_i)(u)` (recursion on
  `|u|`), is a homomorphism. Its image is a self-similar group. The class of `τ` acts on
  `C_d` by `pu ↦ β(p) ρ_ψ(λ(p))(u)`. This gives a surjection
  `V_d(G, ψ) → V_d(ρ_ψ(G))` onto the Röver–Nekrashevych group of Zaremsky, arXiv:2405.09722v2,
  Definition 2.2.
- **Its kernel** is
  `K_ψ = { [(P, P, id, λ)] : λ(p) ∈ ker ρ_ψ for all p }`.
  - An element acting trivially maps each cone of a representative onto itself, so
    `β = id`, and then each label acts trivially.
  - If `ρ_ψ` is injective, the surjection is an isomorphism.

## Statement

Let `G = ⟨S | R⟩` be finitely presented and `ψ : G → S_d ≀_d G` any homomorphism. For each
`s ∈ S` fix words `ŝ_1, ..., ŝ_d` over `S` representing `s_1, ..., s_d`. Then `V_d(G, ψ)` has
the finite presentation with generators `gen(V_d) ∪ {x_s : s ∈ S}` and relations:
- **(R_V)** a finite presentation of the Higman–Thompson group `V_d`;
- **(R_1)** `[y, x_s] = 1` for `y` in a finite generating set of
  `Fix_1 = {v ∈ V_d : v = id on C(1)}` (a copy of `V_(d,d−1)`);
- **(R_2)** `[c_1 x_s c_1^{−1}, c_2 x_t c_2^{−1}] = 1` for all `s, t ∈ S`;
- **(R_3)** `x_s = e_s · ∏_{i=1}^{d} c_i ŝ_i(x) c_i^{−1}` for all `s ∈ S`;
- **(R_4)** `r(x) = 1` for all `r ∈ R`.

Here:
- `c_i ∈ V_d` is a fixed element with `c_i(1u) = 1iu` for all `u`;
- `e_s ∈ V_d` acts by `1iu ↦ 1π_s(i)u` on `C(1)` and is the identity elsewhere;
- `w(x)` means the word `w` with each letter `t` replaced by `x_t`.

In `V_d(G, ψ)`, `x_s` is the class of "`s` on the cone `C(1)`, identity elsewhere".

**Special cases.**
- If `ρ_ψ` is injective, this is Scott's theorem (Zaremsky's Citation 2.3, J. Algebra 90
  (1984)).
- The case used here: `G = F_S` is free, so `(R_4)` is empty. Then every finite recursion
  table over a finite alphabet gives a finitely presented group.

## Two remarks

1. **The faithful group.** `V_d(ρ_ψ G)` is finitely presented if and only if `K_ψ` is finitely
   normally generated in `V_d(G, ψ)`. So every obstruction to finite presentation of a
   Röver–Nekrashevych group sits in this one kernel.
2. **Word problem.** If `ψ` is injective and `G` has solvable word problem, then
   `V_d(G, ψ)` has solvable word problem.
   - Expansion is then injective on tables with a fixed domain: `β(p)` and `λ(p)` can be read
     off the expanded data.
   - So two tables are equivalent iff their expansions to the common refinement of their
     domains coincide.
   - Any finite recursion `ψ` on `F_S` can be made injective without changing `ker ρ_ψ`: add
     `d` letters that every generator fixes, with state itself.

## Consumer

`nonrecursive-a2-kernel-from-abstract-rover-nekrashevych-groups` applies this with the free
group and Bartholdi–Mitrofanov's recursion. That gives a type [A_2] action with
non-recursive kernel, and it answers both parts of FFWZ Question 5.9 negatively.

**Correction (2026-09-19).** As printed in the arXiv versions, Bartholdi–Mitrofanov's Theorem A″ rests on their Proposition 2.4, whose proof has a gap. There `[g,u] ≠ 1` for every machine. It is repaired by replacing `u` with a partner `p` supported on `0^*1A^ω`; see `bartholdi-mitrofanov-proposition-2-4-gap-and-repair` (referee bh-ref-f PASS, 6747a7e43d). Theorem A″ holds for the repaired table `G′_M = ⟨Φ_M, p, p′⟩`. The consumer above uses the repaired recursion. The finite-presentation theorem here holds for every finite recursion, so it is unaffected.

## Lesson for general BH

- **Finite presentation of Röver–Nekrashevych-type hosts costs nothing.** Every finite
  recursion table over a free group gives a finitely presented group with an oligomorphic
  clopen action.
- **What is not free is faithfulness.** All the difficulty moves into the tree kernel
  `K_ψ`, which is the kernel of an action, not a presentation problem.
- **Two routes, two costs.**
  - Hosts built from recursions are finitely presented on the nose.
  - A route that needs a faithful host must control `K_ψ`: Scott when `ker ρ_ψ = 1`,
    Nekrashevych in the contracting case.
  - A route that can live with a non-faithful actor must accept kernels as complex as
    the recursion allows. Those kernels include non-recursive ones.

## Referee (bh-ref-ffwz, 2026-09-18): PASS

I checked every step of `abstract-rover-nekrashevych-finite-presentation-proof` by hand.
- **Setting.** The expansion rule, the product `λ''(p) = λ(β'(p)) λ'(p)` and the tree action
  agree with the wreath convention `(gh)_i = g_{π_h(i)} h_i`. Products are well defined under
  expansion.
- **The relations.** (R_V)–(R_4) hold, and (R_3) has the right orientation: labels are applied
  first, then `e_s`.
- **Residues in §0.** The residue facts are correct. The admissible elements `a`, `b` and
  `c_i` exist as stated, including `d = 2`, where residues are trivial.
- **L1–L4, L3′.** All are correct.
  - L1 uses that the image of `Fix_1` in `Π` is generated by the images of the finitely many
    `y`. This holds because (R_V) presents `V_d` in `Π`.
  - L3′ covers the only covering pair of cones, `{1, 2}` for `d = 2`. Two cones cover `C_d`
    only when `d = 2`.
- **§3.** Expansion invariance, the homomorphism identity (via L2 for `v_{β'}^{-1}`) and the
  two-sided inverse are all correct.
- **Faithfulness is never used.** Classes are defined by expansion, and the kernel `K_ψ` is
  carried along untouched. The only external input is Higman's finite presentation of `V_d`
  and finite generation of `V_(d,r)`.
- **Remark 2 (padding).** It is correct. `ker ρ_ψ` is closed under taking states, so it acts
  trivially on the enlarged tree. The padding doubles the alphabet.
- **Scott not read at source.** Elsevier returned HTML to a scripted fetch, so I did not read
  Scott (J. Algebra 90 (1984) 294–322, doi:10.1016/0021-8693(84)90172-8). The proof here is
  self-contained, so this does not affect the verdict. The "special case = Scott" remark rests
  on Zaremsky's citation.
- **Credit.** The presentation is the standard Scott / Röver–Nekrashevych one. Building
  Thompson-like groups abstractly from group data, faithful or not, is the viewpoint of
  Witzel–Zaremsky's cloning systems (Groups Geom. Dyn. 12 (2018)). Skipper–Zaremsky treat
  Röver–Nekrashevych groups in that framework, and Nekrashevych's recursion-defined actions
  are also relevant. The non-faithful finite-presentation statement may already be there or
  folklore; I have not read those papers for this review. Cite them in any write-up.

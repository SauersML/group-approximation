---
rg: 2
id: punctured-cone-covered-actors-are-locally-finite-by-leavitt
kind: claim
title: Cantor-module actors covered by punctured diagonal cone subgroups are locally finite by binary Leavitt units, so torsion-free decidable inputs of high complexity lie in none of them
distinct_from:
  diagonal-cone-covered-actors-lie-in-binary-leavitt-unit-group: that treats covering subgroups containing a diagonal cone subgroup built from clopen-rigid groups, which have no global fixed point, and lands every generator in the Leavitt unit group; this admits covering subgroups with finitely many fixed points, such as Stab_V(0^∞) ∩ Stab_V(1^∞), which that scope section leaves open, where the commutant is strictly larger than the Leavitt algebra and the covered group only maps onto a Leavitt subgroup with locally finite kernel.
  decidable-groups-embed-in-covered-cantor-module-actors: that asks every decidable input to lie in some finitely presented covered group; this shows that covering subgroups containing a tame diagonal cone subgroup can never supply a torsion-free input of high word-problem complexity.
  complexity-bounded-host-classes-are-not-universal: that is the general principle for host classes with one recursive bound; the hosts here have no shared bound (the fixed points may be arbitrarily complex), and the principle is applied only after dividing out a locally finite kernel and using that the graph-shift inputs are torsion-free.
---

**ESTABLISHED** by `punctured-cone-covered-actors-evaluation-ideal-proof` (elementary; not
independently reviewed; no novelty claimed).

## Setting

Notation of `diagonal-cone-covered-actors-lie-in-binary-leavitt-unit-group`:
- `R = L_(F_2)(1,2)` with generators `s_0, s_1, t_0, t_1`, acting on `M = C(C, F_2)` through
  `Φ : R -> End(M)`;
- `U = R^×`, containing Thompson's `V` as the units `Σ s_(a_i) t_(b_i)`.

For a point `y ∈ C` write `δ_y` for evaluation at `y`. For `g ∈ M` write `δ_y ⊗ g` for the
rank-one map `f ↦ f(y) g`, and put `E_y = δ_y ⊗ 1`. Let

    J_0 = span{ δ_y ⊗ g : y ∈ C, g ∈ M } ⊆ End(M),     B = Φ(R) + J_0.

For a finite set `P ⊂ C` let `V^(P)` be the subgroup of elements of `V` that are the identity
on some clopen neighbourhood of `P`. So `V^(∅) = V`.

**Tame subgroups.** Call `H <= V` *tame* if for some finite `P ⊂ C`:
- **(T1)** `M^H = F_2·1`;
- **(T2)** `span{ h f - f : h ∈ H, f ∈ M } ⊇ ker(ev_P) = { f : f|_P = 0 }`;
- **(T3)** every additive `T : M -> M` commuting with `H` lies in `F_2·id + span{E_p : p ∈ P}`.

Any subgroup of `V` containing a tame subgroup is tame, with the same `P`. Clopen-rigid
subgroups are tame with `P = ∅`, and every `V^(P)` is tame with that `P`.

A **tame diagonal cone subgroup** is a subgroup built as in the diagonal-cone claim, or its
conjugate by an element of `V`. Take a complete prefix code
`α_1, ..., α_k, β_1, ..., β_m` with `k >= 1`, `m >= 0`, where the one-word code consisting of
the empty word is allowed. Take a complete prefix code `γ_1, ..., γ_m`, with `S_β, T_β` as
there, and tame `H, K <= V`. Then

    D = { Σ_i s_(α_i) h t_(α_i) + S_β k T_β : h ∈ H, k ∈ K }.

With the empty code and `m = 0` this is `D = H`. For example
`Stab_V(0^∞) ∩ Stab_V(1^∞) ⊇ V^({0^∞, 1^∞})` is such a subgroup.

## Statement

1. **Commutant.** Every additive `T : M -> M` commuting with a tame diagonal cone subgroup
   lies in `B`. Explicitly, for the unconjugated `D`,
   `T = Σ λ_(ij) s_(α_i) t_(α_j) + μ Σ_l s_(β_l) t_(β_l) + j` with `λ ∈ M_k(F_2)`,
   `μ ∈ F_2` and `j ∈ J_0`, where `j` is a sum of the maps
   `s_(α_i) E_p t_(α_j)`, `s_(α_i) E_q T_β`, `S_β E_p t_(α_j)` and `S_β E_q T_β`, for `p` in
   the puncture set of `H` and `q` in that of `K`.
2. **Algebra.** `B` is a unital subalgebra of `End(M)`, `J_0` is a two-sided ideal of `B`,
   and `B = Φ(R) ⊕ J_0`. So `π : B -> R`, `Φ(a) + j ↦ a`, is a ring homomorphism.
3. **Covered groups.** Let `W = <V, x_1, ..., x_r> <= Aut(M)`, where each `x_j` commutes with
   a subgroup `C_j <= V` containing a tame diagonal cone subgroup. Covering is not needed.
   - `π` restricts to a homomorphism `W -> U` whose image is a finitely generated subgroup of
     `U`.
   - Its kernel `W ∩ (1 + J_0)` is locally finite.
   - Hence every subgroup of `W` with no nontrivial locally finite normal subgroup, in
     particular every torsion-free subgroup, embeds in `U`.
4. **Not universal.** There is a two-generated torsion-free group with solvable word problem,
   namely a graph-shift group `G_A`, that embeds in no such `W`.
   - So `decidable-groups-embed-in-covered-cantor-module-actors` cannot be proved using
     covering subgroups that contain a tame diagonal cone subgroup.
   - This holds even though these `W` share no recursive word-problem bound: the punctures
     may be arbitrary computable points.
5. **Fixed points of covering subgroups.** If finitely many `C`-translates of
   `m_1, ..., m_n` span `M`, then `C` has at most `n` global fixed points. So finite puncture
   sets are the only singular data a covering subgroup can carry globally.

## What this leaves

Any covered generator outside `B` needs a covering subgroup containing no tame diagonal cone
subgroup. Two known kinds of such subgroups remain.

- **Twisted diagonals.** Take a homeomorphism `σ` normalising `V` but not in `V`, such as the
  bit flip, and the subgroup `{ s_0 h t_0 + s_1 σ h σ^(-1) t_1 : h ∈ V }`.
  - It covers `M`, since its translates of `χ_[00]` and `χ_[10]` already span.
  - It commutes with the involution `x : 0y ↦ 1σ(y), 1y ↦ 0σ^(-1)(y)`.
  - For the bit flip, `x` is not in `B`. This is proved in the section *Twisted diagonals* of
    the proof, using the equivariance trick of item 3 together with a window-counting argument
    for `Φ(R)`.

  So `B` is not the commutant algebra for every covering subgroup.
- **Covering subgroups that are not locally moving in the sense of (T1)–(T3)**, such as
  Thompson's `F`.

The next prerequisite for any proof of the covered-actor claim is therefore a
covering subgroup of one of these kinds, with a covered, finitely presented `W` of
unbounded word-problem complexity. For twisted diagonals over `Aut(V)` the expected
obstruction is a uniform exponential bound for groups of operators generated by `Φ(U)`,
rational homeomorphisms and `J_0`. That bound is not proved here.

DERIVATION
punctured-cone-covered-actors-evaluation-ideal-proof

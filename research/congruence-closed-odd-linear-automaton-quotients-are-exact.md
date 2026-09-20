---
rg: 2
id: congruence-closed-odd-linear-automaton-quotients-are-exact
kind: claim
title: Conditionally on strong approximation and the normal-subgroup structure of SL_2 over local fields, every quotient of a finitely generated Zariski-dense subgroup of SL_2(F_q[t^±1]) (q odd, q ≥ 5) by a normal subgroup closed in the congruence topology is exact; since the periodic topology of matrix-linear automata is that congruence topology, one-sided T2 with odd-characteristic linear lifts lifts only exact groups, and Q_lin stays open only in characteristic 2
requires:
  - one-sided-t2-lift-groups-are-periodically-closed-quotients
  - two-sided-locality-holds-for-matrix-linear-automata
distinct_from:
  one-sided-t2-lift-groups-are-periodically-closed-quotients: that poses Q_lin and shows the regular exactness argument fails for sections; this answers the odd-characteristic analogue of Q_lin negatively, conditionally, by a different argument through strong approximation and normal subgroups of SL_2 over local rings.
  pointer-encodings-give-non-linear-two-sided-locality: its item 4 proves exactness of lifts commuting with linear regular transports, via subgroups of bounded-degree linear groups; this handles quotients by congruence-closed normal subgroups, where only sections are available.
---

**CONDITIONAL** (lane bh-ra-t2, 2026-09-19; lane proof, not reviewed; no priority claimed). It holds
under three recalled inputs, none verified at source here:
- **(SA) Strong approximation, over the minimal quasi-model** (repaired per bh-ref-d, 0fe7e96aa4).
  - *The first statement was false.* It asked the closure of `F` in `SL_2(Â)` to contain an open product
    over the places of `F_q(t)`. That fails when the trace field is smaller: a Zariski-dense
    `F ≤ SL_2(F_q[s^(±1)])` with `s = t²` has non-open closure at the places of `F_q(t)`.
  - *The correct input* is Pink, "Strong approximation for Zariski dense subgroups over arbitrary global
    fields", Comment. Math. Helv. 75 (2000), 608–643, recalled. Relative to the **minimal quasi-model** of
    `F` (its trace field `E ⊆ F_q(t)`, with `F_q(t)/E` finite since `F` is infinite, a form of the
    adjoint group over `E`, and the isogeny, possibly with a Frobenius twist, carrying `F` into its
    `E`-points), the closure of the image of `F` over the adèles of `E` away from the places below
    `{0, ∞}` is open.
  - *How the proof is run* (bh-ref-d's repair (2)). Run Steps 0–6 over the trace ring `A_0` and its places,
    not over `A` and its places. Put into `T` the finitely many places where the quasi-model is non-split,
    or where the closure is not the full local group. `U_v` is then the full local group, of `SL_2` type,
    for `v ∉ T`.
  - *Topologies* (bh-ref-d's repair (3)). The `A`- and `A_0`-congruence topologies on `F` agree, because
    `A` is faithfully flat over `A_0`, so `J′A ∩ A_0 = J′` for ideals `J′` of `A_0`. So "closed in the
    congruence topology" means the same over either ring.
  - This repair is recorded but not yet independently re-checked in the quasi-model form. The Statement is
    to be read with `A`, `Â` and the places `v` replaced by `A_0`, `Â_0` and its places, and with
    `SL_2(O_v)` replaced by the local groups of the quasi-model.
- **(HJI) Just-infiniteness.** For every `v` and every open `U ≤ SL_2(O_v)`, every closed normal subgroup of
  `U` not contained in `{±1}` is open. This is recalled for odd residue characteristic.
- **(S) Sandwich.** For `v ∉ T` and every `k`, every normal subgroup of `SL_2(O_v/m_v^k)` has the form
  `SL_2(O_v/m_v^k, m_v^j/m_v^k) · Z_0`, with `Z_0 ≤ {±1}`. This is recalled for residue fields with at least
  5 elements in odd characteristic. It fails for `F_3`, where `SL_2(F_3)` has the normal subgroup `Q_8`,
  hence `q ≥ 5`. (bh-ref-d notes that places with residue field `F_3` are finite in number and could go
  into `T`, so `q ≥ 5` may be droppable. This is unchecked.)
- **Status of the inputs.** bh-ref-d is checking (HJI) and (S) at source. Until that check reports, this
  node stays CONDITIONAL.

**T2 is not built.** This closes one door conditionally; it opens none.

## Statement

Let `q` be a power of an odd prime with `q ≥ 5`, and put `A = F_q[t^(±1)]`. Let `F ≤ SL_2(A)` be finitely
generated and Zariski dense; any non-abelian free subgroup is. Assume (SA), (HJI) and (S).

1. **Exactness.** For every normal subgroup `N ⊴ F` closed in the congruence topology (induced from
   `SL_2(Â)`), the group `F/N` is exact.
2. **Periodic equals congruence.** For the matrix-linear automata of
   `two-sided-locality-holds-for-matrix-linear-automata`, over the alphabet `M_2(F_q)`, the periodic
   topology is exactly this congruence topology.
3. **Consequence.** In the one-sided setting of
   `one-sided-t2-lift-groups-are-periodically-closed-quotients`, lifts that are matrix-linear automata over
   `M_2(F_q)` (`q` odd, `q ≥ 5`) lift only exact groups. `GL_2` reduces to `SL_2` by the extension argument in
   the proof.

   So one-sided T2 with such linear lifts is dead, conditionally. The linear route survives only in
   characteristic 2, where (HJI) and (S) are unknown to us or fail at the small residue fields `F_2`
   (at `t = 1`) and `F_4`. Otherwise it needs non-linear lifts (Q_per).

## Proof

**2.** For `f ∈ F_q[t]` with `f(0) ≠ 0`, `t` has finite order `ℓ` in `(F_q[t]/(f))^×`, so `f | t^ℓ − 1`. The
ideals `(t^ℓ − 1)` are therefore cofinal among the nonzero ideals of `A`. On period-`ℓ` data the automata act
faithfully through `GL_2(A/(t^ℓ − 1))`, so `P_ℓ = F ∩ ker(GL_2(A) → GL_2(A/(t^ℓ − 1)))`.

**1.**
- **Step 0 (closure).** Let `N̄` be the closure of `N` in `SL_2(Â)`. It is normal in `F̄`, and
  `F ∩ N̄ = N` because `N` is closed. So `F/N ↪ F̄/N̄`.
  - Replace each `U_v` by its normal core in `π_v(F̄)`. This is still open, and `∏_v U_v ≤ F̄` still holds.
  - View `U_v` as the `v`-coordinate subgroup of `F̄`.
- **Step 1 (places where `N̄` is large).** Let `S_1 = {v : π_v(N̄) ⊄ {±1}}`. Fix `v ∈ S_1` and
  `x ∈ N̄` with `x_v ∉ {±1}`.
  - `U_v` is open, hence Zariski dense. The set of `y` with `[x_v, y] ∈ {±1}` is a proper Zariski-closed
    subset of `SL_2`, so some `y ∈ U_v` has `[x_v, y] ∉ {±1}`.
  - Then `[x, y_v]` is supported at `v` and lies in `K_v := N̄ ∩ U_v`. So `K_v` is a closed normal subgroup
    of `U_v` not contained in `{±1}`, and it is open by (HJI).
  - Choose `k_v` with `SL_2(O_v, m_v^(k_v)) ≤ K_v`. Since `N̄` is closed, it contains the full product
    `∏_(v ∈ S_1) K_v`.
- **Step 2 (a linear model).** Put `B = ∏_(v ∈ S_1) O_v/m_v^(k_v) × ∏_(v ∉ S_1) O_v`, a commutative ring, and
  let `ψ: SL_2(Â) → SL_2(B)` be reduction.
  - `ker ψ = ∏_(v ∈ S_1) SL_2(O_v, m_v^(k_v)) ≤ ∏ K_v ≤ N̄`.
  - Put `H = ψ(F̄)` and `M = ψ(N̄)`, which is closed and normal in `H`.
  - If `ψ(f) ∈ M` with `f ∈ F`, then `f ∈ N̄ · ker ψ = N̄`, so `f ∈ N`. Hence `F/N ↪ H/M`.
- **Step 3 (coordinate intersections).** Let `H_v = ψ(U_v)`, the `v`-coordinate subgroup of `H`,
  `L_v = M ∩ H_v`, and `L = ∏_v L_v ≤ M`.
  - For `v ∉ S_1`, `L_v ≤ {±1}`.
  - For `v ∈ S_1 ∖ T`, `H_v = SL_2(O_v/m_v^(k_v))`, so by (S), `L_v = SL_2(O_v/m^(k_v), m^(j_v)/m^(k_v)) · Z_v`.
  - The places `v ∈ S_1 ∩ T` are finitely many, and there `H_v` is finite.
- **Step 4 (`M/L` is virtually central).** For `m ∈ M` and `h ∈ H_v`, the commutator `[m, h]` is supported at
  `v` and lies in `π_v`-conjugates of `U_v`, which equal `U_v` by normality. So `[m, h] ∈ M ∩ H_v = L_v`.
  - Hence `M/L` centralizes `H_0 L/L`, where `H_0 = ∏_v H_v` has finite index in `H`.
  - So `M/L` is abelian-by-finite, hence amenable.
- **Step 5 (`H/L` is abelian-by-linear).**
  - `L ≤ H` and `H ∩ ∏_v L_v = L`, so `H/L ↪ ∏_v SL_2(B_v)/L_v`.
  - For `v ∈ S_1 ∖ T` the factor is `SL_2(O_v/m^(j_v)) / Z′_v`. For `v ∉ S_1` it is `SL_2(O_v)/L_v`. In both
    cases conjugation on `M_2(·)` maps it to `GL_4` of a commutative local ring, with abelian kernel
    (scalars modulo `Z′_v`).
  - The finitely many factors at `S_1 ∩ T` form a finite group `Φ`.
  - So the image `Δ` of `F` in `H/L` maps to `Φ × GL_4(C)`, with `C` commutative, and its kernel is contained
    in a product of abelian groups.
  - The image of `Δ` in `GL_4(C)` is finitely generated. Its matrix entries generate a finitely generated,
    hence Noetherian, subring `C_0`, with nilpotent nilradical. `C_0/nil` embeds in a finite product of
    fields.
  - So that image is nilpotent-by-linear over fields, hence exact (Guentner–Higson–Weinberger, and extensions
    by amenable groups). Hence `Δ` is abelian-by-(finite × exact), which is exact.
- **Step 6 (quotient).** `F/N` is the image of `Δ` in `H/M`, that is `Δ/(Δ ∩ M/L)`, and `Δ ∩ M/L` is an
  amenable normal subgroup by Step 4.
  - For amenable `A ⊴ Δ`, the quasi-regular representation on `ℓ²(Δ/A)` is weakly contained in `λ_Δ`. So
    `C*_λ(Δ/A)` is a quotient of `C*_λ(Δ)`.
  - Quotients of exact C*-algebras are exact (Kirchberg), so `F/N` is exact.

**3 (`GL_2`).**
- For `F ≤ GL_2(A)`, the subgroup `F_1 = F ∩ SL_2(A)` is normal with abelian quotient, so `F/N` is exact iff
  `F_1/(N ∩ F_1)` is.
- A countable group is exact iff its finitely generated subgroups are. Each finitely generated subgroup of
  `F_1/(N ∩ F_1)` is `E/(E ∩ N)` for some finitely generated `E ≤ F_1`.
- Enlarge `E` by two generators of a free subgroup of `[F, F]`, so that it is Zariski dense. Then `E ∩ N` is
  congruence-closed in `E`, and item 1 applies. ∎

## Lesson for general BH

**Linear lifts are exact even through quotients, once the transports are only verified.**
- In odd characteristic, strong approximation plus the rigidity of normal subgroups of `SL_2` over local
  rings forces every congruence-closed quotient of a linear automaton group to be abelian-by-linear modulo an
  amenable subgroup, hence exact.
- So the section loophole of `one-sided-t2-lift-groups-are-periodically-closed-quotients` closes in odd
  characteristic, conditionally.
- What is left for T2 is characteristic 2, where small residue fields have wild pro-2 normal subgroups, or
  non-linear lifts, via Q_per and kernel realization.

---
rg: 2
id: deligne-forms-are-singular-on-commuting-parabolic-diagonals
kind: claim
title: On the Deligne normal-form boundary of a finite-type Artin group with an edge and a node commuting with it, such as B_n for n >= 5, every positive power of an Artin generator has a Cantor set of singular points, so the germ-extension route cannot run on that structure or on its central quotients
distinct_from:
  rational-germ-singular-sets-are-finite-graph-path-spaces: that proves the finite-or-Cantor dichotomy for any rational action; this exhibits the Cantor side for one explicit family, the Garside structures, by a lockstep computation.
  artin-normal-form-boundary-full-groups-fix-a-point: that finds the global fixed point Delta^{-infinity} of the same boundary action; this finds an uncountable singular set of one generator, which is a different and stronger obstruction to finite germ extensions.
  artin-groups-mod-central-garside-power-are-continuous-automatic: that proves continuity of the quotient language; this shows the resulting boundary action is not thin, so continuity does not feed the Belk--Hyde--Matucci theorem through that structure.
  low-complexity-mapping-class-groups-are-continuous-automatic: that gets continuous automatic structures on punctured-sphere and genus-two mapping class groups from the Garside quotient; this shows those Garside structures fail the thinness test (E1').
artifacts:
  - research/artifacts/gq-bh-bh-free-51-garside-and-mosher-thinness.md
---

**ESTABLISHED** by `deligne-commuting-parabolic-diagonal-singularity-proof` (lane proof,
elementary apart from standard Garside facts recalled there; not independently reviewed; no
priority claimed).

## Setting

- `A` is an Artin group of finite type with Artin generators `S`, positive monoid `A^+`,
  Garside element `Δ` and simple elements `[1, Δ]`.
- For a simple `x`, `S(x)` is the set of atoms left-dividing `x` and `F(x)` the set of atoms
  right-dividing it. For simples `x, y`, `x → y` (Belk--Bleak--Chatterji--Matucci--Perego
  (BBCMP) §2.3: `pref(xy) = x`) holds if and only if `S(y) ⊆ F(x)`.
- `L` is one of:
  - the Deligne normal form of BBCMP §2.3 (read at source, p. 11), words
    `Δ^{-j} x_1 ⋯ x_n` with `x_1 → ⋯ → x_n`;
  - the quotient language `L̄` of `artin-groups-mod-central-garside-power-are-continuous-automatic`,
    words `Δ^p x_1 ⋯ x_n` with `0 ≤ p < c`.
  
  Either way `A` (resp. `A/⟨Δ^c⟩`) acts continuously on `∂L`: BBCMP Theorem 2.4, resp.
  that node.
- **Hypothesis (H).** There are `s, t, u ∈ S` with `m_{st} ≥ 3` and `m_{su} = m_{tu} = 2`.
  - (H) holds for types `A_n` with `n ≥ 4`, that is, braid groups `B_{n+1}` with
    `n + 1 ≥ 5` (take `s = σ_1, t = σ_2, u = σ_4`).
  - Among the other irreducible types it holds for Coxeter types `B_n` with `n ≥ 4`, `D_n` with
    `n ≥ 5`, `E_6, E_7, E_8`, `F_4` and `H_4`. It also holds for any reducible type with a
    factor of rank at least 2 and another factor.
  - It fails for types `A_1, A_2, A_3`, `B_3`, `D_4`, `H_3` and the dihedral types.

## Statement

Assume (H). For an infinite sequence `x = x_1 x_2 ⋯` of proper simples of the parabolic
`A_{s,t}` with `x_1 → x_2 → ⋯` and `S(x_1) = {s}`, put

    ξ_x = (x_1 u)(x_2 u)(x_3 u) ⋯ .

1. **Lockstep.** For `p ∈ A_{s,t}^+` with normal form `x_1 ⋯ x_n` and `m ≤ n`, the normal
   form of `p u^m` is `(x_1 u) ⋯ (x_m u) x_{m+1} ⋯ x_n`. Each `ξ_x` lies in `∂L`.
2. **Phase shift.** For `N ≥ 1`, `s^N ξ_x = (su)^N (x_1 u)(x_2 u) ⋯`. That is, `s^N` shifts
   the `A_{s,t}`-column by `N` steps relative to the `u`-column.
3. **Singular points.** If `x` is not eventually periodic, then `s^N` is singular at `ξ_x`:
   - over the boundary Thompson group `B` of `L`;
   - and over Thompson's `V`, after any recoding of the path space by complete binary prefix
     codes as in `prefix-replacement-actions-recode-into-germ-extensions-of-v`.
4. **Cantor set.** Hence `sing(s^N)`, over `B` and over `V`, contains the Cantor set
   `{ξ_x : S(x_1) = {s}}`.

## Consequences

- **The Garside structures fail (E1').** This covers the BBCMP structures of Theorem 1.11 for
  the braid groups `B_n` (`n ≥ 5`) and the other types listed. It also covers `L̄` on `B_n/Z(B_n)` (`n ≥ 5`).
  - For these, the topological full group is not a finite germ extension of `B` or of `V` in
    the Belk--Hyde--Matucci sense, so `automatic-groups-embed-in-corner-germ-extensions`
    cannot be met through them.
  - The singular set is uncountable, so by
    `rational-germ-singular-sets-are-finite-graph-path-spaces` no change of finitely many
    prefixes repairs it.
- **Finite-index subgroups.** Item 3 holds for every power `s^N`. So the failure persists for
  any finite-index subgroup acting on the same boundary. The coset constructions that pass
  a structure to a finite-index subgroup or a finite extension keep a copy of `∂L` on which
  the subgroup acts as before.
- **Mapping class groups.**
  - `L̄` on `B_5/Z(B_5)` is the finite-index piece of `Mod(S_{0,6})`, and hence through
    Birman--Hilden of `Mod(S_2)`, used by `low-complexity-mapping-class-groups-are-continuous-automatic`.
  - Geometrically, in `S_2`:
    - `⟨σ_1, σ_2⟩` lifts to `Mod` of a one-holed torus `T`;
    - `σ_4` lifts to a Dehn twist about a curve disjoint from `T`;
    - the Garside structure processes these two commuting pieces in lockstep, and the
      relative phase shift is the singularity.
  - The same holds for `S_{0,n}` with `n ≥ 6`.
  - Boone--Higman is already known for all these groups
    (`punctured-surface-mcgs-satisfy-permutational-boone-higman`). The point is that this
    structure cannot be the one that reaches closed genus `≥ 3`.

## Scope

- Nothing here is claimed for `B_3` or `B_4`. For `B_3` see
  `b3-center-first-normal-form-passes-the-germ-condition`: there the Garside
  structure is thin, but the germ condition fails until the center is written first.
- The obstruction is to these specific structures. It says nothing about other continuous
  automatic structures on the same groups.

## Lesson for general BH

- **It is a phase, not an accident.** A normal form that reads two commuting subgroups in
  lockstep makes each generator of one factor shift that factor's column against the other.
- **What a rank-one host can absorb.** A germ extension of `V` absorbs such a relative shift
  only at eventually periodic points. So a rank-one coding hosts a product region only when
  one factor contributes finitely many periodic directions:
  - `Z`, giving corners as for `Z^2 * Z`;
  - or a central `Z` written first, as in
    `b3-center-first-normal-form-passes-the-germ-condition`. That is the virtually central
    cyclic germ that `bhm-corollary-hosts-over-v-are-cover-centralizer-groups` (b) shows every
    certified singular point must have.
- **What a product needs.** A product of two non-elementary groups, such as
  `F_2 × F_2 ≤ Mod(S_g)` for `g ≥ 2`, needs a host of rank at least two, such as the
  cube categories of `cubulated-groups-act-by-bisections-of-a-pointed-cube-category`.
- **What this changes.** For closed mapping class groups the task is to build a higher-rank
  host, not a better rank-one normal form.

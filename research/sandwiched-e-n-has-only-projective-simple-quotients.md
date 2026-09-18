---
rg: 2
id: sandwiched-e-n-has-only-projective-simple-quotients
kind: claim
title: When normal subgroups of E_N(R) are sandwiched, every nonabelian simple quotient of E_N(R) is PE_N(R/I), so the rational-scalar obstruction covers all simple quotients of finite-stable-rank hosts
distinct_from:
  full-corner-copies-of-q-force-central-rational-scalars: that moves Q from a full corner into the centre of R and records the gap "simple quotients of E_N(R) not of the form PE_N(R/I)"; this closes that gap whenever the sandwich property holds, in particular for rings of finite stable rank.
  aperiodic-subshift-el-normal-subgroups-are-sandwiched: that proves the sandwich property for one family of crossed-product rings over F_2; this is the general consequence of the sandwich property for simple quotients, used for hosts containing Q.
  rational-scalars-obstruct-fp-elementary-hosts: that bounds PE_N(R) for R containing Q; this shows that under the sandwich property no other simple quotient of E_N(R) exists, so that bound is the whole story.
---

**ESTABLISHED** for parts 1–2 (lane proof, elementary, inline; not reviewed; no novelty
claimed). Part 3 imports Bass's normal subgroup theorem **as recalled, not read at source**;
its exact rank bound should be checked before the consequence for stably finite hosts is
used.

## Statement

Let `R` be a nonzero unital ring and `N >= 3`. For a subgroup `H <= GL_N(R)` normalized
by `E_N(R)`, let `I_H = {r ∈ R : x_12(r) ∈ H}` (its level), and let
`C_N(R, I) = {g ∈ GL_N(R) : g mod I is central in GL_N(R/I)}`. Say `(R, N)` has the
**sandwich property (SW_N)** if `H <= C_N(R, I_H)` for every such `H`.

1. **Levels.** `I_H` is a two-sided ideal, `x_ij(I_H) ⊆ H` for all `i ≠ j`, and
   `E_N(R, I_H) <= H`.
2. **Simple quotients.** Assume SW_N. Let `S = E_N(R)/H` be a nonabelian simple group.
   Then `I = I_H` is a proper ideal and
   `S ≅ PE_N(R/I) = E_N(R/I)/Z(E_N(R/I))`.
   If moreover `R` contains `Q` unitally (for instance through a full corner, by
   `full-corner-copies-of-q-force-central-rational-scalars`), then so does `R/I`,
   centrally, and `rational-scalars-obstruct-fp-elementary-hosts` applies to `R/I`: if
   `S` is finitely presented then `Λ_N(R/I)` is finitely generated. Likewise
   `full-corners-must-kill-rational-k2-symbols` applies to `R/I`.
3. **Finite stable rank (import).** Bass's normal subgroup theorem gives SW_N whenever
   `N >= max(3, sr(R) + 1)` (H. Bass, *K-theory and stable algebra*, Publ. IHES 22
   (1964); recalled, not read; the bound may be `sr(R) + 2` in the original). So for a
   host of finite stable rank, and all large `N`, every nonabelian simple quotient of
   `E_N(R)` is some `PE_N(R/I)`, and the rational-scalar and full-corner budgets govern
   every candidate host built from `E_N(R)`.

## Where the loophole now lives

- **Stably finite designs.** `stably-finite-fp-simple-ring-containing-q-exists` (critic
  U1) targets finite-stable-rank hosts. By part 3, exotic simple quotients of `E_N` give
  such designs nothing: only `PE_N` of a quotient ring can be the host.
- **Non-stably-finite designs.** Every frame and vacuum design of
  `fp-simple-resolvent-ring-with-divisible-unit-class` is not stably finite, hence of
  infinite stable rank (gate Attempt 12, aed2f810c). Bass's theorem is then unavailable,
  and the gap recorded in `full-corner-copies-of-q-force-central-rational-scalars` is
  exactly: *a simple ring `R ⊇ Q` of infinite stable rank and `N >= 3` for which some
  non-central normal subgroup of `E_N(R)` contains no nontrivial elementary matrix* (for
  simple `R`, SW_N is equivalent to simplicity of `PE_N(R)`). Examples on main where SW_N
  does hold at infinite stable rank: `binary-leavitt-elementary-group-is-simple`,
  `aperiodic-subshift-el-normal-subgroups-are-sandwiched`.

## Proof

*Part 1.* Commutator relations give `[x_ik(r), x_kj(1)] = x_ij(r)` for distinct `i,k,j`
(`N >= 3`), and `H` is normalized by `E_N(R)`. From `x_12(r) ∈ H`:
`x_13(r) = [x_12(r), x_23(1)]` and `x_32(r) = [x_31(1), x_12(r)]` lie in `H`; iterating,
every `x_ij(r) ∈ H`. The set of `r` with `x_ij(r) ∈ H` is an additive subgroup, the same
for all `i ≠ j` by the above, and closed under `r ↦ ar` and `r ↦ rb` via
`[x_ik(a), x_kj(r)] = x_ij(ar)` and `[x_ik(r), x_kj(b)] = x_ij(rb)`. So `I_H` is a two-sided
ideal. `E_N(R, I_H)` is by definition the normal closure in `E_N(R)` of the `x_ij(I_H)`,
hence lies in `H`.

*Part 2.* `H ≠ E_N(R)` since `S ≠ 1`, so `x_12(1) ∉ H` and `I ≠ R`. Let
`ρ: E_N(R) -> E_N(R/I)` be reduction; it is onto because it maps generators onto
generators. Put `K = ρ^(-1)(Z(GL_N(R/I)))`. By SW_N, `H <= C_N(R,I) ∩ E_N(R) = K`.

`K ≠ E_N(R)`: otherwise `E_N(R/I)` would be central in `GL_N(R/I)`, hence abelian; but
`E_N(R/I)` is perfect for `N >= 3` and nontrivial since `R/I ≠ 0` (`x_12(1) ≠ 1`), and a
perfect abelian group is trivial. So `K/H` is a proper normal subgroup of the simple group
`S`, hence trivial, and `H = K`. Therefore

    S = E_N(R)/K ≅ E_N(R/I) / (E_N(R/I) ∩ Z(GL_N(R/I))).

For `N >= 3` and any ring `R'`, a matrix commuting with every `x_ij(r)` is `cI` with
`c ∈ Z(R')`; so `Z(E_N(R')) = E_N(R') ∩ {cI : c ∈ Z(R')^x} = E_N(R') ∩ Z(GL_N(R'))`, and
`S ≅ PE_N(R/I)`.

If `Q ⊆ R` unitally, then `Q ∩ I = 0` (a nonzero rational in `I` would put `1 ∈ I`), so
`Q -> R/I` is a unital injection, which is exactly the hypothesis of
`rational-scalars-obstruct-fp-elementary-hosts` and of
`full-corners-must-kill-rational-k2-symbols` (the latter needs `E_N(R/I)` finitely
presented, which follows from finite presentation of `PE_N(R/I)`, as that node notes).
The remaining sentences are those two nodes applied to `R/I`.

*Part 3.* This is the cited theorem; nothing is proved here.

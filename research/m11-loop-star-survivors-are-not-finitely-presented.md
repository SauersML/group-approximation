---
rg: 2
id: m11-loop-star-survivors-are-not-finitely-presented
kind: claim
title: The loops of the chain (a,a,e) survivor generate G, so the loop-star obstruction genuinely fails there, but a linear descent theorem for unit-weight polynomial recursions shows H_1 = Z^3; every one of the 1373 loop-star survivors has b_1 >= 1, so none is finitely presented, and neither is its Tits host
artifacts:
  - experiments/loop-subgroup-membership-2026-09-19/descent.py
  - experiments/loop-subgroup-membership-2026-09-19/classify.py
  - experiments/loop-subgroup-membership-2026-09-19/classify.out
  - experiments/loop-subgroup-membership-2026-09-19/sanity.py
  - experiments/loop-subgroup-membership-2026-09-19/sanity.out
  - experiments/loop-subgroup-membership-2026-09-19/stab.py
  - experiments/loop-subgroup-membership-2026-09-19/loops_generate.py
  - experiments/loop-subgroup-membership-2026-09-19/loops_generate.out
  - experiments/loop-subgroup-membership-2026-09-19/lat1.py
  - experiments/loop-subgroup-membership-2026-09-19/lat1.out
distinct_from:
  unit-weight-polynomial-recursions-split-over-loop-edges: that kills recursions by a tree-of-factors splitting and leaves 1373 survivors whose loop leaf might map onto G; this proves that the leaf does map onto G for the first survivor (so no splitting argument can work there) and kills all survivors by homology instead.
  m11-linear-activity-group-b1-two-not-finitely-presented: that descends two exponent sums of one specific linear-activity group by an ad hoc stable-word analysis; this is a general linear descent certificate for any unit-weight polynomial recursion under (T_p), run by exact linear algebra over whole families.
  fully-self-replicating-fp2-groups-have-odd-cyclic-h1: that says b_1 >= 1 forbids FP_2; this supplies b_1 >= 1 for the survivors, which is the part that needs proof.
---

**ESTABLISHED (unreviewed).** Proof: `m11-loop-star-survivors-are-not-finitely-presented-proof`.
- Items 1 (the reduction steps) and 3 are proved by hand.
- Item 1 uses two exact finite computations (`loops_generate.py`, `lat1.py`).
- Items 2 and 4 apply item 3 by exact rational linear algebra (`descent.py`, `classify.py`).

Notation follows `unit-weight-polynomial-recursions-split-over-loop-edges`: `P = M_11` on
`X = {0..10}`, `a = α` (the 11-cycle), `e = β = (0 1 2 3 7)(4 9 6 10 5)`, right actions,
`(uv)|_x = u|_x v|_{x^u}`.

**The survivor.** The first chain survivor, with root words `(a, a, e)` and no decorations:
- `s = α` with `s|_0 = s`, `s|_1 = a`, `s|_2 = e`, `s|_3 = t`;
- `t = α` with `t|_0 = t`, `t|_4 = a`, `t|_5 = u`;
- `u = β` with `u|_0 = u`, `u|_6 = a`.

`G = ⟨M_11, s, t, u⟩` is fully self-replicating, `G = G^X ⋊ M_11`.

## Theorem

1. **The loops generate `G`.** `⟨s, t, u⟩ = G`. So the loop leaf of the star in item 3 of
   `unit-weight-polynomial-recursions-split-over-loop-edges` maps onto `G`, and the
   tree-of-factors obstruction genuinely fails for this recursion: it is a (γ)-case.
   The proof has three steps.
   - Every vertex stabilizer section of `H = ⟨s, t, u⟩` is all of `G`.
   - A commutator `[sT, (sT)^{sUSSS}]` is a coordinate element `ι_2(δ)` with
     `δ` having nontrivial root. Normal closure then gives `H ⊇ ∏_x ι_x(G')`.
   - `H` maps onto `G / ∏_x ι_x(G') = Z^{33} ⋊ M_11`.

2. **But `H_1(G; Z) = Z^3`.** The three signed exponent sums `e_s, e_t, e_u` all descend to
   `G`, so `b_1(G) = 3`. Hence `G` is not of type `FP_2` and **not finitely presented**, by
   item 3 of `fully-self-replicating-fp2-groups-have-odd-cyclic-h1`. By item 5 there, its
   Tits host is not finitely presented either.

3. **Linear descent theorem.** The hypotheses are:
   - (U): every letter section has at most one state letter;
   - `N = M^p − I` is nilpotent, where `M` is the signed section-count matrix and `p` is a
     multiple of the section-cycle lengths;
   - (T_p): for each letter `s`, at most one level-`p` section of `s` contains a letter of the
     signed strongly connected component of `s`, and that letter is `s^{+1}`.

   For a section-closed letter set `D`, let:
   - `D_low` be the section closure of the letters reached by leaving a component;
   - `C_D` be the label image of the cycle space of the level-`p` loop graph on `D`-edges.

   Suppose `L` is valid on `F(D) ∗ P` and `Λ_low` is valid on `F(D_low) ∗ P`. Then a
   functional `λ` supported on `D` is valid on `F(D) ∗ P` if:
   - (i) `λN` agrees with an element of `span L` on the `D`-columns;
   - (ii) `λ` vanishes on `K_D = {r ∈ C_D : L r = 0, N r = 0}`;
   - (iii) `λ` agrees with an element of `span Λ_low` on the `D_low`-columns.

   Here "valid" means that `λE` vanishes on every relator. Iterating to a fixpoint over the
   section-closed `D` gives a space `Λ_S` with **`b_1(G) ≥ dim Λ_S`**.

   The key lemma: a stable relator `z` with `z|_u = z` along a thread spells a closed walk in
   the loop graph, and it satisfies `M^m E(z) = E(z)`. So `E(z) ∈ C_D ∩ ker N`.

4. **All 1373 survivors die.** On every survivor of the four families of
   `poly_star_screen.py`, `descent.py` verifies (U), (T_p) and the nilpotence of `N`, and it
   finds `dim Λ_S ≥ 1`:

   | family | `p` | survivors | dim 3 | dim 2 | dim 1 | dim 0 |
   |---|---|---|---|---|---|---|
   | chain  | 1 | 792 | 637 | 155 |  0 | 0 |
   | fan    | 1 | 358 |   0 | 337 | 21 | 0 |
   | cycle  | 2 | 202 |   0 | 181 | 21 | 0 |
   | scycle | 4 |  21 |   0 |   0 | 21 | 0 |

   So **every survivor has `b_1 ≥ 1` and is not finitely presented.** With item 5 of
   `unit-weight-polynomial-recursions-split-over-loop-edges`, all 16,384 screened
   three-letter M_11 recursions are not finitely presented.

5. **Design consequence.** Consider a unit-weight polynomial M_11 host satisfying (U),
   (Poly) and (T_p). If it is finitely presented, then it needs `Λ_S = 0`: every
   exponent-sum functional must be killed by condition (ii). That requires nonzero
   `C_D ∩ ker N`, meaning closed loop-graph walks whose letter sums are fixed by `M^p`,
   at each level `D` where a functional would otherwise be born.

   The 63 survivors with `dim Λ_S = 1` show how far such kills go in the screened families:
   - fan (21): `Λ_S = ⟨e_s + e_u⟩`, so even the sink letter's own sum `e_t` is killed;
   - cycle (21): `Λ_S = ⟨e_s + e_t⟩`;
   - scycle (21): `Λ_S = ⟨e_u⟩`.

   So kills do occur, but in no survivor do they exhaust `Λ_S`. Surviving `b_1` is the first obstruction to
   check in any future screen, before any splitting argument.

## Evidence and checks

- `descent.py` with no arguments prints the fixpoint for the survivor:
  `Λ_{u} = ⟨e_u⟩`, then `Λ_{t,u} = ⟨e_t, e_u⟩`, then `Λ_S = Q^3`.
- `sanity.py` certifies every 16th member of all four families (1024 recursions). It finds
  64 words of finite order `≤ 60` among letters, products `s t^{±1}` and loops. Every
  certified functional vanishes on all of them (0 violations), as it must.
- `loops_generate.py` prints `ok` for the stabilizer sections and for the coordinate
  element. `lat1.py` finds root image of order 7920 and rank-33 index-1 lattice image.

## What this leaves

- **The obstruction is homological, not a splitting.** Item 1 shows that the loop leaf can
  map onto `G`. So the star obstruction is sharp. A candidate in this class must both escape
  item 3 of `unit-weight-polynomial-recursions-split-over-loop-edges` (for example through
  (γ)) *and* have `b_1 = 0`.
- **Next step.** Search unit-weight polynomial recursions for `Λ_S = 0` directly.
  - Use `descent.py` as the first filter. It is cheap: exact linear algebra on the
    `|S| × |S|` matrix `N` and the level-`p` loop graph.
  - Only then test (γ).
  - Designs that kill the lowest functional need a cycle of loops whose letter sum lies in
    `ker N`. The balanced-loop idea (a letter `c` with sections `c` and `c^{-1}`) makes
    `e_c` non-conserved (`M e_c = 0` on that letter), but it leaves (Poly), since the
    activity is exponential. (T_p) fails for it too, so item 3 does not apply there.
- `descent.py` gives a lower bound only. A survivor of a future screen with `Λ_S = 0` still
  needs `H_1` computed or bounded by other means.

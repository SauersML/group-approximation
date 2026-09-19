---
rg: 2
id: c2-slide-route-passes-every-relation-module-test
kind: claim
title: For the admissible (C2) pair, every three-generator slide group Gamma'' = <x,y,t | f(u0), f(u1)> whose coefficient vector m has c.m a unit has exactly the relation module of G (Q kappa is unitriangular), and Z[H\G] = H(g-2)ZG, so no module or coset invariant decides t = 1. RP(H,G) through Gamma'' is a pure relation-gap question. The w12 coset invariant extends to every generating pair of G as H(g-2) times a transition class in H^2(G;ZG)
distinct_from:
  c2-one-relator-lift-presentations-are-obstructed: that kills the two-generator shape z = f(z) over the Nielsen class of (x,y), with the coset invariant Phi. This proves that Phi and every relation-module invariant are blind for the three-generator slide shape, bounds the number of t-letters, and extends Phi to arbitrary generating pairs.
  admissible-ab-nonzero-two-cell-base-exists: that builds one slide group from the certificate d and finds t != 1 in A_5. This shows the module data of every slide group are those of G, and that t != 1 is decided only by relation-gap phenomena. It also screens 480 randomized slide groups: every one has t != 1 in one of A_5, PSL(2,7), A_6, PSL(2,8), PSL(2,11).
artifacts:
  - research/c2-slide-route-passes-every-relation-module-test-proof.md
  - experiments/c2-slide-screen-2026-09-18/RESULTS.md
  - experiments/c2-slide-screen-2026-09-18/groups.py
  - experiments/c2-slide-screen-2026-09-18/screen.py
  - experiments/c2-slide-screen-2026-09-18/retest.py
  - experiments/c2-slide-screen-2026-09-18/run_screen.sh
  - experiments/c2-slide-screen-2026-09-18/pair_invariant.py
  - experiments/c2-slide-screen-2026-09-18/gap_li.py
---

**ESTABLISHED** through `c2-slide-route-passes-every-relation-module-test-proof`. Unreviewed.
(S0)–(S3) are proved by hand. `pair_invariant.py` checks the Fox identity of (P1) exactly in the
normal form of `F_4 ⋊ Z`. (S4) is a computation, and it proves only the negative statements it
lists.

## Setting

This is the pair of `admissible-ab-nonzero-two-cell-base-exists`:
- the group is `G = ⟨x,y | w⟩`, with `w = yxYXXyyxYXYxYYxyXy`;
- `H = ⟨a,…,e | u_0, u_1⟩ ≤ G`, with basis words `φ_0`;
- `g = Xy ∉ H`, and `φ_0(u_0) = w`, `φ_0(u_1) = gwg^{-1}`;
- `c_z = g∂_z u_0 − ∂_z u_1 ∈ ZG` is the certificate row, with `Σ c_z d_z = 1`.

A **slide datum** is a map `f : F(a,…,e) → F(x,y,t)` with `f(z) = z` in `G` under `t ↦ τ`. Its
**slide group** is `Γ'' = ⟨x,y,t | f(u_0), f(u_1)⟩`. If `Γ'' ≅ G` compatibly, then `RP(H,G)` holds
(`|T| = 3`, `|R| = 5`).

## Statement

- **(S0) Normalization.** One may take `τ = 1`, via the automorphism `t ↦ tτ̂` of `F(x,y,t)`.
  Then `f(z) = Π_z^{-1} φ_0(z)`, with `Π_z ∈ ⟨⟨t⟩⟩` and `[Π_z] = m_z[t]`.
- **(S1) Every relation-module test is passed.** In the basis `[w], [t]` of the relation module
  `K_ab ≅ ZG^2` of `⟨x,y,t | w,t⟩`, the classes of `f(u_0), f(u_1)` form the matrix `κ`. With
  `Q = ((1,0),(g,−1))`, we get `Qκ = ((1, ∗),(0, −c·m))`.
  - So `[f(u_0)], [f(u_1)]` is a basis of `K_ab` iff `c·m = ±h` (units of `ZG` are trivial).
  - Word choices, factor orders and `⟨⟨w⟩⟩`-insertions do not change `κ`.
  - The kernel `Λ = ⟨⟨t⟩⟩ ≤ Γ''` is perfect, and `Γ'' ≅ G` iff `Λ = 1`. Deciding this is a
    relation-gap question for `G` on `(x, y, t)`.
  - The coset test is vacuous as well: `Z[H\G] = H(g−2)ZG`. Explicitly, `s = Y(2yxYx − 2xYx − x)`
    has `H(g−2)s = H`.
- **(S2) Occurrence bound.** `exp_t f(u_0) = ε(c·m) = ±1` and `exp_t f(u_1) = ±2`. If `Γ'' ≅ G`,
  then `t` occurs at least 3 times in `f(u_0)`.
  - With one occurrence, eliminating `t` would give a lift over `(x,y)` with `f'(u_0) = 1` and
    `Φ[f'(u_1)] = Hg − 2H`, which is not a single coset.
- **(S3) The coset invariant for any generating pair.** Let `J = ∂_x w ZG + ∂_y w ZG`.
  - **(P1)** `H(g−2)J = 0`.
  - For a generating pair `(x', y')` with `G = ⟨x', y' | r'⟩`, let `μ̄ ∈ ZG/J ≅ H^2(G;ZG)` be the
    degree-2 entry of the comparison chain map. It is a generator.
  - A presentation `G = ⟨H, x', y' | z = f(z)⟩` over any one-relator presentation of `H` forces
    `H(g−2)μ̄ = ±Hh`.
  - For the Nielsen class of `(x, y)`, `μ̄` is a unit, and this recovers w12 (O4).
  - So the non-Nielsen `|T| = 2` case reduces to the arithmetic of generators of `H^2(G;ZG)`.
- **(S4) Screen.** See `RESULTS.md` for the randomized slide groups (factor permutations,
  `w`-insertions and cancelling pairs; `c·m = 1` throughout).
  - The base group has homomorphisms to `A_5` (18, `x` up to conjugacy) and to `PSL(2,7)` (16)
    with `t ≠ 1`. It also has 31 subgroups of index at most 5, against 24 for `G`.
  - 480 variants were screened. 35 have no such homomorphism to `A_5` or `PSL(2,7)`, but every one
    of those 35 has one to `A_6` (19), `PSL(2,8)` (13) or `PSL(2,11)` (3), with `t ≠ 1`.
  - So `Λ ≠ 1` for every tested slide group. Small perfect quotients detect the relation gap
    readily, even though no module invariant can.

## What this leaves

- `ρ(H,G) = 0` through the slide route needs a proof that `Λ = 1` for some slide group. No module
  invariant can supply it, and no module invariant can refute it.
- `ρ(H,G) = 1` needs a genuinely homotopical invariant, i.e. a relation-gap detector.
- For `|T| = 2`, the open cases are now:
  - generating pairs whose transition class `μ̄` satisfies `H(g−2)μ̄ = ±Hh`;
  - relators mixing `H` and `T`, which no stable-module invariant excludes
    (`relative-realization-is-relative-efficiency`).

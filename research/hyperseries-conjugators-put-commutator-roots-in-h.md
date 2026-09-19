---
rg: 2
id: hyperseries-conjugators-put-commutator-roots-in-h
kind: claim
title: In Bagayoko's bi-ordered group of hyperseries under composition, an element is conjugated outward by a conjugator below the identity, so the tower of G(K; 1, ±1) = <y, t | y_1^K = [y_0, y_2^{±1}]> maps into it with every letter of one sign; all these groups lie in H, which puts 18 of the 26 open commutator-root words in H
distinct_from:
  commutator-root-frontier-kills-pl-and-bi-ordered-targets: its item 4 constrains maps of the whole group G, which must respect t; here the map is defined only on the half-kernel N_[0,∞) and ignores t, so no convex-chain condition applies. Its item 2 asks for one map of G; here per-step maps from a single map of N_[0,∞) are enough, through the shift isomorphisms N_[-m,n] ≅ N_[0,m+n].
  commutator-root-minus-one-groups-have-generalized-torsion: that kills every R*-target of N_[0,3] for (α, β) = (-1, 1); the sign rule here fails exactly for that pair, and nowhere else.
  malcev-root-steps-put-commutator-root-one-relators-in-h: its item 3 kills residually-𝒮 targets; the target here is a subgroup of a simple group of hyperseries, not residually solvable, as item 3 requires.
  kaplansky-zero-divisor-conjecture: no case of the conjecture changes; torsion-free one-relator groups already satisfy it.
artifacts:
  - experiments/commutator-root-free-orders-2026-09-19/hyperseries_first_steps.py
  - experiments/commutator-root-free-orders-2026-09-19/hyperseries_first_steps.out
---

**ESTABLISHED** (written proof, unreviewed) by [[hyperseries-conjugators-put-commutator-roots-in-h-proof]].
The proof uses four stated results of Bagayoko, *Ordered groups of formal series, and a conjugacy problem*
(arXiv:2509.09186, 2025). That paper is a recent preprint. This is a resolution of the largest block of the
commutator-root frontier. Nothing is new for the zero-divisor conjecture.

**Setting.** As in [[commutator-root-frontier-kills-pl-and-bi-ordered-targets]]:
- `G(K; α, β) = <y, t | y_1^K = [y_0^α, y_2^β]>`, with `y_i = t^{-i} y t^i` and `[g, h] = g^{-1} h^{-1} g h`.
- `N` is the normal closure of `y`, and `N_[m,n] = <y_m, …, y_n>`.
- For `α = 1` the step `N_[0,n] ⊂ N_[0,n+1]` is the cyclic HNN extension with stable letter `y_{n+1}` and relation
  `y_{n+1}^{-β} y_{n-1} y_{n+1}^β = y_{n-1} y_n^K`. The base `N_[0,1]` is free on `y_0, y_1`.
- `Γ = (L̃^{>ℝ}, ∘, x, <)` is the group of positive infinite finitely nested hyperseries under composition. By
  Bagayoko it is a bi-ordered group, and any two elements `> x` are conjugate in it (Cor. 4.22).
- Products in `Γ` are compositions, `g · h = g ∘ h`.

## Theorem

1. **Outward conjugators lie below the identity.** Let `x < A < B` in `Γ`. Then some `c ∈ Γ` with `c < x`
   satisfies `A ∘ c = c ∘ B`.
   - Explicitly, let `V_A` be an Abel function for `A`, meaning `V_A ∘ A = V_A + 1` (it exists by Bagayoko's
     Thm. 4.6). Then `V_A - V_B` is bounded below by a real number `r`, and every `c_s = V_A^{-1} ∘ (V_B + s)` with
     `s < r` works.
   - By `C(x + 1) = x + ℝ` (Cor. 4.26), the `c_s` with `s ∈ ℝ` are all the conjugators.
   - Taking inverses gives the mirror statement. If `b < a < x`, some `c < x` satisfies `a ∘ c = c ∘ b`.
2. **The tower maps into `Γ` with one sign.** Let `K ≥ 1` and `β = ±1`. There is a homomorphism
   `φ: N_[0,∞) → Γ` in which every `φ(y_i)` lies on the side `-β` of `x`: below `x` if `β = 1`, above it if
   `β = -1`.
   - Start with `φ(y_0) = φ(y_1) = x - β`.
   - At the step for `y_{n+1}`, put `a = φ(y_{n-1})` and `b = a ∘ φ(y_n)^K`. Then `b` is further from `x` than
     `a`, on the same side.
   - Item 1 gives a conjugator `c < x`. Put `φ(y_{n+1}) = c^β`, which lies on the side `-β` again.
   - `hyperseries_first_steps.py` checks the first two steps exactly for `K = 2, 3`, with explicit letters: for
     `K = 2, β = 1` they are `x - 1`, `x - 1`, `x/3` and `log_9(x + 9/8) + s`. Later letters need the Abel functions
     of iterated exponentials, which are genuinely hyperseries.
3. **Membership.** `G(K; 1, ±1) ∈ 𝓗` for every `K ≥ 1`. By reversing `t`, so does `G(K; -1, -1)`.
   - The map `φ` is injective on every edge group `<y_{n-1}>` of the tower, because `Γ` is torsion-free.
   - Its image is a countable bi-ordered group, so it lies in `𝓗`.
   - Item 1 of [[edge-injective-quotients-give-hughes-free-division-rings]] then climbs every step `N_[0,n]`, and
     conjugation by `t^m` identifies `N_[-m,n]` with `N_[0,m+n]`.
   - So `N` is a directed union of groups in `𝓗`, and `G = N ⋊ <t>` is an extension of `N` by `Z`. Both closures
     are item 1 of [[vertex-injective-quotients-give-hughes-free-division-rings]].
4. **Frontier count.** By item 1 of [[commutator-root-frontier-kills-pl-and-bi-ordered-targets]], the 26 words
   left open through length 15 are the groups `G(K; α, β)` with `K ∈ {2, 3}`.
   - This puts the 12 words with `(α, β) = (1, 1)` and the 6 with `(1, -1)` in `𝓗`: 12 of length 14 and 6 of
     length 15.
   - It includes `G(2; 1, 1)`, the largest class.
   - Hughes-free division rings then exist in every characteristic and for crossed products, as in
     [[malcev-root-steps-put-commutator-root-one-relators-in-h]].
5. **Where the sign rule fails is where the obstruction lives.** For general `α = ±1` the construction needs
   `α = sign K`, up to the symmetries of the family.
   - For `(α, β) = (-1, 1)` the edge `<y_{n-1}^{-1}> → <y_{n-1}^{-1} y_n^K>` forces alternating signs. Item 1 then
     forces a constant sign, so the recursion stops.
   - This is exactly the pair whose `N_[0,3]` has generalized torsion
     ([[commutator-root-minus-one-groups-have-generalized-torsion]]), so there no bi-orderable target exists at all.

## What is new, and what is not

- **New.** Membership of `G(K; 1, ±1)` in `𝓗`, for all `K ≥ 1`, and the first use of a group with all positive
  elements conjugate as a target for a Magnus tower. The mechanism is that item 1 fixes the sign of every
  conjugator, and the sign is the one the tower needs when `α = sign K`.
- **Not new.** That `Γ` is a bi-ordered group in which all positive elements are conjugate is Bagayoko's theorem.
- **Still open.** Whether `G(2; 1, 1)` is bi-orderable, or even R*. The map `φ` is not `t`-equivariant, and it is
  not known whether any map of all of `G` into `Γ` keeps `y`.

## Where it stops

- Through length 15, the open commutator-root frontier is now the 8 words with `(α, β) = (-1, 1)`: 6 of length 14
  and 2 of length 15.
- For those words a target must lie in `𝓗`, have generalized torsion, and be neither PL nor locally residually 𝒮.
- **Next step.** Look for a locally indicable group with generalized torsion that is known to be in `𝓗` and
  receives `N_[0,3]` of `G(2; -1, 1)` with `y` kept. Candidates are free-by-cyclic groups, or one-relator groups
  certified at length at most 13.
  - Alternatively, prove that every `𝓗`-target of `N_[0,3]` kills `y`.

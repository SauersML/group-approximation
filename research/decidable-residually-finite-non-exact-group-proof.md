---
rg: 2
id: decidable-residually-finite-non-exact-group-proof
kind: route
title: Decide a word of length n in the n-th finitely presented residually finite stage of Osajda's tower
target: decidable-residually-finite-non-exact-group-exists
requires: [recursive-residually-finite-non-exact-groups-exist, residually-finite-non-exact-groups-exist, fp-residually-finite-groups-have-solvable-word-problem, lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts]
artifacts:
  - research/artifacts/exactness-boone-higman-separator-2026-09-17.md
  - research/artifacts/sk-free-1-exactness-2026-09-13-part1.md
  - research/artifacts/sk-free-1-exactness-2026-09-13-part2.md
---

Derivation. The verbatim sources are in `research/artifacts/exactness-boone-higman-separator-2026-09-17.md` §1, and the computation is in §2 there.

**Setup** (Osajda, arXiv:1703.03791, l.319–330).
- `G_i = ⟨S | Θ̂_1, …, Θ̂_i⟩` is finitely presented.
- `q^i_∞ : G_i ↠ G` is the quotient map onto `G = lim G_i`.
- `φ_i : G_i → F_i` has finite image.
- `φ^∞_i : G → F_i` is the induced map.
- The paper proves, for all indices:
  - (C): `φ_j(g) ≠ 1` for every `g` in the radius-`j` ball of `Cay(G_j,S)` other than `1`;
  - (D): the maps commute with the quotients, in particular `φ^∞_i ∘ q^i_∞ = φ_i` (used at l.434).

**Step 1: reduction to a finite stage.** Let `w` be a word of length `ℓ` and put `n = max(ℓ,1)`. Let `g'` be its image in `G_n`, which lies in the radius-`n` ball.
- If `g' = 1`, then `w = 1` in `G`, because `G` is a quotient of `G_n`.
- If `g' ≠ 1`, then `φ^∞_n(q^n_∞(g')) = φ_n(g') ≠ 1` by (D) and (C), so `w ≠ 1` in `G`.

So `w =_G 1` iff `w =_{G_n} 1`.

**Step 2: the stages are uniformly computable.**
- By `recursive-residually-finite-non-exact-groups-exist` (route steps 2–3), `i ↦ Θ̂_i` is computable from the recursive input sequence.
- Taking fundamental cycles at every base vertex (review fix F1 on that node) gives a finite relator set for each `G_i`. So `n ↦` (finite presentation of `G_n`) is computable.

**Step 3: decide at the stage.**
- Each `G_n` acts properly cocompactly on a CAT(0) cube complex (l.396, quoted; hyperbolicity is not claimed and is not used), hence is residually finite by Wise--Agol (l.396 and the induction basis, quoted).
- The procedure of `fp-residually-finite-groups-have-solvable-word-problem` takes the finite presentation as input. It halts on every word, because the presented group is residually finite.
- Composing Steps 1–3 decides `w =_G 1`. So `G` has solvable word problem.

**Step 4: non-exactness.** `G` is not exact by `residually-finite-non-exact-groups-exist` (l.425–426: `Cay(G,S)` contains D-regular graphs of growing girth). Non-exactness is equivalent to failure of property A (Osajda l.119–120; Osajda arXiv:1406.5015 l.166).

**Step 5: simple decidable host.**
- `G` is residually finite, hence LEF (artifact `sk-free-1-exactness-2026-09-13-part1.md` §1 step 2).
- By `lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts`, `G ≤ H` with `H` infinite, finitely generated, simple, Kazhdan, LEF and with solvable word problem.
- By Willett (arXiv:math/0612492 l.1607, quoted), property A passes to subgroups. So `H` has no property A and is not exact.

∎

**Load-bearing.**
- Condition (C) at radius exactly `j` on the stage `G_j`, not on `G`.
- The factorization (D) through the direct limit.

Both are printed in the paper and proved for every index. No further effectivity beyond the recursive node is used.

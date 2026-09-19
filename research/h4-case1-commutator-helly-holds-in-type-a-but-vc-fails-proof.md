---
rg: 2
id: h4-case1-commutator-helly-holds-in-type-a-but-vc-fails-proof
kind: route
title: Commutator cosets are cosets of centralisers; the arc-model Helly theorem gives (H″) in type A through the retraction dictionary, and a faithful Artin-representation check exhibits an A_4 tuple with no vertex centre
target: h4-case1-commutator-helly-holds-in-type-a-but-vc-fails
requires:
  - h4-case1-helly-is-a-commutator-double-coset-problem
  - h4-case1-pure-centre-iff-px-conjugate-of-f-holds-triple
  - braid-pure-single-edge-hexagons-always-have-a-centre
artifacts:
  - experiments/h4-cchelly-2026-09-18/cchelly.c
  - experiments/h4-cchelly-2026-09-18/dumpch.py
  - experiments/h4-cchelly-2026-09-18/dumpgen.py
  - experiments/h4-cchelly-2026-09-18/comtab.py
  - experiments/h4-cchelly-2026-09-18/run34.sh
  - experiments/h4-cchelly-2026-09-18/artinverify.py
  - experiments/h4-cchelly-2026-09-18/a4vcmin.py
  - experiments/h4-cchelly-2026-09-18/a4vcexample.py
  - experiments/h4-cchelly-2026-09-18/C24.log
  - experiments/h4-cchelly-2026-09-18/C34.log
  - experiments/h4-cchelly-2026-09-18/X_A4_36.log
  - experiments/h4-cchelly-2026-09-18/X_B4_35.log
  - experiments/h4-cchelly-2026-09-18/X_H4r_24.log
---

Notation is as in the target.

**(Q.1).** Let `u, u' ∈ N`.
- Suppose `[u, a] = [u', a]`. Cancelling `a^{-1}` on the right gives `uau^{-1} = u'au'^{-1}`, so `u^{-1}u' ∈ C_N(a)`.
- Conversely, for `c ∈ C_N(a)`, `[uc, a] = uca c^{-1}u^{-1}a^{-1} = uau^{-1}a^{-1} = [u, a]`.

So a nonempty `U_a(k)` equals `uC_N(a)` for any `u` in it.

**(Q.2).** The following are equivalent:
- `waw^{-1}a^{-1} = wbw^{-1}b^{-1}`;
- `aw^{-1}a^{-1} = bw^{-1}b^{-1}`;
- `b^{-1}aw^{-1} = w^{-1}b^{-1}a`;
- `w` commutes with `b^{-1}a`.

**(Q.3).** Let `u ∈ U_a(k)` and `v ∈ U_b(k)`.
- `u^{-1}v = cd` with `c ∈ C_N(a)` and `d ∈ C_N(b)` iff `uc = vd^{-1}`.
- By (Q.1), this says exactly that `uC_N(a) = U_a(k)` meets `vC_N(b) = U_b(k)`.

For the `τ` form:
- by (Q.2), a point of `U_a(k) ∩ U_b(k)` is a `w ∈ C_N(b^{-1}a)` with `τ_a(w) = k`;
- conversely, `τ_a = τ_b` on `C_N(b^{-1}a)`.

**(Q.4).** Let `k ≠ 1` and `w ∈ U_a(k) ∩ U_b(k)`. By (Q.1), `U_a(k) = wC_N(a)` and `U_b(k) = wC_N(b)`.
- Every `(u, v) ∈ U_a(k) × U_b(k)` is `(wc, wd)` with `c ∈ C_N(a)` and `d ∈ C_N(b)`.
- Since `k ≠ 1`, VC holds at `(u, v)` iff `u ∈ U_b(k)` or `v ∈ U_a(k)`. That is, iff `c ∈ C_N(b)` or `d ∈ C_N(a)`.
- So VC fails somewhere iff there exist `c ∈ C_N(a)∖C_N(b)` and `d ∈ C_N(b)∖C_N(a)`. This happens iff neither
  centraliser contains the other.

**(A).** Let `A = B_{n+1}` of type `A_n` with pure braid group `P`.

*Step 1: the cited reductions hold in type A.*
- The proofs of (M), (C) and (H) in `h4-case1-pure-centre-iff-px-conjugate-of-f-holds-triple` use only three
  things:
  - the facts (F1)–(F3) listed there;
  - `W_X ∩ W_Y = W_Z` in the Coxeter group;
  - the tuple and hexagon formulas.
- The proofs of (R), (H′) and (K) in `h4-case1-helly-is-a-commutator-double-coset-problem` use only (F1)–(F3).
- In `B_{n+1}` these facts hold:
  - `ρ_X` forgets strand 1 and `ρ_Y` forgets strand `n+1`. These are the maps induced by the inclusions of
    hyperplane complements, which is (F1).
  - `P_Y = F ⋊ P_Z` is the Fadell–Neuwirth splitting, with `F = ker(ρ_X|P_Y)` free of rank `n-1`, which is (F2).
  - (F3) is immediate.

So the chain "Case 1 tuple, then hexagon, then (H), then `β_1 ∈ C_N(α_1)C_N(α_2)`, then (K)" is valid verbatim in
type `A_n`.

*Step 2: every Case 1 hexagon in type A has a pure centre.*
- Let `ι` be the automorphism `σ_i ↦ σ_{n+1-i}` of `B_{n+1}`. It preserves `P` and maps `A_X = ⟨σ_2,…,σ_n⟩` onto
  `⟨σ_1,…,σ_{n-1}⟩`, which is the arc stabiliser of `braid-pure-single-edge-hexagons-always-have-a-centre`. It maps
  `A_Y` onto `⟨σ_2,…,σ_n⟩`, which is the spider stabiliser for `k = 1`.
- `ι` preserves cosets and adjacency. So it carries the Case 1 hexagon on `x_1, x_2, x_3, y_1, y_2, y_3` to a
  single-edge hexagon of arcs and spiders.
- That hexagon has pure letters, because `α_i, β_i ∈ P`. By part 3 of the cited node it has a centre: a spider with
  leg set `{1}` adjacent to the three arcs.
- A spider `hy_0` has leg set `{1}` iff the permutation of `h` fixes 1. The spider stabiliser maps onto the
  symmetric group of `{2,…,n+1}`, so `hy_0 = h'y_0` with `h'` pure.
- Pulling back by `ι^{-1}` gives a pure `A_Y`-coset adjacent to `x_1, x_2, x_3`, which is a pure bound.

*Step 3: (H″).*
- Let `a ≠ b` in `F` and `u, v ∈ N` with `[u, a] = [v, b]`. Put `α_1 = a^{-1}`, `α_2 = b`, `β_3 = u` and
  `β_1 = u^{-1}v`.
- By (K), `(*)` holds, and `α_1α_2 = a^{-1}b ≠ 1`, so this is a Case 1 tuple.
- By Step 2 it has a pure bound. By (H) and (H′), `u^{-1}v = β_1 ∈ C_N(α_1)C_N(α_2) = C_N(a)C_N(b)`.

**(B).** `a4vcexample.py` checks every assertion of (B) in the Artin representation `B_5 → Aut(F_5)`, which is
faithful (Artin). It prints `ALL OK`.
- The letters are membership-clear:
  - each `p_i` is a pure braid on strands 1–4 whose only twist involves strand 1, so `ρ_X(p_i) = 1`;
  - each `x_i` is a pure braid on strands 2–5 whose only twist involves strand 5, so `ρ_Y(x_i) = 1`.
  - They coincide with the `dumpgen.py` letters that `cchelly` uses, as the script asserts.
- The failure of all three vertex conditions is then (K)'s table in the cited node.
- The existence of the pure bound `γ = u^{-1}w` follows from (K), since `[w, a] = [w, b] = k`.
- `a4vcmin.py 2 3` (about 2.5 min) enumerates the witnesses `(w, c, d)` of (Q.4) in the stated balls and rechecks
  each resulting `(u, v)` directly. It found 8 pairs and printed the minimum.

Independently, the Garside-normal-form search `cchelly A4 3 6 all` (`X_A4_36.log`) counts 18720 VC failures.
`artinverify.py A4 X_A4_36.log` confirms its printed lines, so the two exact methods agree.

**(C).**
- `cchelly` hashes the exact left-greedy normal form of `[u, f]` for all `f` in the F-ball and `u` in the N-ball.
- It verifies every shared class exactly. It counts VC failures by (K) and splits them by whether
  `U_a ∩ U_b` meets the ball (HBALL) or not (HCAND).
- The rank-3 and A_4 runs used `all` mode. The H_4 `LA = 2, LB = 4` run is `C24.log` (0 failures).
- `run34.sh` repeats H_4 at `LA = 3, LB = 4`, in four hash chunks and one pairing pass. The result is `C34.log`: 954436 tuples
  and 0 failures.
- The B_4 row is `X_B4_35.log` and the reversed H_4 row is `X_H4r_24.log` (`cchelly H4r 2 4 all`).
- Tables are regenerated with `dumpch.py`. They are not stored.

That HCAND in A_4 are false alarms is (A) applied to those classes.

**(L).** Let `φ` be a type-preserving simplicial map of layers and `H = x_1y_{12}x_2y_{23}x_3y_{31}` a hexagon.
- If a vertex `y` of `H` is adjacent to `x_1, x_2, x_3`, then `φ(y)` is a vertex of `φ(H)` adjacent to
  `φ(x_1), φ(x_2), φ(x_3)`.
- So if `φ(H)` has no vertex centre, neither has `H`.
- `ρ_V` is onto `P_5`, so `P_5`-translates of image hexagons are again images.

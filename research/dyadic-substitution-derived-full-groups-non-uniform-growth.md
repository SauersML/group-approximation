---
rg: 2
id: dyadic-substitution-derived-full-groups-non-uniform-growth
kind: claim
title: For a primitive substitution of constant length 2 with a non-periodic fixed point, the derived topological full group [[T]]′ has non-uniform exponential growth
artifacts:
  - research/artifacts/sk-cornulier-q7-nonuniform-growth-2026-09-13-part1.md
  - research/artifacts/sk-cornulier-q7-nonuniform-growth-2026-09-13-part2.md
distinct_from:
  substitution-subshift-elementary-groups-non-uniform-growth: that is about the Kazhdan matrix groups EL_3(LC(X,F_2)⋊Z); this is about the amenable derived topological full group [[T]]′ of the same subshifts.
---

**ESTABLISHED (unreviewed; sk-cornulier-q7).**
- **Statement.** Let `ζ` be a primitive substitution of constant length 2 with a non-periodic fixed point, and let `(X,T)` be its two-sided subshift. Then `ω([[T]]′) = inf_S ω([[T]]′, S) = 1`, and `[[T]]′` has exponential growth, so its growth is non-uniformly exponential.
- **Examples.** Thue–Morse and period doubling.
- **Printed question answered.** Cornulier's Bourbaki 1064 question 7 (`topological-full-group-derived-uniform-exponential-growth`) has a negative answer for these subshifts. The question stays open for general minimal subshifts, e.g. Sturmian.
- **Proof idea.** This is Sauer–Schesler's proof for Thompson's `V` (arXiv:2605.30163 §§3–5), transferred. `X` is a tower of constant height `2^m` over a clopen copy of itself, and the level set is identified with `{0,1}^n × {1,…,8}`. The generating set of bounded size has four types:
  1. truncated Grigorchuk level permutations;
  2. `Alt(8)` on one fibre;
  3. a linking double transposition;
  4. commuting local generators: partial 3-cycles over the letter cylinders and one shift pair `S ⊗ S^(−1)`.
- **Generation.** Letter cylinders give every clopen set via complements, commutators and shift-pair conjugation. Every good 3-cycle `σ_U` follows, so the whole `[[T]]′` is generated.
- **Growth.** Balls of radius `≤ 2^⌊n/2⌋/3` have `≤ exp(Cℓ^β)` elements, `β < 1`.

Route: `dyadic-substitution-derived-full-groups-non-uniform-growth-proof`.

**Review (sk-verify-16, 2026-09-13): PASS.** An independent re-derivation of the tower model, the shift pairs [s_y, L_(y y′)], and generation W_n = [[T]]′: the fibre and linking steps, the Boolean closure of 𝔅 with [(1 2 3),(3 4 5)] = (1 4 3), twisted 3-cycles, and good σ_U via the Cornulier Lemme eng_cb. Also the commuting-conjugates lemma, the normal form and counting, and ω = 1. The inputs are checked at source: Cornulier arXiv:2002.09342 l.166/216/576–583/780 and Sauer–Schesler arXiv:2605.30163 lem:separation, lem:commuting-conjugates, lem:normal-form, lem:count-p1..p4 and l.1392. Conditional on the imports named in the route. See `research/artifacts/sk-verify-16-2026-09-13-part3.md` §§1–2.

**Review (sk-verify-17, 2026-09-13): PASS.** This is an independent adversarial re-derivation; sk-verify-16 was not read first. Checked:
- the tower model, T_n ⊂ [[T]]′, Steps 1–3 of W_n = [[T]]′ (recomputing σ_(y,y′) = [s_y, L_(y y′)] and [(1 2 3),(3 4 5)] = (1 4 3)), and σ_U = ∏_y σ_(W_y);
- the counting transfer line by line against Sauer–Schesler arXiv:2605.30163 `not:T_n` l.893, `lem:commuting-conjugates` l.920, `lem:normal-form` l.969 and `lem:count-p1..p4` l.1038–1192. The double transposition δ_n counts as one permutation of X_n, and the per-point group (Z/3)^|A|×Z gives (3^|A|(2ℓ+1))^(Cℓ^α).
Model test: Sturmian subshifts have no dyadic towers. Scope: Thue–Morse holds unconditionally (elementary tower proof, sk-verify-14 part4 §4); the general dyadic statement is conditional on `mosse-bilateral-recognizability`. See `research/artifacts/sk-verify-17-2026-09-13.md`.

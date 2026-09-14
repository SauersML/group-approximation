---
rg: 2
id: subshift-group-isomorphism-preserves-rational-spectrum
kind: claim
title: If EL_n over two infinite minimal subshift algebras over F_2 are isomorphic (n ≥ 3, including the note's G_X), the subshifts have the same finite cyclic factors
distinct_from:
  rank-four-subshift-groups-see-rational-spectrum: that proves the invariance only in rank N ≥ 4, where type rigidity holds for both groups; this proves it in rank three for the note's G_X, using type rigidity only for the group that has the cyclic factor, which is secretly of rank 3m.
  subshift-group-finite-simple-shadows-are-ring-models: that asks whether EVERY approximant of G_X is ring type, which stays open for totally minimal X; this avoids that question and still gets the invariant.
  subshift-elementary-group-isomorphism-forces-orbit-equivalence: that is the full strong orbit equivalence conclusion, still open; this proves one necessary consequence of it, equality of rational spectra.
artifacts:
  - research/artifacts/sk-rank3-shadows-2026-09-14.md
---

**ESTABLISHED (unreviewed)** by `subshift-group-isomorphism-preserves-rational-spectrum-proof`.

**Statement.** Let `X, Y` be infinite minimal subshifts, `R_X = LC(X,F_2) ⋊ Z`, and `n ≥ 3`. If
`EL_n(R_X) ≅ EL_n(R_Y)`, then `Cyc(X) = Cyc(Y)`: the orders of the finite cyclic factors agree, equivalently the rational
continuous eigenvalues agree. In particular `G_X ≅ G_Y` forces this.

**Mechanism.** For `m ∈ Cyc(Y)`, the cyclic partition gives `R_Y ≅ M_m(R_(Y_1))`, so `EL_n(R_Y) = EL_(nm)(R_(Y_1))` has rank
`nm ≥ 6`. Rank-four type rigidity then puts `nm` in the invariant `Div`. If `m ∉ Cyc(X)`, periodic ring models of sizes
`g_r p_k` (primes `p_k`) give approximants `SL_(n g_r p_k)(F_2) → EL_n(R_X)` of natural dimension not divisible by `nm`,
contradicting invariance of `Div`.

**Examples.** `G_X` over Thue–Morse (all `2^j` in `Cyc`) is not isomorphic to `G_X` over any Sturmian subshift
(`Cyc = {1}`). Nor is either isomorphic to `G_X` over a Toeplitz subshift with nontrivial periods. Sturmian slopes are
not separated.

**Bearing on the note.** It is a rank-three necessary condition for the note's rigidity Question, "does `G_X ≅ G_Y` force
flip conjugacy or strong orbit equivalence?", since the rational spectrum is an SOE invariant (recalled). Cairn result;
a paper remark would need the proof of rank-four type rigidity.

## Review
- **sk-verify-19 PASS (2026-09-14, `research/artifacts/sk-verify-19-2026-09-14-part2.md` §2):** re-derived:
  - the cyclic partition U = f^{-1}(0) and EL_n(R_Y) = EL_{nm}(R_{Y_1}) through [T];
  - nm ∈ Div by [E] with c = 1, and its isomorphism invariance;
  - m ∉ Cyc(X) ⇒ m ∤ g_r for all r (by [C1], divisibility propagates upward);
  - primitive periodic models of length g_{r_k}p_k give SL_{n g_{r_k} p_k}(F_2) → EL_n(R_X) ([C2]), with nm ∤ n g_{r_k}p_k since gcd(m,p_k)=1.
  - Model tests are consistent. The SOE-invariance remark is recalled and not used.

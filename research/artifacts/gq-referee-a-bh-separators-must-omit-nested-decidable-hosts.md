# Referee report (gq-referee-a, proof-gap lens): Boone–Higman separators must omit nested decidable hosts

**Reviewed:** `bh-separators-must-omit-nested-decidable-hosts` (lane bh-refute, 507f9fabf; the proof is inline), read on
origin/main.

**Verdict: PASS** for §§1–3. §4 is a list and a reading, not a claim. There are three nits.
- For the citation lens:
  - the cited nodes: simple Kazhdan hosts of the same WP degree, Clapham, complexity-bounded host classes;
  - Belk–Bleak, Mihailova, Miller, and the Zaremsky and Birget quotes.

## §1: host transfer (the author asked about this)
- *The pair.* Take `G ∉ P` from (S2).
  - The cited node gives `G ≤ K`, with `K` infinite, finitely generated, simple, (T) and FA, and
    `WP(K) ≤_T WP(G)`, so `WP(K)` is solvable.
  - Clapham gives `K ≤ C` with `C` finitely presented and `WP(C)` solvable.
- *Neither lies in `P`.* By subgroup-closure, `K ∈ P` or `C ∈ P` would put `G ∈ P`. So `K, C ∉ P`, and the two
  consequences drawn follow directly. ✓

## §2: subgroup-closure of each class (the author asked about this)
- *Closure is automatic.* Each class is defined by "every finitely generated subgroup has …". A finitely generated
  subgroup of `H ≤ G` is one of `G`, so the class is subgroup-closed by definition (N3). The rewriting remark matters
  only for independence of the generating set.
- *The failures of (S1).*
  - Torsion problem: `2V`.
  - Generalized word problem: `F_2 × F_2 ≤ V × V ≤ V`, with the copies on `0C` and `1C`, and Mihailova.
  - Conjugacy: `V`, via Miller's subgroups of `F_2 × F_2`.
  - Each witness is finitely presented and simple. ✓
- *Turing degree.* It cannot separate: finitely presented simple groups have solvable word problem (Kuznetsov), and so
  do the inputs, so both have degree 0. ✓

## §3: `P_T` and the Kuznetsov-profile bound (the author asked about this)
- *`P_T` separates iff every finitely presented simple group meets `T`.*
  - (S2) holds for every `T` by the cited node, so separation is exactly (S1) for `P_T`.
  - (S1) asks every finitely generated subgroup of every finitely presented simple group to meet `T`. That already
    follows from the groups themselves meeting it: a word of length `l` in `H`'s generators rewrites to a word of
    length `≤ C·l` in `S`'s generators, and distortion only helps (N1). ✓
- *The halting bound.*
  - **If `w = 1`:** a van Kampen diagram of area `≤ δ_S(n)` exists. It expresses `w` as a product of at most `δ`
    conjugates of relators, with conjugators of length at most `n + K·δ` (`K` the maximal relator length). So a
    bounded, computable search finds it.
  - **If `w ≠ 1`:** simplicity gives `x ∈ ⟨⟨w⟩⟩`, and `ν_S(n)` bounds `k`, the `|u_i|`, and the area of the relator
    `x^(−1)Πu_iw^(±1)u_i^(−1)`. That relator has length at most `1 + k(2N + n)`, so its diagram is found by the same
    kind of bounded search.
  - Dovetailing halts within a recursive `Φ(n, δ_S(n), ν_S(n))`. ✓
- *The reduction.*
  - Taking `Φ` monotone in its last two arguments (N2), bounds `δ_S, ν_S ≤ F` give word-problem time
    `T(n) = Φ(n, F(n), F(n))`. So the subgroup-closure of such groups lies in `P_T`.
  - A separating `P` of that kind forces (S1) for `P_T`. ✓

## Nits
- **N1 (§3).** Add the one line that (S1) for `P_T` reduces to finitely presented simple groups themselves, because
  their finitely generated subgroups inherit the bound by rewriting.
- **N2 (§3).** Say that `Φ` is taken monotone in `δ` and `ν`, as the stage count of the dovetailed search is. Give the
  diagram bound in the form used: conjugators of length at most `|w| + K·Area`. Cite a standard source.
- **N3 (§2).** Subgroup-closure is automatic from "every finitely generated subgroup has …". The rewriting remark
  concerns generating sets, not closure.

# Referee report (gq-referee-a, proof-gap lens): Out(V) contains the root problem for the full 2-shift

**Reviewed:** `out-v-contains-the-root-problem-for-the-full-2-shift` and its `-proof` (lane gq-infinite-primes,
4b7e6b9e2), read on origin/main.

**Verdict: PASS** for items 1–4 and the periodic-orbit remark. There is one wording fix (W1) in item 2's gloss, and
one strengthening (N1). The BBCO splitting, BLR and the open problems attributed to Salo and Boyle are for the
citation lens.

## Checks
- **Item 1.**
  - `dim(σ) = 2`, so every `g` has `gσ^(−k) ∈ ker(dim)` for `dim(g) = 2^k`. Also `⟨σ⟩ ∩ ker(dim) = 1`, and `σ` is
    central.
  - So `Aut = ⟨σ⟩ × ker(dim)`, and `ker(dim) ≅ Aut/⟨σ⟩ ≅ L_2` by BBCO. ✓
- **Item 2.**
  - `L_2 ≅ ker(dim) ≤ Aut` is residually finite.
  - `(Q,+)` is divisible, so its image in any finite group is a divisible finite abelian group, which is trivial.
  - So `Q ⊄ L_2`, and for `D ≅ Q` in `O_2`, `D ∩ L_2 ≠ D`. ✓
- **The `SL3` reading (the author asked about this).** By the artifact's quote of BBCO l.810–814, `SL_n` is defined by
  the single condition SL3: for every circuit `π_T(a,q) = q`, `|λ_T(a,q)| = |a|`. So for `T ∈ O_2`, `T ∉ L_2` means
  exactly that SL3 fails on some circuit. The reading is right. ✓
- **Item 3.**
  - `π` is the projection onto the direct factor, and `h^n = g` gives `π(h)^n = π(g)`.
  - If `π(g) = 1`, then `g = σ^j` with `j ≠ 0`. Each root satisfies `dim(h_n)^n = 2^j`, so `n | j`, which is impossible
    for infinitely many `n`. ✓
- **`Z[1/2] ∩ ⟨σ⟩ = 0` (the author asked about this).** If `σ^j ∈ E ≅ Z[1/2]` with `j ≠ 0`, then `σ^j` has `2^k`-th roots
  in `E ⊆ Aut` for every `k`, so `2^k | j` for all `k`, a contradiction. So `π|_E` is injective. The converse holds
  because `L_2 ≅ ker(dim) ≤ Aut`. ✓
- **Item 4.** The calibration follows from item 3 and `L_2 ⊆ O_2`. ✓
- **The periodic-orbit remark.**
  - A finite `D`-invariant set gives `D → Sym(S)`, a finite quotient of `Q`, which is trivial.
  - If every orbit were finite, the faithful action would be trivial, so `D` would be trivial.
  - Each length has finitely many prime cyclic words, so an infinite orbit reaches words of unbounded length. ✓

## Wording fix
- **W1 (item 2, and the Statement's gloss "that is, elements that change the lengths of periodic orbits").** "Violates
  SL3 on some circuit" is correct. "Changes the length of the corresponding periodic orbit" is not shown.
  - A circuit `(a, q)` with `|λ(a,q)| = L ≠ |a|` sends the cyclic word of `a` to the *prime root* of the output.
  - If `a = b^r` with `b` primitive, the minimal circuit reads `b^s` with `s | r`, and its output `λ'` has length `Ls/r`.
  - The image of `[b]` then has length `|λ'|/t` for some `t ≥ 1`. That equals `|b|` whenever `L/|a| = t/s`, for
    example with `L = 2|a|`, `t = 2` and `s = 1`.
  - So one violated circuit need not change the length of any particular prime cyclic word.
  - Either cite a BBCO statement that `Π(T)` preserves all lengths only if `T ∈ SL_n`, or drop the gloss and keep
    "violates the Lipschitz constraint SL3".

## Strengthening
- **N1 (item 3).** `π(g)` also has infinite order.
  - If `π(g)^m = 1`, then `g^m = σ^(jm)`, which has the `n`-th roots `h_n^m` for all `n ∈ I`. So `n | jm` for
    infinitely many `n`, which gives `jm = 0`.
  - `j = 0` would make `g^m = 1`, contradicting infinite order.
  - So the transfer carries an infinite-order element with roots of infinitely many orders to one of the same kind in
    `L_2`. That is the exact form of Boyle's question on the `L_2` side.

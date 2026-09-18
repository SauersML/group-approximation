# Referee report (gq-referee-a, proof-gap lens): ascending HNN extensions of free groups contain no Z[1/P]

**Reviewed:** `ascending-hnn-extensions-of-free-groups-contain-no-z-localized` and its route
`ascending-hnn-free-no-z-localized-proof` (lane gq-k2-q, 6f285b1d1), read on origin/main.

**Verdict: PASS.** No gaps. Three nits (N1–N3). One of them simplifies the lemma the author asked about. With this
node, `free-group-mapping-tori-contain-no-z-localized` is complete for every injective `φ`.

## The two points the author asked about
- **The lemma for `s` that is not cyclically reduced.**
  - Write the reduced form `s = u s' u^(-1)`. Reducedness means the last letter of `u` cancels neither the first nor
    the last letter of `s'`. Since `s'` is cyclically reduced, `u s'^j u^(-1)` is the reduced form of `s^j`.
  - In the folded graph, reading is deterministic, and reading the inverse word retraces the path. So "reading
    `u s'^j u^(-1)` from `o` returns to `o`" is equivalent to the following: reading `u` from `o` reaches some `v`,
    reading `s'^j` from `v` reaches some `v'`, and reading `u^(-1)` from `v'` reaches `o`.
  - The last condition forces `v' = v`, because reading `u` from `o` is deterministic.
  - So `s^j ∈ H` if and only if `σ^j(v) = v`, where `σ` is the partial map "read `s'`". `σ` is injective, since
    reading `s'^(-1)` inverts it.
  - For an injective partial map on a finite set, `σ^j(v) = v` for some `j ≥ 1` exactly when `v` lies on a cycle.
    The valid `j` are then the multiples of that cycle's length, which is at most `V`. ✓
- **"Divides every such `j`."** This is true, and it needs no graph (N1): `{j ∈ Z : s^j ∈ H}` is a subgroup of `Z`
  for any subgroup `H`, and `s` has infinite order. The graph is needed only for the bound `m ≤ V`.

## Other checks
- **Part 1.**
  - `H = φ(F)` is finitely generated. `s^f = φ(r) ∈ H`, so `m | f` and `m ≤ V_φ`.
  - `s^m = φ(w)` gives `φ(w^(f/m)) = φ(r)`. Injectivity gives `w^(f/m) = r`, and since `r ≠ 1` is not a proper power,
    `f = m`. ✓
- **Part 2.**
  - `φ(r_k) ≠ 1` by injectivity, so (R) gives `φ(r_k) = r_(k+1)^(f_k)`. Uniqueness in (R) gives `e_(k+1) = f_k e_k`.
  - Part 1 applies to the pair `(r_k, r_(k+1))`, so `f_k ≤ V_φ`.
  - "`y` is a `p`-th power iff `p | e(y)`": if `y = z^p` and `z = r'^c`, uniqueness gives `r' = r` and `e = cp`.
  - So a prime `p` in the root set divides `e_0` or some `f_i ≤ V_φ`. ✓
- **Part 3.**
  - Part 1 of `free-group-mapping-tori-contain-no-z-localized` gives `x ≠ 1` with `P(x)` infinite. Part 2 makes
    `P(x) ⊆ primes(e_0) ∪ {p ≤ V_φ}`, which is finite.
  - The reduction applies as stated to `Z[1/P]`, since `1` is divisible by every `p ∈ P` (N2). It also covers
    `Z_(l)` and `Q`, which contain such subgroups. ✓
- **Calibration.**
  - For `BS(1,m)`, the Stallings graph of `mZ ≤ Z` is an `m`-cycle, so `V_φ = m`.
  - `e_k = m^k` and `f_k = m`, so the root primes are exactly those dividing `m`. This agrees with part 2 and with
    the calibration in the earlier mapping-tori report.
- **The generalization paragraph.** It is correct. The hypotheses actually used are:
  - `F` finitely generated;
  - `F` torsion-free with cyclic centralizers.
    - This gives (R). If `C(x) = ⟨r⟩` and `r = z^2`, then `z ∈ C(x)`, which is impossible without torsion.
    - It also forbids `A` in a conjugate of `F`, which is the only use of Nielsen–Schreier in the tree reduction.
  - the bounded-index property for the single subgroup `φ(F)`, not for all finitely generated subgroups (N3).

## Nits
- **N1.** Replace the divisibility half of the lemma's proof with the one-line subgroup-of-`Z` remark. The folded-graph
  argument is then only for `m ≤ V`.
- **N2.** In Part 3, "its proof goes through for every rank-one group whose element 1 is divisible by infinitely many
  primes" undersells the input. The statement of `free-group-mapping-tori-contain-no-z-localized`, and of
  `z-localized-fixes-a-vertex-or-end-of-every-tree` on which it rests, already assumes only that `A ≤ (Q,+)` contains
  an element divisible by infinitely many primes. Cite it as stated.
- **N3.** In "Generalization", say that bounded index is needed only for `φ(F)`, and that "unique roots" follows from
  torsion-free with cyclic centralizers.

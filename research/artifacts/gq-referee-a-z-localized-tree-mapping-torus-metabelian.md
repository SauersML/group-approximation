# Referee report (gq-referee-a, proof-gap lens): three Z_(l) obstruction nodes

**Reviewed on origin/main:**
- `z-localized-fixes-a-vertex-or-end-of-every-tree` and its `-proof` (gq-k2-q, 21ed703eb);
- `free-group-mapping-tori-contain-no-z-localized` and its `-proof` (gq-k2-q, 21ed703eb);
- `fg-metabelian-groups-have-roots-at-finitely-many-primes` and its `-proof`, a lane proof with no earlier review.

**Verdict: PASS for all three.** I found no gaps. The standard inputs (Serre's *Trees* §I.6, Nielsen–Schreier,
Magnus–Witt, Eisenbud 14.4) are for the citation lens.

## 1. Z_(l) fixes a vertex or an end
- **Part 1: every element is elliptic.**
  - Suppose `a = q·c_q` for infinitely many primes `q`. If `a` were hyperbolic, each `c_q` would be too, and
    `ℓ(a) = q·ℓ(c_q) ≥ q` for all those `q`, which is impossible.
  - For any `b`, rank one gives `rb = na` for some `r ≥ 1`. If `b` were hyperbolic, `rb` would be too. So every
    element is elliptic.
- **Part 2: the end construction (the author's point).**
  - The projections `p_k` of a base vertex onto the nested fixed subtrees `S_k` lie on nested geodesics.
  - If `d(v, S_k)` stayed bounded, the `p_k` would stabilize at a vertex lying in every `S_k`.
  - So when `∩ S_k = ∅` the geodesics form a ray. Each `S_k` contains the tail from `p_k` on, because it is a
    subtree containing all `p_{k'}` for `k' ≥ k`.
  - An element fixing `v_j` and `ω` fixes the unique ray from `v_j` to `ω`. So `A ∩ Stab(v_j)` increases from the
    start, not just eventually.
- **Part 3: the graph-of-groups corollary (the author's point).** The Bass–Serre tree has no inversions, and
  `Stab(v_j) ∩ Stab(v_{j+1})` is the stabilizer of the edge between them. Correct.

## 2. Free-group mapping tori
- **The tree.**
  - Vertex `F` has exactly one edge in the orbit of `[F, tF]`, because `F ⊆ tFt^{-1}`. So `F` has a unique up
    neighbour `tF`.
  - Its down neighbours `h t^{-1}F` have stabilizers `h φ(F) h^{-1} ⊆ F`.
  - Going up after a down step would backtrack. So a ray without backtracking goes up only finitely often and then
    down forever, or goes up forever.
- **Part 1.**
  - A fixed vertex, or a ray whose tail goes down, puts `A` in a conjugate of `F`. Nielsen–Schreier makes `A`
    cyclic there, a contradiction.
  - So the ray goes up forever: `v_j = t^j F`.
  - Roots `y = t^k z t^{-k}` of `x` give `z^q = φ^k(x)`.
- **Part 2 (the author's point).**
  - *Degree.* A root `y` of degree `d < c` would give `m[y] ≠ 0` in the torsion-free group `Γ_d`, contradicting
    `z ∈ γ_c ⊆ γ_{d+1}`. So `[z] = m[y]` in `Γ_c`.
  - *The lattice.* After `K ≥ dim V_nil` steps, `Φ_c^K[x]` lies in `L = V_inv ∩ Γ_c`, and it is nonzero by
    hypothesis.
  - *Roots.* By persistence, `φ^k(x) = y^p` with `k ≥ K`. Then `p[y] ∈ L` forces `[y] ∈ V_inv`, and so `[y] ∈ L` by
    saturation.
  - *Counting.* For `p ∤ D`, `Φ_c` is invertible on `L/pL`, so `Φ_c^K[x] ∈ pL`. So only the primes of `D` and of one
    fixed content are possible. Correct.
- **Part 3.** The degree is nondecreasing, and `P(x) = P(φ^{k_0}(x))` by persistence. Correct.
- **Part 4 (the author's point).**
  - The identification `gr F ≅ L(F_ab)` is natural for all homomorphisms of free groups: `gr(φ)` and `L(φ_ab)` are
    Lie maps that agree in degree 1. So `Φ_c = L_c(φ_ab)`.
  - `L_c(V) ⊆ V^{⊗c}` naturally. A tensor power of an injective map over a field is injective, so `Φ_c ⊗ Q` is
    injective.
  - Hence nothing sinks. Correct.
- **Calibration.** For `BS(1,m) = ⟨Z, t | t^{-1}xt = x^m⟩`, `P(x)` is the set of primes dividing `m = D`. That set is
  finite, as part 2 predicts, and `BS(1,m)` contains `Z[1/m]` but no `Z[1/P]` with `P` infinite.

## 3. Finitely generated metabelian groups have roots at only finitely many primes
- **Step 1.** `G'` is the normal closure of the lifted relators of a finite presentation of `Q = G/G'`. Conjugation
  acts through `Q`, so `M = G'` is a finitely generated `Z[Q]`-module.
- **Step 2.** Generic freeness over `A = Z` gives `M[1/a]` free over `Z[1/a]`.
- **Step 3.** An element of infinite order survives in `M[1/a]`.
  - For `q ∤ ae`, a `q`-th root `y` has image of order dividing `q` in `Q`, so the image is trivial and `y ∈ M`.
  - Then `q` divides the numerator of one fixed coordinate. Correct.
- **Step 4.** The image of `Z[1/P]` in `Q` is finitely generated and `q`-divisible for infinitely many `q`, so it is
  finite, of order `b`. Then `ι(b) ∈ G'` has infinite order and roots at every `q ∈ P`. Correct.
- **Addendum.**
  - The `Z^s`-parts of `x̄` and of `ȳ_q` vanish: `x̄`'s because it is divisible by infinitely many primes, `ȳ_q`'s
    because `q·ȳ_q = x̄` and `Z^s` is torsion-free.
  - Then `x^ε ∈ G'`, and item 1 applies. Correct.
- **Consequence.** This supports the lower bound "derived length `≥ 3`" in
  `z-localized-embeds-in-fg-rf-soluble-group`: the group `G_l` contains `Z_(l)`, and item 2 applies with `P` the
  primes other than `l`.

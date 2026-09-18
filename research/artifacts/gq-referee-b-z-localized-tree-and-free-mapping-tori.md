# Referee report (gq-referee-b, citation/hypothesis lens): Z_(l) on trees; free-group mapping tori

**Reviewed.** Both nodes and their routes are from lane gq-k2-q, read on origin/main (21ed703eb and later):
- `z-localized-fixes-a-vertex-or-end-of-every-tree` and its `-proof`;
- `free-group-mapping-tori-contain-no-z-localized` and its `-proof`.

**Verdict: PASS on both.** Every step is correct.

The textbook imports are Serre's *Trees* §I.6, Nielsen–Schreier and Magnus–Witt. I could not read any of them at
source: they are books, not open-access. The routes say "not re-read", and that stands. In place of the source
reading I checked each imported fact directly, recorded below, and every one holds as used.

Borisov–Sapir is context only. I checked it at its arXiv abstract.

Three wording fixes, none of which changes a conclusion:
- statement 3 of the tree lemma overclaims about edge stabilizers;
- the example chain for `Z[1/P]` does not exhaust it;
- one uncited remark in `distinct_from`.

## 1. `z-localized-fixes-a-vertex-or-end-of-every-tree`: PASS

**Imports, checked directly (Serre not read at source).**
- *Elliptic/hyperbolic dichotomy without inversions, and `ℓ(g^q) = q ℓ(g)`.* A hyperbolic `g` translates its axis
  by `ℓ(g)`. For every vertex `x`, `d(x, g^q x) = 2 d(x, axis) + q ℓ(g)`, so the minimum displacement of `g^q` is
  `q ℓ(g)`.
- *The fixed set of an elliptic element is a nonempty subtree.* This is standard, and holds without inversions.
- *Nested nonempty subtrees `S_1 ⊇ S_2 ⊇ ...` with empty intersection determine an end.* Proof:
  - Let `p_k` be the projection of a base vertex `x` onto `S_k`. Every geodesic from `x` to a point of `S_k` passes
    through `p_k`, so `[x,p_k] ⊆ [x,p_(k+1)]`.
  - If `d(x,S_k)` were bounded, `p_k` would be eventually constant. That point would lie in every `S_k`,
    contradicting the empty intersection.
  - So the segments `[x,p_k]` exhaust a ray. `S_k ⊇ [p_k, p_j]` for all `j ≥ k`, so `S_k` contains the tail of the
    ray from `p_k`.
  - **Correct.** The pointer "Serre, *Trees*, §I.6.5" was not read by me either. Treat it as an unverified pointer,
    not as the justification.

**Part 1: correct.** If `a` were hyperbolic, every root `c` of `a` would be hyperbolic too (an elliptic `c` has an
elliptic power). Then `ℓ(a) = q ℓ(c) ≥ q` for infinitely many `q`, which is impossible.
- For a general `b ∈ A`: `A` has rank one, so `r b = n a`.
- If `b` were hyperbolic, `r b` would be hyperbolic, which forces `n ≠ 0`, but `n a` is elliptic.
- If `n = 0`, then `b = 0`, since `A` is torsion-free.

**Part 2: correct.** Each finitely generated subgroup of `Q` is cyclic, so `Fix(A_k) = Fix(generator)`.
- An element fixing `v_j` and `ω` fixes the unique ray from `v_j` to `ω`, so it fixes `v_(j+1)`.
- Hence the groups `A ∩ Stab(v_j)` increase from the start, not only eventually.

**Part 3: correct.** It is the Bass–Serre dictionary: vertex stabilizers are conjugates of vertex groups, and
`Stab(v_j) ∩ Stab(v_(j+1))` is an edge stabilizer.

**Wording fixes.**
- **W1 (statement 3 overclaims).** "Consecutive ones lie in a common edge stabilizer", read literally, puts both
  `A ∩ Stab(v_j)` and `A ∩ Stab(v_(j+1))` in `Stab([v_j,v_(j+1)])`.
  - The proof gives only the smaller one: `A ∩ Stab(v_j) ⊆ Stab(v_j) ∩ Stab(v_(j+1))`.
  - The larger one fails within the node's own hypotheses.
    - Take `A = Q = ∪_n (1/n!)Z` acting on the tree of this increasing union. Its vertices are `⊔_n Q/G_n` with
      `G_n = (1/n!)Z`, and its edges join `g + G_n` to `g + G_(n+1)`.
    - Along the ray `v_n = G_n`, `A ∩ Stab(v_(n+1)) = G_(n+1)` does not fix `v_n`, since `Stab(v_n) = G_n`.
    - The same happens for `Z[1/m]` in `BS(1,m)` along `v_j = t^j⟨a⟩`: `Stab(v_j) = ⟨a^(1/m^j)⟩`.
  - Suggested wording: "each `A ∩ Stab(v_j)` lies in the edge stabilizer `Stab([v_j, v_(j+1)])`. So `A` is the
    increasing union of its intersections with the edge stabilizers along the ray." That is what the title says,
    and it is what the proof shows.
- **W2 (the example chain for `Z[1/P]` is wrong).** The route takes `A_k = ⟨1/m_k⟩`, where `m_k` is the product of
  the first `k` primes of `P`.
  - This union contains only fractions with squarefree denominators, so it misses `1/p^2`.
  - Take `m_k = (p_1⋯p_k)^k` instead.
  - The argument itself is unaffected: any countable `A ≤ Q` is an increasing union of cyclic subgroups.

## 2. `free-group-mapping-tori-contain-no-z-localized`: PASS

**Bass–Serre bookkeeping (requested): all correct.** Convention: for `H*_A` with `t^(-1) A t = B ⊆ H`, the edge
`gA` joins `gH` to `gtH`. This is legitimate because `A ⊆ H ∩ tHt^(-1)`, which holds since `t^(-1)At ⊆ H`. Here
`H = A = F` and `B = φ(F)`.

| Claim | Check |
|---|---|
| `e_0` joins `F` and `tF`, and `Stab(e_0) = F` | `Stab(e_0) = F ∩ tFt^(-1) = F`, because `t^(-1)Ft = φ(F) ⊆ F` gives `F ⊆ tFt^(-1)`. |
| The up-neighbour is unique | The edges with origin at the vertex `F` are the `hF`, `h ∈ F`, which are all the single coset `F`. So there is exactly one, to `tF`. This is well defined: `ghtF = gt·φ(h)F = gtF`. |
| Down-neighbours are indexed by `F/φ(F)` | The edges ending at `F` are `ht^(-1)F`, `h ∈ F`. Two of them coincide exactly when `h'^(-1)h ∈ t^(-1)Ft = φ(F)`, so they are indexed by `F/φ(F)`. The origin `ht^(-1)F` has stabilizer `hφ(F)h^(-1) ⊆ F`. |
| Rays without backtracking go up forever, or up finitely often and then down forever | After one down step the only way up is back, so every later step goes down. Stabilizers decrease going down. |

- The node states the edge set and stabilizers but not the index set `F/φ(F)` explicitly. Adding it would help.
- For an automorphism `φ`, there is one down-neighbour and the tree is a line, which is consistent.

**Parts 1–4: correct.**
- **Part 1.**
  - A fixed vertex, or a down-going tail, puts `A` in a conjugate of `F`, where (NS) makes it cyclic.
  - `A` is not cyclic: in `Z`, a nonzero element is divisible by only finitely many primes.
  - `t^(-k) y t^k = z` gives `z^q = φ^k(x)` from `t^(-1) x t = φ(x)`.
- **Part 2.**
  - *Degree step.* A root of `z ≠ 1` is `≠ 1`, so it has a finite degree. This uses `∩ γ_c = 1`.
    - Degree `d < c` is excluded because `Γ_d` is torsion-free.
    - Degree `d > c` is excluded because `γ_d ⊆ γ_(c+1)`.
  - *The lattice `L`.* `V_inv` is a rational subspace, so `L = V_inv ∩ Γ_c` is a full lattice in it, saturated and
    stable. Hence `D ≠ 0`.
  - *Landing in `L`.* `Φ_c^K` kills `V_nil`, so `Φ_c^K[x] ∈ L`.
  - *Counting.* Invertibility modulo `p` for `p ∤ D` gives the bound `P(x) ⊆ primes(D) ∪ primes(content)`.
- **Part 3.** `φ` is injective, so the degrees are finite and nondecreasing. `P(x) = P(φ^(k_0)(x))` because roots
  persist.
- **Part 4.** The (MW) functoriality used is exactly this: `Φ_c ⊗ Q` is the restriction of `(φ_ab ⊗ Q)^(⊗c)`.
  - `gr(F) ⊗ Q` is generated in degree 1.
  - The Magnus–Witt map `gr(F) ⊗ Q → T(V)` is a Lie homomorphism that is the identity in degree 1.
  - So it intertwines `gr(φ)` with `T(φ_ab)`, because both composites are Lie homomorphisms that agree on
    generators.
  - The only deep input is injectivity of that map. Together with `Γ_c` torsion-free of finite rank and
    `∩ γ_c F = 1`, this is textbook (Magnus; Witt), and none of it was read at source.

**Borisov–Sapir (context only).** arXiv:math/0309121, *Polynomial maps over finite fields and residual finiteness of
mapping tori of group endomorphisms*. Abstract: "We prove that every mapping torus of any free group endomorphism is
residually finite." **Supports** the setting line. The route does not use it.

**Wording fix.**
- **W3.** The `distinct_from` entry says mapping tori of free groups are "not linear in general". This has no
  citation. It needs a source, such as a named non-linear example, or should be softened to "not known to be
  linear". It is a `distinct_from` annotation only, so this is non-blocking.

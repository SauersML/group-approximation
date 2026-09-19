---
rg: 2
id: boone-higman-is-equality-of-two-sigma-3-index-sets-proof
kind: route
title: Proof of the index-set form of Boone-Higman via a cofinite/noncomputable splitting and circulant graph wreath products
target: boone-higman-is-equality-of-two-sigma-3-index-sets
requires:
  - simple-envelope-forces-solvable-word-problem
  - clapham-fp-embedding-preserves-word-problem
---

Lane proof, not reviewed.

## Upper bounds (item 1)

- `w =_{G_i} 1` is `Σ_1`, uniformly in `i`.
- `i ∈ DEC` iff `∃e [φ_e` is total, and for every `w`, `φ_e(w)=0 → w=1` and
  `φ_e(w)=1 → w≠1]`. The bracket is `Π_2`, so the condition is `Σ_3`.
- `i ∈ EMB` iff `∃(Q,φ)` (a finite presentation `Q` with words `φ(a), φ(t)`) such
  that:
  - (hom) `∀r ∈ W_i`, `φ(r) =_Q 1`, which is `Π_2`;
  - (simple, nontrivial) `Q ≠ 1`, which is `Π_1`, and
    `∀u (u =_Q 1 ∨ Q/⟨⟨u⟩⟩ = 1)`, which is `Π_2`;
  - (injective, given simplicity) `∀w (w =_{G_i} 1 ∨ Q/⟨⟨φ(w)⟩⟩ = 1)`, which is
    `Π_2`.

  So `EMB` is `Σ_3`. The `fp` versions are the same, since a finite relator set
  makes (hom) `Σ_1`.

Inclusion `EMB ⊆ DEC` is Kuznetsov's theorem.

## Item 2

- `⇒`: if `i ∈ DEC`, then `G_i` is finitely generated with solvable word problem,
  so the conjecture embeds it in a finitely presented simple group.
- `⇐`: a finitely generated decidable `G` is recursively presented, and it embeds
  in a finitely presented decidable group by Clapham's theorem.
- The same argument works for the `fp` sets.

## Splitting lemma

**Claim.** There is a computable `i ↦ u(i)` with the following properties.
- If `W_i` is cofinite, then `U := W_{u(i)}` is cofinite.
- If `W_i` is coinfinite, then `U` is noncomputable.
- `U ⊆ N_{≥1}`.

**Construction.** Let `⟨n,m⟩ ≥ 1` be a computable pairing and `K` the halting set.
Enumerate `⟨n,m⟩` into `U` when
- `n ∈ K`, or
- `|[0,m] ∖ W_i| < n`.

The second event is `Σ_1`: the set `[0,m] ∖ W_i` only shrinks as `W_i` is
enumerated. So `U` is c.e., uniformly in `i`.

**Cofinite case.** Let `N = |N ∖ W_i|`.
- For `n > N`, every `⟨n,m⟩ ∈ U`, since `|[0,m]∖W_i| ≤ N < n`.
- For `n ≤ N`: if `n ∈ K`, column `n` is full. Otherwise it is finite, because
  `|[0,m]∖W_i| = N ≥ n` for all large `m`.

So all but finitely many columns are full, and the remaining finitely many columns
are each full or finite. Hence `U` is cofinite.

**Coinfinite case.**
- `|[0,m]∖W_i| → ∞`, so for `n ∉ K` column `n` is the finite initial segment
  `{⟨n,m⟩ : m < m_n}`, while for `n ∈ K` it is full.
- If `U` were computable, then `n ∉ K ⟺ ∃m ⟨n,m⟩ ∉ U` would make `N ∖ K`
  c.e. That is false, so `U` is noncomputable.

## The family `G_U`

For `U ⊆ N_{≥1}`, let `G_U = ⟨a, t | [a, t^k a t^{-k}] = 1 (k ∈ U)⟩`, and put
`a_j = t^j a t^{-j}`.

1. **Structure.** By Reidemeister–Schreier on the kernel of the `t`-exponent map,
   `G_U = A(Γ_U) ⋊ ⟨t⟩`.
   - `Γ_U` has vertex set `Z`, with `j ~ j'` iff `|j−j'| ∈ U`.
   - `t` acts by the shift `a_j ↦ a_{j+1}`.
2. **`U ≤_T WP`, uniformly.** Vertex generators of a right-angled Artin group
   commute iff they are adjacent. So `[a, a^{t^k}] = 1` in `G_U` iff `k ∈ U`.
3. **`WP ≤_T U`, uniformly.** Given `w` of length `n`:
   - reject if its `t`-exponent sum is nonzero;
   - otherwise rewrite `w` as a word in `a_j^{±1}` with `|j| ≤ n`;
   - decide it in the finite right-angled Artin group on the induced subgraph with
     vertices `[−n,n]`. Its edges are read from `U ∩ [1,2n]`. Induced
     subgraphs give retracts, so this equals triviality in `A(Γ_U)`.
4. **Uniformity.** A c.e. index for `U` gives a c.e. presentation of `G_U`,
   uniformly.

## Items 3–5

- **The map.** `i ↦` (the c.e. index of `G_{W_{u(i)}}`) is computable.
  - If `W_i` is cofinite, then `U` is cofinite, hence computable, and `G_U` is
    decidable by item 3.
  - If `W_i` is coinfinite, then `U` is noncomputable, so `WP(G_U)` is undecidable
    by item 2.
- **Completeness of `DEC`.** Hence `COF ≤_m DEC`. `COF` is `Σ_3`-complete (Rogers;
  Soare IV.3.5), so `DEC` is `Σ_3`-complete.
- **The fp version.** Compose with the uniform Clapham embedding, which preserves
  the Turing degree of the word problem. This is cited, not re-read. It gives
  `COF ≤_m DEC_fp`.
- **Item 4.** Under the conjecture, `EMB = DEC`.
- **Item 5.** If every cofinite `G_U` lies in `EMB`, then:
  - cofinite `W_i` gives `G_U ∈ EMB`;
  - coinfinite `W_i` gives an undecidable `G_U`, which lies outside `EMB` by
    Kuznetsov.

  So `COF ≤_m EMB`.

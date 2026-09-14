# sk-wp-embedding proposal: solvable word problem in the envelopes

Lane `sk-wp-embedding`, 2026-09-13. Line numbers are from the note on main at the time of writing
(`git show "${T}:simple_kazhdan_sofic_group.tex"`, 386 lines, the revision with `\section{Questions}`).
Status of every mathematical item: UNREVIEWED, landed at `bd68876d34` and `f416195bac`, queued with `sk-verify-4`.

## Recommendation

**Default: change nothing.** The note answers Brown, Ozawa and Pestov over the integers, where the acting group's
word problem is trivial and the existing corollary already says everything the reader needs. My results are about
envelopes over other acting groups, which the note does not carry.

**One clause, only if the residually finite embedding corollary goes in** (main's decision 22). That corollary would
say that every finitely generated residually finite group embeds in an infinite finitely generated simple Kazhdan
LEF group. Then append:

```latex
When $\Gamma$ is perfect, effectively residually finite and has solvable
word problem, the group containing it can be chosen with solvable word
problem; this applies to $\SL_n(\Z)$ for $n\ge3$.
```

- (c) Length: +3 source lines, about +2 printed lines, no new bibliography item.
- (d) Reader trade-off: the corollary becomes a statement about computable objects instead of an abstract embedding,
  at one clause, and it names a group the reader knows. The reader has to accept one new term, effective residual
  finiteness, which the sentence itself does not define; that is the cost.
- (e) Status: `perfect-erf-groups-have-decidable-simple-kazhdan-hosts` (established, unreviewed) with its route;
  it requires the reviewed `rf-groups-embed-in-simple-kazhdan-lef-groups` and
  `residually-finite-group-toeplitz-elementary-groups-lef-kazhdan`, and the new
  `crossed-product-el-word-problem-is-group-wp-plus-language`,
  `rf-toeplitz-subshift-has-computable-language` and `effectively-rf-groups-have-computable-chains`.

If the clause is used, the word "perfect" cannot be dropped: the general case is open
(`erf-groups-have-decidable-simple-kazhdan-hosts`), because the overgroup that puts a group inside a derived
subgroup is built coordinatewise in a product of finite symmetric groups and controls no word problem.

## Considered and not recommended

**N1. A general degree formula in the Word problems section.** The formula proved this run is

```text
WP(EL_n(LC(X,F_2) ⋊ Δ)) ≡_T WP(Δ) ⊕ L(X)
```

for every finitely generated acting group `Δ`, every subshift `X ⊆ A^Δ` and `n ≥ 3`; the note's corollary is the
case `Δ = Z`. Stating it would cost about 6 lines and would generalize a sentence in a direction the note never
takes. It belongs in Cairn (`crossed-product-el-word-problem-is-group-wp-plus-language`).

**N2. A Boone–Higman sentence in the Questions section.** The following is true and tempting:

```latex
Boone and Higman characterized the finitely generated groups with
solvable word problem as the subgroups of simple subgroups of finitely
presented groups. No infinite simple LEF group is finitely presented, so
the groups here sit outside that picture.
```

It is commentary on what the note is not, it needs a new reference, and it makes no statement about `G_X`. Left out.

**N3. Naming the decidable instance.** The note could say that the Fibonacci subshift gives a group with solvable
word problem. The current corollary already implies it through `L(X_\alpha) ≡_T \alpha`, and sk-open-3 owns the
Fibonacci material.

## What is settled behind the clause

- `WP(G) ≡_T WP(Δ) ⊕ L(X)` over any finitely generated acting group.
- A computable chain of finite-index normal subgroups, with decidable membership, exists exactly for effectively
  residually finite groups with solvable word problem; by Rauzy's Theorem 2, already imported on main in
  `rf-higman-embedding-for-decidable-groups-fails`, residual finiteness with a solvable word problem does not
  suffice.
- The Toeplitz subshift of such a chain has decidable language, so the envelope's word problem is solvable.
- Converse: a finitely generated subgroup of a finitely generated group with solvable word problem has solvable word
  problem, and a subgroup of a LEF group is LEF. The class of groups with such envelopes is therefore between the
  perfect effectively residually finite groups with solvable word problem and the LEF groups with solvable word
  problem; it is not inside the residually finite groups, since `[[T]]'` embeds in `G_X` itself.

Details and proofs: `research/artifacts/sk-wp-embedding-decidable-envelopes-2026-09-13.md`.

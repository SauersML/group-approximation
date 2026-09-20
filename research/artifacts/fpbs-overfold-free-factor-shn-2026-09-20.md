# The image subgraph is a free factor: SHN proves the Z = X branch of (RI_B), refutes the image claim, and sandwiches (RI) between two fibre statements

Worker swarm-0917-w21-w21-fp-follow (host-geometry), September 20, 2026.
Target: `fpbs-mal-overfold-merges-never-help` (O), through the chain
`(RI_{L_j}) => (G_j) => (O)` (w17 Prop 3). Follows the w20 census
`research/artifacts/fpbs-overfold-malnormal-host-census-2026-09-20.md`,
whose next step 1 was "prove the image claim (A) at k = 1 for all B".

Code and runs: `experiments/fpbs-overfold-image-claim-2026-09-17/`
(imports the census kernel from
`experiments/fpbs-overfold-malnormal-host-census-2026-09-17/`).

Status: **OPEN.** (RI_B) is not proved. What is proved is one of its two
branches, for every k, for every rank-2 host; the other branch is isolated
as a fibre statement (Fib) that is equivalent to (RI) up to a factor 2.

## 0. Notation

- `X ≤ B ≤ F = F(a,b)`, f.g., `X ≠ 1`. `Γ_X`, `Γ_B` based folded
  (Stallings) graphs, `f : Γ_X → Γ_B` the immersion.
- A k-pair join: `J = π_1 fold(Γ_X / (u_1~w_1, ..., u_k~w_k))`,
  `q : Γ_X → Γ_J` the fold map. Then `J = <X, g_1, ..., g_k>` with
  `g_i = t_{u_i} t_{w_i}^{-1}`, so `rk(J:X) ≤ k`.
- `P` = based component of the pullback `Γ_J ×_R Γ_B`, `Y = π_1 P = J ∩ B`.
- `m = (q, f) : Γ_X → P`, an immersion. `Z = π_1(m Γ_X)`, the fundamental
  group of the image subgraph. Equivalently
  `Z = π_1 fold(Γ_X / (ker q ∩ ker f))`, and `X ≤ Z ≤ Y`.
- (RI_B): `rk(Y : X) ≤ rk(J : X)`. (RI,C)_B: `rk(Y:X) ≤ C · rk(J:X)`.
  By w17 Prop 3 (claim file, Attempts), (RI,C)_{L_j} gives
  `deep ≥ law / C`, which is enough for the floor.
- (A) image claim: `Z = Y`. (B) one-fibre claim: `Z` is a one-pair fold
  of `Γ_X` along one `m`-fibre pair.
- Branches: **ZX** `Z = X`; **ZY** `Z = Y`; **MIX** `X < Z < Y`.
- `r̄(A) = max(rk A − 1, 0)`.

## 1. Summary

1. **Theorem 1 (proved).** If `rk B = 2`, then for every join,
   `rk(Y:X) ≤ rk(Z:X) + rk J − rk Z ≤ rk(Z:X) + rk(J:Z)`.
2. **Corollary 2 (proved): (RI_B) holds on the ZX branch.** For every k
   and every rank-2 host `B` (malnormal or not): if `Z = X`, then
   `rk(Y:X) ≤ rk J − rk X ≤ rk(J:X) ≤ k`.
3. **Corollary 3 (proved): the fibre sandwich.** Put
   (Fib)_B: `rk(Z:X) ≤ rk(J:X)`. Then (RI_B) ⇒ (Fib)_B for every host,
   and (Fib)_B ⇒ (RI,2)_B for rank-2 hosts. So, for the route,
   **(RI,2)_{L_j} reduces to the fibre statement (Fib)_{L_j}**. That
   statement only sees the image subgraph `f(Γ_X)`.
4. **The image claim (A) is false (proved by example).** It fails at k = 1
   for a malnormal rank-2 host and infinite-index `X`, including when
   `Γ_X → Γ_B` is onto. All k = 1 failures of (A) on rank-2 hosts in the
   runs are ZX, so Corollary 2 covers them. Step 1 of w20 is dead as
   stated; its job is done instead by Theorem 1.
5. **Why (A) looked true (proved).** If `[B:X] < ∞`, (A) holds for every
   join and every k (Lemma 5). All earlier (A) data at k = 1 were in this
   regime or in the φ-level regime.
6. **Rank 3 kills both branches (computed).** On malnormal rank-3 hosts
   there are k = 1 violations of (RI) in all three branches, including
   ZY with `X` normal of index 6 in `B` and `Y = B`. The ZX ones live in
   the SHN slack that rank 3 allows (typically `rk X, J, Y = 1, 2, 3`, so
   `rk Y > rk J`). So rank 2 must be
   used on both branches, and on the ZY branch malnormality too (the w19
   normal S3 example, reproduced).
7. **Branch census (computed).** On rank-2 hosts at k = 1, MIX never
   occurred (20966 joins with `Y ≠ X`: random malnormal, random
   non-malnormal, and `X ≤ L_2` inside `B = L_1`). At k = 2 all 132 MIX joins are
   certified by Theorem 1. The (G_1) regime (`X` f.i. in `L_2`,
   `B = L_1`, k = 2) is 404 ZX + 23023 ZY, all ZX now proved.

## 2. Theorem 1 and its proof

**Lemma 4 (free factor).** `Z` is a free factor of `Y`. Hence
`rk(Y:Z) ≤ rk Y − rk Z`.

*Proof.* `m Γ_X` is a connected subgraph of `P` that contains the base
vertex. Extend a maximal tree of `m Γ_X` to a maximal tree of `P`. The
edges of `P` outside the tree then form a basis of `Y`, and the edges of
`m Γ_X` outside the tree form a basis of `Z`, which is a subset.
Write `Y = Z * W` with `rk W = rk Y − rk Z`. Then `Y = <Z, basis of W>`,
which gives the bound. ∎

The identification `Z = π_1 fold(Γ_X/(ker q ∩ ker f))` holds because
`m Γ_X` is the quotient of `Γ_X` by `ker m = ker q ∩ ker f` on vertices,
with equal-label edges merged, and it is already folded, being a subgraph
of the folded graph `P`. Since `m_*` is the inclusion on `π_1`,
`X ≤ Z`.

**SHN input (background).** Friedman and Mineyev proved the Hanna Neumann
conjecture, `r̄(H ∩ K) ≤ r̄(H) r̄(K)`, and its strengthened form, a sum
over double cosets. Only the one-term form is used here. For `rk B = 2`
and `Y ⊇ X ≠ 1` it gives `rk Y ≤ rk J`.

**Theorem 1.** If `rk B = 2`, then for every k-pair join,
`rk(Y:X) ≤ rk(Z:X) + (rk J − rk Z) ≤ rk(Z:X) + rk(J:Z)`.

*Proof.* Relative rank is subadditive along a chain:
`rk(Y:X) ≤ rk(Y:Z) + rk(Z:X)`. Apply Lemma 4 and then SHN:
`rk(Y:Z) ≤ rk Y − rk Z ≤ rk J − rk Z`. The last step is trivial:
`rk J ≤ rk Z + rk(J:Z)`, since `Z ≤ J`. ∎

**Defect form.** Put `d(A:X) = rk X + rk(A:X) − rk A ≥ 0`, which is 0
iff `X` together with `rk(A:X)` elements forms a basis of `A`. Then
Theorem 1 reads

    rk(Y:X) ≤ rk(J:X) − d(J:X) + d(Z:X).

So (RI_B) can fail only when the image subgraph `Z` sits over `X` with
more rank defect than `J` does.

**Corollary 2 (ZX branch).** If `Z = X` and `rk B = 2`, then
`rk(Y:X) ≤ rk J − rk X ≤ rk(J:X) ≤ k`. This is (RI_B) with no loss, at
every k, with no malnormality assumption.

**Corollary 2' (MIX at k = 1 is rigid).** Suppose `k = 1`, `rk B = 2`,
and `X < Z < Y`. Then `rk Y = rk J = rk Z + 1`. So SHN is an equality at
the identity double coset, and the strengthened form forces
`J ∩ cBc^{-1}` to be cyclic for every `c ∉ JB`.

*Proof.* `J = <Z, g>` gives `rk J ≤ rk Z + 1`. Since `Z` is a proper free
factor, `rk Y ≥ rk Z + 1`, and SHN gives `rk Y ≤ rk J`. Then
`r̄(J ∩ B) = r̄(J)`, and in the strengthened sum
`Σ_c r̄(J ∩ cBc^{-1}) ≤ r̄(J)` every other term is 0. ∎

**Corollary 3 (fibre sandwich).**
- (RI_B) ⇒ (Fib)_B, for every host `B`. Take `Y = Z * W` and the
  retraction `ρ : Y → Z` that kills `W`. It fixes `Z ⊇ X`. If
  `Y = <X, y_1..y_s>`, then `Z = <X, ρ y_1, ..., ρ y_s>`. So
  `rk(Z:X) ≤ rk(Y:X)`.
- (Fib)_B ⇒ (RI,2)_B, for rank-2 `B`. By Theorem 1,
  `rk(Y:X) ≤ rk(Z:X) + rk(J:Z) ≤ rk(J:X) + rk(J:X)`, using `Z ⊇ X`.

On the ZY branch, (Fib) is (RI) itself. On the ZX branch it is empty.

**Reduction to the image host.** `m Γ_X` lies in the component of
`Γ_J × f(Γ_X)`. Its fundamental group `B_X = π_1 f(Γ_X)` is a free factor
of `B`, by the argument of Lemma 4, and it is malnormal in `F` if `B` is.
So `Z` and (Fib) depend on `B` only through `B_X`, onto which `Γ_X`
surjects. If `rk B_X ≤ 1`, then `Z` is cyclic and (Fib) holds trivially.
So (Fib) for rank-2 hosts reduces to the case where
`Γ_X → Γ_B` is onto, with `B` of rank 2. Caution: this is a
reduction of (Fib), not of (A). By §3, the image claim fails even for
onto hosts.

## 3. The image claim (A): where it holds and where it fails

**Lemma 5 (proved).** If `X` is not contained in any proper free factor
of `Y`, then `Z = Y`. In particular (A) holds for every join, at every k,
whenever `[B:X] < ∞`.

*Proof.* By Lemma 4, `Y = Z * W` with `Z ⊇ X`. If `W ≠ 1`, `Z` is a proper
free factor containing `X`. If `[B:X] < ∞`, then `[Y:X] < ∞`. But a
proper free factor `Z` has infinite index in `Y`: for `1 ≠ w ∈ W`, the
cosets `w^n Z` are pairwise distinct, since `Z ∩ W = 1`. ∎

So the w20 observation "(A) never fails at k = 1" is mostly explained by
the regime.
- In the `L1` and random-host censuses, `X` had finite index in `B`, so
  Lemma 5 applies.
- In the L1overL2 regime, `X` has finite index in `L_2` but infinite
  index in `B = L_1`, so Lemma 5 does not apply. There (A) held at
  k = 1 (13062 joins here, all ZY) but fails at k = 2: 22 cases in w20,
  and 404 ZX here (§5).

**(A) is false for infinite-index X on malnormal rank-2 hosts.**
Both examples are checked by `a_refute.py`.

1. `B = <bab, b²a⁻²b⁻¹a⁻¹>` (`bab`, `bbAABA`), malnormal, and
   `X = <b⁻¹a⁻¹b⁻¹>` (`BAB`), with the pair (0,1).
   - Ranks: `rk X, J, Y, Z = 1, 2, 2, 1`, and `Y = B`.
   - So `Z = X < Y = B`, and (A) fails.
   - Here `f(Γ_X)` is the single loop, so `B_X = X`.
   - (RI) holds: `rk(Y:X) = 1` (certificate "arc"), as Corollary 2
     predicts.
2. An onto host (`surj_check.py 3 150 mal2 sub 1`, 1 of 195 joins):
   - `B = <bABaB, Abaa>`, malnormal.
   - `X = <bABaBAABabAbaB, bAbaBAABabAbaB, bAbbaB>`, pair (1,5).
   - `rk B_X = 2`, so `Γ_X → Γ_B` is onto the core.
   - `rk X, J, Y, Z = 2, 3, 3, 2`, class ZX, and `J ∩ B_X = Y ≠ Z`.
   - (RI) holds, by Corollary 2.

In `ab_split.py` (seed 7), (A) fails in:

| hosts | joins with Y ≠ X | (A) fails |
|---|---|---|
| malnormal rank 2 | 871 | 52 |
| non-malnormal rank 2 | 2352 | 950 |
| malnormal rank 3 | 1737 | 217 |

For finite-index `X` it fails in 0 cases, as Lemma 5 requires. Every
rank-2 (A)-failure with k = 1 in `dichotomy.py` is of class ZX, so
Corollary 2 proves (RI) there. **The w20 step 1 is dead as stated.** The
ZX part of its job is done by Theorem 1. What is left is the ZY part,
which is exactly (Fib).

## 4. Rank 3 breaks every branch; the normal layer

**Rank 3 (computed, `dichotomy.py 11 1500 mal3 sub 1`).** There are
4594 joins with `Y ≠ X` on random malnormal rank-3 hosts at k = 1:
496 ZX, 4056 ZY and 42 MIX. 182 of them violate `rk(Y:X) ≤ 1`: 125 ZX,
15 ZY and all 42 MIX. SHN with factor `r̄(B) = 2` allows `rk Y > rk J`,
and that happens in 486 joins. A typical ZX violation is
`B = <AABabba, BBAbABB, abaBA>`, `X = <abABA>`, pair (0,2), with
`rk X, J, Y, Z = 1, 2, 3, 1`. Here `rk Y − rk J = 1 = r̄(B) − 1` is
exactly the SHN slack. So Theorem 1 is sharp in its use of rank 2.

**The normal finite-index layer.** Let `X = ker(B → G)` with `G` finite.
By Lemma 5, `Z = Y` for every join: this layer is all ZY, and there
(Fib) = (RI). Put `H = Y/X ≤ G`. Since `X ⊴ Y`, `rk(Y:X) = d(H)`, the
minimal number of generators. So at k = 1:

    (RI_B) on the normal layer  ⟺  H is cyclic for every g.

`kern.py` tests every one-pair join exactly, with `4 ≤ |G| ≤ 60`
(regular actions of random permutations):

- **Malnormal rank 3: violations.** `B = <Abaab, aaba, BaaB>`, `|G| = 6`,
  pair (0,6), `Y = B`, `H = G = S_3`. Also
  `B = <baBBabb, AbAAA, bbAB>`, `|G| = 24`, pair (0,24), `Y = B`, and the
  pair (6,25) gives a proper `Y` of rank 5. There are 12 KVIOL lines in
  `kern_mal3_s21/s22.txt`.
- **Non-malnormal rank 2: violations.** `B = <BaaB, BBaa>` and
  `B = <abABA, baaaB>`, with `G = S_3`, pair (0,6), `Y = B`,
  `rk X, J, Y = 7, 2, 2` (`kviol_check.py`). This is the w19 mechanism
  (`B = <b, ab²a⁻¹>`, `X = ker(B → S_3)`) on new hosts.
- **Malnormal rank 2:** see §5 for the counts; there were no violations.

So on the ZY branch, rank 2 **and** malnormality are both needed, while
on the ZX branch neither malnormality nor finite index is needed.

**Proved facts on the normal layer** (partial; they do not close it).
Write `J = <X, g>`.
1. If `g ∈ B`, then `Y = <X,g>` and `H = <ḡ>` is cyclic.
2. Let `N = ⟨⟨X⟩⟩_J`. Then `J/N = <gN>` is cyclic, so `Y/(Y ∩ N)` is
   cyclic. Hence `Y ∩ N = X` suffices for H to be cyclic.
3. Suppose `Y = B`, i.e. `J ⊇ B`, and `G ≠ 1`, with `rk B = 2`. Then
   `J = <B, g>` has rank exactly 2 and properly contains `B`.
   - `J ≠ B * <g>`: otherwise the map `J → G` that kills `g` kills
     `<X, g> = J`, so it kills `B`, and `G = 1`.
   - A 3-generated group of rank 3 is freely generated by those
     generators (Hopficity), so `rk J ≤ 2`.
   - `[J:B] = ∞`, by the Schreier formula: a proper subgroup of index
     `n ≥ 2` in a rank-2 free group has rank `n + 1 ≥ 3`.
   So a violation with `Y = B` on a rank-2 host needs a rank-2 group `J`
   of infinite index over `B`, generated by `X` and one element, with
   `B/X` not cyclic. The non-malnormal examples above realise exactly
   this configuration: `rk J = 2`, and `Γ_J` has 2 vertices. Malnormality
   must therefore enter through the configuration itself, not through
   ranks or indices.
4. **Dehn-filling remark (background, not a proof).** If `B` is
   malnormal in `F`, then `Y = J ∩ B` is malnormal in `J`: for
   `j ∈ J \ Y` we have `j ∉ B`, so `Y ∩ jYj^{-1} ⊆ B ∩ jBj^{-1} = 1`.
   Both groups are f.g. subgroups of a free group, hence quasiconvex.
   The Dehn filling theorem (Osin; Groves–Manning) then applies to `J`,
   relatively hyperbolic with respect to `Y`: there is a finite set
   `S ⊂ Y \ 1` such that `⟨⟨X⟩⟩_J ∩ Y = X` whenever `X ⊴ Y` avoids `S`.
   With fact 2, this gives `H` cyclic. The catch is that `S` depends on
   `J = <X, g>`, which depends on `X`. So this proves the normal-layer
   instance only in a non-uniform form: for fixed `(J, Y)` and deep
   enough `X`. Making the depth uniform over the one-pair joins of `X`
   is one concrete way to attack the open core.

## 5. Branch census

`dichotomy.py`, seed 11, 1500 instances per row. Columns: joins with
`Y ≠ X`, then the three branches, then the k = 1 violations of
`rk(Y:X) ≤ 1` (exact, via `relrank_le1`).

| host B | X | k | Y ≠ X | ZX | ZY | MIX | `rk Y > rk J` | viol (k=1) |
|---|---|---|---|---|---|---|---|---|
| random malnormal rank 2 | sub | 1 | 2110 | 120 | 1990 | 0 | 0 | 0 |
| random non-malnormal rank 2 | sub | 1 | 5794 | 2234 | 3560 | 0 | 0 | 0 |
| `L_1` | sub of `L_2` | 1 | 13062 | 0 | 13062 | 0 | 0 | 0 |
| random malnormal rank 3 | sub | 1 | 4594 | 496 | 4056 | 42 | 486 | 182 |
| random malnormal rank 2 | sub | 2 | 6957 | 1172 | 5653 | 132 | 0 | – |
| random malnormal rank 2 | f.i. | 2 | 7733 | 0 | 7733 | 0 | 0 | – |
| random non-malnormal rank 2 | f.i. | 2 | 8588 | 0 | 8588 | 0 | 0 | – |
| `L_1` | f.i. in `L_2` | 2 | 23427 | 404 | 23023 | 0 | 0 | – |

- At k = 2, all 132 MIX joins have `rk(Z:X) = 1` (certificate "pair")
  and `rk Y − rk Z = 1`. So Theorem 1 gives `rk(Y:X) ≤ 2 = k`
  (`mix_check.py`, tally `{('pair', 1, True): 132}`).
- The k = 1 runs with `X` of finite index in `L_2` (for `B = L_1`) and in
  `L_3` (for `B = L_2`) did not finish in this session. Their files
  `out/dich_L1overL2_fi_k1.txt` and `out/dich_L2overL3_fi_k1.txt` are
  empty, which means no violation and no MIX was printed before they
  were stopped. No summary line was printed, so they count only as
  partial evidence.
- The w20 census found 22 (A)-failures at k = 2 for `X` of finite index
  in `L_2`. All of them had `Z = X`, so they are now proved instances of
  (RI), by Corollary 2.

Normal layer (`kern.py`, exact over all one-pair joins):

| host B | runs | inst | Y ≠ X | Y = B | viol |
|---|---|---|---|---|---|
| malnormal rank 2 | seed 31 (cap 100) | 33 | 174 | 3 | 0 |
| malnormal rank 2 | seed 32 (cap 100) | 132 | 698 | 9 | 0 |
| non-malnormal rank 2 | seed 33 (cap 100) | 138 | 1305 | 31 | 10 |
| malnormal rank 3 | seeds 21, 22 (partial) | – | – | – | 12 lines |

`ab_split.py` (seed 7, 600 instances) with `X` a point stabiliser, which
is of finite index but not normal: 0 violations on rank-2
non-malnormal, rank-3 malnormal and rank-3 non-malnormal hosts. So
normality, i.e. regular covers, is where the ZY failures live in these
samples.

## 6. What is left, precisely

- **Established.**
  - Lemma 4, Theorem 1 and the defect form.
  - Corollary 2: (RI_B) on the ZX branch, for every k and every rank-2
    `B`. Corollary 2': rigidity of MIX at k = 1.
  - Corollary 3: (RI_B) ⇒ (Fib)_B ⇒ (RI,2)_B, and the reduction of (Fib)
    to the image host `B_X`.
  - Lemma 5: (A) holds when `X` lies in no proper free factor of `Y`,
    in particular at finite index.
  - The explicit refutations of (A), including one on an onto host, and
    the rank-3 kernel violations of (RI) on the ZY branch. These are exact
    computations.
- **Not established.** (Fib)_{L_j}, hence neither (RI,2)_{L_j} nor (G_j)
  nor (O). Also not the k = 1 dichotomy `Z ∈ {X, Y}` for rank-2 hosts
  (data only; Corollary 2' is the proved part).
- **The open core, in its sharpest form.** (Fib) on the ZY branch:
  if `Γ_X → P` is onto the core of `P`, then `rk(Y : X) ≤ rk(J : X)`.
  Its simplest instance is the normal layer at k = 1: for a malnormal
  rank-2 `B` and `X = ker(B → G)`, the image of `<X, g> ∩ B` in `G` is
  cyclic. Rank-3 malnormal and rank-2 non-malnormal hosts both violate
  this instance (§4). So any proof must use rank 2 and malnormality
  together, on the fibre `ker q ∩ ker f`.
- **Dead approaches.**
  - The image claim (A) as a route to (RI): false, §3.
  - Any proof of (Fib)_B that is valid for all rank-2 hosts `B`, i.e.
    that does not use malnormality. (Fib) fails for the non-malnormal
    rank-2 hosts of §4, where `X` is normal of index 6 and `Y = Z = B`.
    SHN, Lemma 4, Lemma 5 and the rank and index facts of §4 all hold
    there. Likewise any proof that does not use rank 2 fails on the
    malnormal rank-3 kernels. This extends the w17 obstruction list
    (claim file, Attempts) to the fibre statement.
- **Most promising next step.** Prove the normal-layer instance. The
  configuration of §4 fact 3 is `B ⊊ J`, both of rank 2, with
  `J = <X, g>` and `G = B/X` non-cyclic. Show that malnormality of `B`
  forbids it, for example through the strengthened SHN sum for
  `(J, B)`, all of whose non-identity terms must vanish when
  `r̄(J ∩ B) = r̄(J) = 1`. The general `Y ⊊ B` case reduces, through
  fact 2, to showing `⟨⟨X⟩⟩_J ∩ B = X`.

## 7. Reproduction

All commands run from `experiments/fpbs-overfold-image-claim-2026-09-17/`.
The kernel is imported from `../fpbs-overfold-malnormal-host-census-2026-09-17/census.py`.

- (A)/(B) split: `python3 ab_split.py 7 600 R M X` with `R` in {2,3},
  `M` in {0,1} and `X` in {fi, sub}. Outputs are `out/ab_rR_mM_X.txt`.
- Branch census: `python3 dichotomy.py 11 1500 HOST XMODE K`. Outputs
  are `out/dich_HOST_XMODE_kK.txt`.
- MIX certificates: `python3 mix_check.py out/dich_mal2_sub_k2.txt mal2 2`.
- Onto hosts: `python3 surj_check.py 3 150 mal2 sub 1`.
- Explicit (A) refutations: `python3 a_refute.py`.
- Normal layer: `python3 kern.py SEED TRIALS HOST CAP`. Outputs are
  `out/kern_*.txt`. The non-malnormal violations are rechecked by
  `python3 kviol_check.py`.

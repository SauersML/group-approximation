# Overfold versus lawful merges on other nested pairs: the rank-3 obstruction and the inertia reduction

Worker swarm-0917-w17-w17-fp-follow (calibration), September 19, 2026.
Target: `fpbs-mal-overfold-merges-never-help`, statement (O):
`deep_j(Q) = law_j(Q)`, and its weak form `deep_j ≥ c · law_j`.
Scripts and outputs: `experiments/fpbs-overfold-other-chains-2026-09-17/`.

Status: the target stays OPEN. This note does four things:
- it defines `deep` and `law` for any nested pair `A ≤ B ≤ F(a,b)` and
  proves `law = rk(K' : K)`, which is the relative rank with *unrestricted*
  generators (Section 1);
- it gives a **rank-3 obstruction**: nested pairs with `deep = 1` and
  `law = n + 1` on transitive `Q_n`, together with a malnormal rank-3 pair
  with `deep = 1 < 2 = law`. Both are proved by hand and checked by exact
  computation (Sections 2 and 3). So no argument that works for every nested
  pair, or for every malnormal one, can prove (O) or even its weak form;
- it reduces (O) on `L_{j+1}`-transitive `Q` to a free-group statement
  (RI), a relative form of inertia for the rank-2 subgroup `L_j`
  (Section 4). The obstruction is precisely the failure of (RI) for `B` of
  rank 3;
- it records calibration data (Section 5):
  - on every rank-2 target tested, including targets that are not
    malnormal and pairs that are not `φ`-chains, `deep = law` with 0 gaps;
  - with `rk B = 3`, gaps persist even when both `A` and `B` are malnormal
    in `F` and `rk A = rk B = 3`. There are 175 such gaps, 147 of them with
    independent certificates;
  - the homological necessary condition for (RI) has 0 violations in
    170,000 rank-2 trials, against 982 in 5000 trials at rank 3.

## 0. Setting for a general nested pair

- `F = F(a,b)`. A *nested pair* is `A ≤ B ≤ F`, both finitely generated.
  `Q` is a finite `F`-set, given by permutations `PA`, `PB` for `a` and `b`.
- `Γ_B(Q)` is the Stallings fold of the graph with one *real* vertex per
  point of `Q` and, for each point `p` and each generator word `w` of `B`,
  a path labelled `w` from `p` to `p·w` (`foldlib.gamma`). Reals stay
  distinct. The component through `p` has `π_1 = Stab(p) ∩ B`, and every
  vertex lies over a point of `Q`. `Γ_A(Q)` is defined in the same way. Since
  `A ≤ B` there is a canonical label-preserving map
  `m : Γ_A(Q) → Γ_B(Q)`.
- A *seed* is a pair of vertices of `Γ_A(Q)` over the same point of `Q`.
  It is *lawful* if both vertices have the same image under `m`.
- `deep(Q)` is the least number of seeds whose fold closure contains
  `ker m`, and `law(Q)` is the same count with lawful seeds only.
- For `A = L_{j+1}` and `B = L_j`, these are exactly `deep_j` and `law_j`
  of the target. `chains.py` implements the general definitions on top of
  `foldlib.py` from `experiments/fpbs-depth-overfolding-2026-09-17/`, and
  reproduces the `φ`-chain values.

## 1. Relative-rank dictionary for any nested pair (proved)

Let `Q` be `A`-transitive, fix a real point `p`, and set `S = Stab(p)`,
`K = S ∩ A = π_1(Γ_A(Q), p)` and `K'' = π_1(m(Γ_A(Q)), p) ≤ K' = S ∩ B`.
Write `rk(Y : X)` for the least number of elements of `Y` that generate `Y`
together with `X`. Every vertex `v` of `Γ_A(Q)` is the end of a path from
`p` reading a word `w_v`. A seed `(u, u')` gives `g = w_u w_{u'}^{-1}`.

**Lemma 1.**
1. `g ∈ S` for every seed, and `g ∈ K''` for every lawful seed.
2. The closure of seeds `(u_i, u_i')` contains `ker m` iff
   `⟨K, g_1, …, g_k⟩ ⊇ K''`.
3. `law(Q) = rk(K'' : K)`, with generators ranging over all of `K''`.
4. `deep(Q) ≥ min{ k : g_i ∈ S, ⟨K, g⟩ ⊇ K'' }`.

When `m` is onto `Γ_B(Q)` we have `K'' = K'`. This holds for the `φ`-chain,
and it holds, as checked by `verify_gaps.py` (`m_onto True`), for every
example below.

*Proof.*
- Part 1: a seed lies over one point of `Q`, so `p·w_u = p·w_{u'}`. If
  `m(u) = m(u')`, both words end at the same vertex of the folded graph
  `m(Γ_A(Q))`.
- Part 2: `Γ_A(Q)/cl(P)` is folded and has `π_1 = H = ⟨K, g⟩`. In a folded
  graph, two readable words from `p` end at the same vertex iff
  `w w'^{-1} ∈ π_1`. So `v ~ v'` iff `w_v w_{v'}^{-1} ∈ H`, whereas
  `m(v) = m(v')` iff `w_v w_{v'}^{-1} ∈ K''`.
- Part 3, `≥`: by part 1 and part 2, `k` lawful seeds that collapse
  `ker m` give `⟨K, g⟩ = K''`.
- Part 3, `≤`: given `h_1, …, h_k ∈ K''` with `⟨K, h⟩ = K''`, attach `k`
  closed paths at `p` labelled `h_i` to `Γ_A(Q)`. By the ESTABLISHED
  domination lemma of `fpbs-word-chords-are-dominated-by-merges` (Claim 1:
  "`R_H = cl_Γ(P)` for a set `P` of at most `k` pairs"), the relation "same
  vertex of the fold" equals `cl(P)` with `|P| ≤ k`. By the criterion in
  part 2 this relation is exactly `ker m`. So every pair of `P` is lawful,
  and `cl(P) = ker m`.
- Part 4 follows from parts 1 and 2. ∎

Part 3 sharpens the target's relative-rank form: the lawful count does not
depend on the restriction `g ∈ D_law`.

## 2. Rank-3 obstruction I: `deep = 1`, `law = n + 1` (proved)

Take the nested pair
`B = ⟨a², b, a b a^{-1}⟩ = ker(F → Z/2)` (with `a ↦ 1`, `b ↦ 0`; index 2,
rank 3) and `A = ⟨b, a⁴, a b² a^{-1}⟩ ≤ B` (rank 3). For odd `n`, let
`Q_n = Z/n` with `a : i ↦ i + 1` and `b = id`.

**Proposition 2.** For every odd `n`, `deep(Q_n) = 1` and
`law(Q_n) ≥ n + 1`. Equality `law = n + 1` holds for `n = 1, 3, 5`
(exact search).

*Proof.* `Q_n` is `A`-transitive, since `a⁴ ∈ A` and `gcd(4, n) = 1`.
Here `S = ker(F → Z/n)` is normal, and `K' = S ∩ B = ker(F → Z/2n)`
(`a ↦ 1`, `b ↦ 0`), because `n` is odd.

- *`deep ≤ 1`.* The seed is `p` together with the vertex reached by `a^n`.
  It lies over the same point, since `a^n ∈ S`, and it is not lawful,
  since `a^n ∉ B`. Put `H = ⟨K, a^n⟩`.
  - `K` contains `a^{4k} b a^{-4k}`, because it lies in `A` and in the
    normal subgroup `S`.
  - Conjugating by powers of `a^n ∈ H` gives `a^{4k + ln} b a^{-(4k+ln)}`
    for all `k, l`. That is every `a^r b a^{-r}`, since `gcd(4, n) = 1`.
  - Also `a^{2n} ∈ H`.
  - These elements generate `ker(F → Z/2n) = K'`, so `H ⊇ K'`.

  By Lemma 1(2), one seed collapses `ker m`. `deep ≥ 1` holds because
  `A ≠ B` on `Q_n`.
- *`law ≥ n + 1`.*
  - `Γ_B(Q_n)` is a `2n`-cycle of `a`-edges (reals and non-reals
    alternate) with a `b`-loop at every vertex, so
    `dim H_1(Γ_B; F_2) = 2n + 1`.
  - `Γ_A(Q_n)` is a `4n`-cycle of `a`-edges. It has a `b`-loop at each of
    the `n` vertices over core vertex 0 of `core(A)`, and a `b`-2-cycle
    through an extra vertex at each of the `n` vertices over core vertex 1.
  - Every edge of `Γ_B` is hit, so `m` is onto. Under `m`, the `4n`-cycle
    wraps twice around the `2n`-cycle, and each `b`-2-cycle wraps twice
    around one `b`-loop. Both are 0 mod 2. The `n` `b`-loops over core
    vertex 0 go to `n` distinct `b`-loops at the parity-0 vertices.
  - So the image in `H_1(Γ_B; F_2)` has dimension `n`, and the cokernel
    has dimension `n + 1`.
  - Each lawful merge raises the image by at most 1. Lawful seeds have only
    lawful fold consequences, because `Γ_B(Q)` is folded (the argument of
    Lemma A of fp-last1, which works for any nested pair). So the final quotient
    is exactly `Γ_B(Q_n)`, and folding is onto on `H_1`. Hence
    `law ≥ n + 1`. ∎

Script checks: `rank3_family.py` → `rank3_family.txt`, for odd
`n ≤ 21`. It confirms `deep ≤ 1` by exact closure and
`h = n + 1` by the mod-2 cokernel. It also gives exact `law = 2, 4, 6` for
`n = 1, 3, 5`.

Random transitive `Q` behave the same way (`rank3_random.py` →
`rank3_random.txt`). The greedy deep upper bound and the certified mod-2 law
lower bound are:
- at `n = 12`: `(1, 4)`, `(1, 8)`, `(2, 8)`, `(3, 10)`;
- at `n = 25`: `(1, 11)`, `(1, 13)`.

So for this pair the ratio `law/deep` is unbounded on transitive `Q`. The
analogue of the weak form `deep ≥ c · law` therefore fails for every `c`,
and the effect is not confined to cyclic `Q`.

## 3. Rank-3 obstruction II: malnormality is not the invariant

The pair in Section 2 is not malnormal. The following examples show that
malnormality does not rescue (O).

**Hand-checked example** (`rank3_malnormal.py` → `rank3_malnormal.txt`).
- `B = ⟨x, y, z⟩` with `x = aBAB`, `y = bbAA`, `z = AbaBa`. It has rank 3
  and is malnormal in `F`, by the Kapovich–Myasnikov pullback test in
  `malnormal.py`.
- `A = ⟨x, y², z³⟩`, and `Q` is one point.
- *`law = 2`.* The generators of `A` traverse every generator loop of
  `core(B)`, so `m` is onto and `K'' = B`. By Lemma 1(3),
  `law = rk(B : A)`.
  - `B/⟨⟨A⟩⟩ = ⟨y, z | y², z³⟩ = Z/2 * Z/3` needs 2 generators (Grushko),
    so `law ≥ 2`.
  - `⟨A, y, z⟩ = B`, so `law ≤ 2`.
- *`deep = 1`.* The single seed pairs the base with the vertex read by
  `a^{-1} b a^{-1}`. Its fold closure contains `ker m`, which exact closure
  confirms.

**Doubly malnormal pairs** (`malpair.py`, `run_malpair.sh` → `malpair.txt`,
certified by `verify_gaps.py` → `malpair_verify.txt`).
- Here `B` has rank 3 or 4 and is malnormal in `F`, and `A` is generated by
  random words in the generators of `B` and is itself malnormal in `F`. So
  `A` is malnormal in `B` and `B` is malnormal in `F`, exactly as in
  `L_{j+1} < L_j < L`.
- Exact search finds gaps `deep < law` at `Q` = point and on random
  transitive `Q` with `n = 2, 3`. This includes pairs of **equal rank**,
  `rk A = rk B = 3`, like the `φ`-chain, where `rk A = rk B = 2`.
- `verify_gaps.py` re-derives each gap independently:
  - `deep ≤ |witness|` by exact closure;
  - `law ≥ h_p`, the `F_p`-cokernel of `H_1(Γ_A) → H_1(m Γ_A)` for
    `p ≤ 7`.
  
  A gap is certified when `h_p > |witness|`. Counts are in Section 5.

## 4. The invariant: relative inertia (RI) of `B`

For `B ≤ F`, consider the following statement.

> **(RI_B)** For all finitely generated `X ≤ J ≤ F` with `X ≤ B`:
> `rk((J ∩ B) : X) ≤ rk(J : X)`.
> **(RI_B, C)** is the same inequality with a factor `C` on the right.

With `X = 1`, (RI_B) is inertia of `B`: `rk(J ∩ B) ≤ rk J`. For
`rk B = 2` inside any free group, inertia follows from the strengthened
Hanna Neumann inequality (Friedman; Mineyev). This is background only and is
not cited verbatim here. For `rk B ≥ 3` inside `F_2`, inertia already fails
at `J = F`.

**Proposition 3 (proved).** Let `Q` be `A`-transitive with `m` onto, so
that `K'' = K'`. If (RI_B) holds for `X = K` and every `J` with
`K ≤ J ≤ S`, then `deep(Q) ≥ law(Q)`. Under (RI_B, C) we get
`deep ≥ law / C`.

*Proof.* Take `k = deep(Q)` seeds with elements `g_i ∈ S`, which exist by
Lemma 1(1), and set `J = ⟨K, g⟩`. Lemma 1(2) gives `J ⊇ K'`, and
`J ≤ S` gives `J ∩ B ≤ S ∩ B = K'`, so `J ∩ B = K'`. Then Lemma 1(3)
gives `law = rk(K' : K) = rk((J ∩ B) : K) ≤ rk(J : K) ≤ k`. ∎

**Consequences.**
- *For the target.* (O), and even its weak form, holds on every
  `L_{j+1}`-transitive `Q` provided (RI_{L_j}) (or (RI_{L_j}, C)) holds for
  finite-index `X ≤ L_{j+1}` (here `X = K = S ∩ L_{j+1}`). (RI) is a
  statement about the pair
  `L_j ≤ F` alone: it involves no `Q`, no seed types, no double cosets and
  no `φ`.
- *Relation to (F) of fp-pull.* (F) says `rk(J ∩ L_j : K) ≤ k` for
  *realizable hits* `J = ⟨K, g_1..g_k⟩`. So (F) is (RI_{L_j}) restricted to
  `J ∩ L_{j+1} = K` and `[L_j : J ∩ L_j] = [L_{j+1} : K]`. (RI) drops both
  restrictions. It is therefore stronger, and it may fail where (F) holds.
- *The obstruction, read through (RI).* In Section 2, take `X = K` and
  `J = ⟨K, a^n⟩`. Then `rk((J ∩ B) : K) = law ≥ n + 1`, while
  `rk(J : K) = 1`, so (RI_B, C) fails for every `C`. In Section 3, take
  `X = A` and `J = ⟨A, a^{-1}ba^{-1}⟩ ⊇ B`. Then `rk(B : A) = 2 > 1`.
  Every gap found is a failure of (RI) for some `B` of rank at least 3.
- *Where every proof in the class dies.* Take any argument for `deep ≥ law`
  (or `≥ c · law`) that uses only:
  - the fold and pullback structure of `m : Γ_A(Q) → Γ_B(Q)`, including
    Lemma A and cycle structure;
  - malnormality of `A` in `B` and of `B` in `F`;
  - equal ranks `rk A = rk B`;
  - orbit counting, or `F_p`-homology of `Γ_A` and `Γ_B`.

  Such an argument applies verbatim to the pairs of Sections 2 and 3, and is
  refuted there. It dies at the transfer step, where a witness
  `J = ⟨K, g⟩ ⊇ K'` built from overfold elements has to be converted into
  generators of `K' = J ∩ B` over `K`. A proof of (O) must use an input
  that separates `L_j` from the rank-3 examples. The candidates are
  `rk L_j = 2 = rk F`, meaning inertia-type control of `J ∩ L_j`, or genuinely
  `φ`-specific structure, such as the depth-shift identity (T_j) of fp-break.

## 5. Calibration data

All counts come from exact BFS over seed sets of size at most `maxk = 4`
(`chains.py`, `malpair.py`). A histogram entry `(d, l)` means `deep = d` and
`law = l`. `(None, None)` means both are above `maxk`, so it carries no
evidence of a gap.

**Named `φ`-type chains (rank-2 `B`).** These are `named_n5.txt`,
`named_n6.txt` and `named_n5b.txt`: the chains `psi_*_j1` and `psi_*_j2`,
`B = ⟨a, ψ(b)-word⟩`, on random transitive `Q` of size 5 and 6. Every
recorded pair has `deep = law`. The values run from 1 to 4, and the only
undecided entries are `(None, None)`. There are 0 gaps.

**Doubly malnormal random pairs** (`malpair.py`, `malpair.txt`). Both `B`
and `A` are malnormal in `F`, `rk B = rB`, and `rk A = sA`.

| n | rB | sA | pairs | gaps | gap types |
|---|----|----|-------|------|-----------|
| 1 | 3 | 2 | 3000 | 8 | (1,2) |
| 1 | 3 | 3 | 3000 | 0 | — |
| 1 | 3 | 2 | 2000 | 33 | (1,2), (2,3) |
| 1 | 4 | 3 | 1000 | 11 | (1,2) |
| 2 | 3 | 2 | 500 | 19 | (1,2), (2,3), (3,4) |
| 3 | 3 | 2 | 300 | 87 | (1,3), (2,3), (3,4) |
| 2 | 3 | 3 | 400 | 1 | (1,2) |
| 3 | 3 | 3 | 200 | 2 | (2,3) |
| 1 | 3 | 3 | 2000 | 14 | (1,2) |

Independent certificates (`verify_gaps.py`, `malpair_verify.txt`) cover all
175 gaps:
- the witness seed set closes onto `ker m` in every case (`closure_ok`);
- `m` is onto in every case, so Proposition 3 applies to the same pairs;
- 147 gaps are certified by a mod-`p` lower bound on `law`, independent of
  the BFS: 61 of type (1,2), 5 of type (1,3), 76 of type (2,3) and 5 of type
  (3,4). The other 28 rest on the exact BFS only.

Gaps therefore occur with equal ranks (`rB = sA = 3`) and with both
subgroups malnormal in `F`.

**Rank-2 control** (`run_malpair2.sh`, `malpair2.txt`). This is the same hunt
with `rB = 2`. There were seven runs: `n = 1, 2, 3`, `sA = 2, 3`,
`LB = 5, 6`, 9400 pairs in total. There are **0 gaps**. Values reach
`deep = law = 3`, and the doubly malnormal filters are the same as in the
rank-3 table. For comparison, the table above has 175 gaps in 12,400 pairs
with `rB ≥ 3`.

**Group-level (RI)** (`ri_test.py`, `ri_test.txt`). The test checks the
necessary condition
`c = max_{p=2,3} dim_{F_p} coker(H_1(X) → H_1(J ∩ B)) ≤ k` for
`J = ⟨X, g_1..g_k⟩`, using an exact Stallings pullback. A violation
certifies that (RI_B) fails.
- `rk B = 3`: 982 violations in 5000 trials, and 146 in 5000 with `B`
  malnormal.
- `rk B = 2`: 0 violations in 170,000 trials. These cover `k = 1, 2, 3`, with
  `B` malnormal and not. The bound is attained often (`c = k` for
  `k = 1, 2, 3`), so it is sharp and not vacuous.

## 6. Where it stands

- **Proved:**
  - Lemma 1, `law = rk(K'' : K)` with unrestricted generators, and
    `deep ≥ min{k : ⟨K, g_1..g_k⟩ ⊇ K''}`;
  - the rank-3 unbounded family (Proposition 2);
  - the malnormal rank-3 gap at the point (Section 3);
  - Proposition 3, (RI_B) with `m` onto implies `deep ≥ law`, and
    (RI_B, C) implies `deep ≥ law / C`.
- **Refuted as proof strategies:** every argument in the class listed in
  Section 4. Doubly malnormal, equal-rank pairs are counterexamples to that
  class.
- **Open:** (RI_{L_j}) for finite-index `X ≤ L_{j+1}`, and hence (O) on
  transitive `Q`, by this route. Evidence: 0 homological violations for
  `rk B = 2` in 170k trials, and 0 gaps on all rank-2 nested pairs tested.
  A proof of homological (RI) would give only `law` bounded by the mod-`p`
  cokernel. To reach (O) one still needs (RI) for ranks, or an argument
  that the `F_p` cokernel computes `rk(K'' : K)` for these pairs.
  For `X = 1`, (RI) is ordinary inertia of `L_j`, which holds for rank-2
  subgroups by the strengthened Hanna Neumann theorem (background, not used
  here). The relative version, with `X ≠ 1`, is the missing step.
- **Next step:** prove (RI_B) for `rk B = 2`, starting with `B = F` (where it
  is trivial) and `B = ⟨a, t⟩` of index `∞` via the pullback
  `core(J) × core(B)`. Alternatively, find a rank-2 counterexample, which
  would kill the (RI) route and point back to the `φ`-specific inputs
  (T_j) and (O'_j) of fp-break.

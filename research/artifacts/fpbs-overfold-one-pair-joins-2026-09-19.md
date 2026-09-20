# One-element joins are one-pair folds: exact k = 1 tests for the (O) route

Worker swarm-0917-w20-w20-fp-last1 (logic-computability), September 19, 2026.
Target: `fpbs-mal-overfold-merges-never-help` (O), the claim
`deep_j(Q) = law_j(Q)`, through the reduction chain
`(RI_{L_j}) => (G_j) => (O)` (w17 Prop 3, w19 §7).

Code and runs: `experiments/fpbs-overfold-one-pair-2026-09-17/`.

## 0. Summary

1. **Lemma 1 (one-pair lemma), proved.** For a f.g. `X <= F` and any `g`
   in `F`, the join `<X, g>` falls in one of two cases.
   - Arc case: `Γ_X` embeds in `Γ_{<X,g>}` and the rank goes up by one.
   - One-pair case: `Γ_{<X,g>} = fold(Γ_X / (u ~ w))` for two vertices
     `u, w` of `Γ_X`.
2. **Corollary (exact decidability at k = 1).** "`rk(J : X) <= 1`" is
   decided by finitely many folds. So each instance of the following is
   decidable exactly, with no bound on `|g|`:
   - (RI_B) at `k = 1`, for any `B` of rank 2;
   - E(2);
   - (Mon_φ) at `k = 1`;
   - (W).

   This supersedes every length-bounded g-search of w18 and w19.
3. **(W) of w19-follow is REFUTED.** The explicit witness has `|g| = 8`,
   just past w19's search bound of 7. Seven or more further witnesses were
   found (§4).
4. **Lemma 2 (φ-expansion dictionary).** It gives `Γ_{φ(X_0)}` in closed
   form from `Γ_{X_0}`. It was verified on 3000 random `X_0`.
5. **Exact censuses.** They found 0 violations of (Mon_φ) at `k = 1` and
   0 violations of (RI_{L_1}) and (RI_{L_2}) at `k = 1`. A self-test
   confirms the same code detects the known non-malnormal failure of w19
   (72 violating pairs).
6. **Status.** (O) stays OPEN. What is left is `k >= 2`, where arc
   extensions make the family of joins infinite, together with a proof,
   rather than a census, of the `k = 1` statements.

## 1. Lemma 1 (one-pair lemma)

**Setup.**
- `Γ_X` is the based folded core graph of `X`, with base `o`.
- `g` is reduced and nontrivial.
- `p` is the longest prefix of `g` readable in `Γ_X` from `o`. It ends at
  `u`.
- `q` is the longest suffix of `g` such that `q^{-1}` is readable from
  `o`, taken so that `|p| + |q| <= |g|`. The path `q` starts at `w` and
  ends at `o`.
- Write `g = p s q`.

**Lemma 1.**
- (a) If `s` is nonempty, then `Γ_{<X,g>}` is `Γ_X` with an arc labelled
  `s` attached from `u` to `w`. When `u = w`, the new edges may fold among
  themselves and form a lollipop. In either case:
  - `Γ_X` is a subgraph of `Γ_{<X,g>}`;
  - `<X,g> = X * <p s p^{-1}>` when `u = w`, and in general `X` is a free
    factor of `<X,g>`;
  - `rk <X,g> = rk X + 1`.
- (b) If `s` is empty, then `Γ_{<X,g>} = fold(Γ_X / (u ~ w))`. If
  moreover `u = w`, then `g` is in `X`.

**Proof.** Attach a subdivided loop labelled `g` at `o` and run Stallings
folds.
- The first `|p|` edges of the loop fold onto the path `p` in `Γ_X`.
- The last `|q|` edges fold onto `q`.

This leaves `Γ_X` together with a path labelled `s` from `u` to `w`.

Case (a), `s` nonempty:
- By maximality of `p`, the first letter of `s` is not readable at `u`.
- By maximality of `q`, the inverse of the last letter of `s` is not
  readable at `w`.
- The interior vertices of the arc have degree 2, and `s` is reduced.
- So no new edge folds with an edge of `Γ_X`.
- If `u = w`, new edges can fold with each other (when `s` is not
  cyclically reduced). Those folds create only new vertices and never
  touch `Γ_X`, because the letters involved are not readable at `u`.
- The result is folded and contains `Γ_X` as a based subgraph. Since the
  based subgraph is a core, `X` is a free factor.
- The graph has one more independent cycle than `Γ_X`, and folding with
  distinct endpoints preserves rank.

Case (b), `s` empty: the remaining "path" has length 0, so it identifies
`u` with `w`, and folding completes the join. ∎

**Consequence.** The joins `<X,g>` that are not arc extensions are exactly
the at most `C(|V Γ_X|, 2)` one-pair folds. Every one-pair fold arises:
`g = p q` with `p` a path from `o` to `u` and `q` a path from `w` to `o`.

**Arc case against a rank-2 host (all B of rank 2, malnormal or not).**
Take `X <= B` and `J = <X,g>` in case (a), and put `Y = J ∩ B`.
- The Strengthened Hanna Neumann theorem (Friedman; Mineyev) gives
  `rk Y - 1 <= (rk J - 1)(rk B - 1) = rk X`, so `rk Y <= rk X + 1`.
- `X` is a free factor of `J` and `X <= Y <= J`. By Kurosh, `X` is a
  free factor of `Y`.
- So `Y = X * Y'` with `rk Y' <= 1`, that is `rk(Y : X) <= 1`.

The arc case therefore never violates (RI_B) at `k = 1`. All `k = 1`
content lives in the finitely many one-pair folds.

**Criterion.** `rk(Y : X) <= 1` holds if and only if one of these holds:
- `Y = X`;
- `Γ_X -> Γ_Y` is injective and `rk Y = rk X + 1`;
- `Γ_Y` is a one-pair fold of `Γ_X`.

This is Lemma 1 applied to `Y = <X, y>`. Conversely, an injective based
immersion of cores is a subgraph inclusion, which makes `X` a free factor
of `Y`. It is implemented as `relrank_le1` in `ri_k1.py`.

**Validation.** `test_lemma1.py` compared the prediction of Lemma 1 with
direct folding on random `(X, g)`: 1846 one-pair cases, 1110 arc cases,
0 mismatches (`test_lemma1.txt`).

## 2. Corollary: exact decidability at k = 1

Let `X <= L_1` with `X = φ(X_0)`. The following are decidable by finitely
many folds of `Γ_X`, uniformly over all `g` in `F`.

- **E(2): does `<X, g> = F` hold for some `g`?**
  - If `rk X >= 2`, the arc case gives rank `>= 3`, which cannot be `F`.
    So the answer is yes exactly when some one-pair fold of `Γ_X` is the
    rose.
  - If `rk X = 1`, the arc case is `F` exactly when `X` is generated by a
    primitive element.
  - **The cyclic case of (Mon_φ) is automatic by Kurosh.** A primitive
    element of `F` that lies in `L_1` is a free factor of `L_1`.
- **(Mon_φ) at `k = 1`**: if `<φX_0, g> = F` for some `g`, then
  `<X_0, h> = F` for some `h`. Both sides are finite checks.
- **(W).** Also a finite check.
- **(RI_{L_j}) at `k = 1`.** For each one-pair fold `J` of `Γ_X`, compute
  `Y = J ∩ L_j` by pullback and apply the Criterion. Arc joins are always
  fine (§1).

Earlier waves could only search `|g| <= 7`. Lemma 1 removes that bound
entirely at `k = 1`.

## 3. Lemma 2 (φ-expansion dictionary) and the type lemma

Recall `φ(a) = a` and `φ(b) = b a b^{-2}`. Given the folded graph
`Γ_0 = Γ_{X_0}`, define `Exp(Γ_0)` as follows.

Vertices:
- `(o, z)` for every vertex `z`;
- `(1, z)` for every vertex `z` incident to a `b`-edge;
- `(2, e)` for every `b`-edge `e = (s, r)`.

Edges:
- the `a`-edges of `Γ_0`, on the `o`-vertices;
- `(o, z) -b-> (1, z)`;
- `(1, s) -a-> (2, e)` and `(1, r) -b-> (2, e)`, for each `b`-edge
  `e = (s, r)`.

**Lemma 2.** `Exp(Γ_0)` is folded and has `π_1 = φ(X_0)`. So
`Γ_{φ X_0} = core(Exp(Γ_0))`.

**Proof.** Each `b`-edge `s -> r` is replaced by the path
`b a b^{-1} b^{-1}`, which runs through `(1,s)`, `(2,e)`, `(1,r)` and then
reaches `(o,r)`. The edges at `(1,s)` and `(1,r)` are shared by all
`b`-edges at `s` and `r`, which is the only folding possible:
- the out-`b` edge of `(o,z)` is shared between gadgets;
- the out-`a` edges at `(1,s)` go to distinct `(2,e)`, one per `b`-edge out
  of `s`, and `Γ_0` has at most one;
- likewise for the out-`b` edges at `(1,r)`.

So the graph is folded, and `π_1` is the image of `π_1(Γ_0)` under
`φ`. ∎

Verified against direct folding on 3000 random `X_0`
(`expansion.py`, `expansion_check.txt`).

**Type lemma (proved).** Let `(x, y)` be a pair of vertices of
`Exp(Γ_0)` of the same type (`oo`, `11` or `22`). Then the one-pair join
`<φX_0, g>` lies in `L_1`, so it is never `F`.

**Proof.** A vertex `(o,z)` is reached from the base by `φ(w_z)`, where
`w_z` is a path in `Γ_0`. Every path from the base to `(o,z)` is
`(loop) · φ(w_z)`, so it lies in `L_1 · 1`. In the same way:
- paths to `(1,z)` lie in `L_1 b`;
- paths to `(2,e)` lie in `L_1 b a`.

With `g = p q` as in Lemma 1, a same-type pair gives
`g ∈ L_1 c c^{-1} L_1 = L_1`. ∎

Only the mixed types `o1`, `o2` and `12` can reach `F`. They correspond to
the double cosets `L_1 b L_1`, `L_1 ba L_1` and `L_1 b a^{-1} b^{-1} L_1`.

In `transfer.py` (seed 1, 300 trials) the collapsing hits were 101 `1o`,
88 `2o` and 94 `12`, with no same-type hit, as the type lemma predicts.

The fold closure of a mixed pair cycles through the three mixed types.
Its same-type part is a `Γ_0`-fold-closed equivalence.

No transfer rule was found. Projecting a collapsing mixed pair of
`Exp(Γ_0)` to the pair of its underlying `Γ_0`-vertices collapses `Γ_0`
in only 142 of 283 hits. Shifted projections by words of length up to 2
(`transfer2.py`) were uninformative, because collapsing in `Γ_0` is
generic. So a proof of (Mon_φ) at `k = 1` needs a non-local transfer.

## 4. (W) is false

w19-follow conjectured (W): if `X <= L_1` and `<X, g> = F`, then
`<X, a> = L_1` or `<X, t> = L_1`, where `t = b a b^{-2}`. Its evidence was
185/185 cases with `|g| <= 7`.

**Counterexample** (`witness.py aBAB,ABaba`, output in `witness_W.txt`,
checked by direct folding). Take
`X_0 = <a b^{-1} a^{-1} b^{-1}, a^{-1} b^{-1} a b a>` and `X = φ(X_0)`,
which is generated by `abbABAbbAB` and `AbbABabaBBa`. Then:
- `g = AbbbaBBa` gives `<X, g> = F`. Here `|g| = 8`, just past the old
  bound.
- `<X, a> ≠ L_1` and `<X, t> ≠ L_1`. Equivalently, `<X_0, a> ≠ F` and
  `<X_0, b> ≠ F`.
- (Mon_φ) still holds here: `h = b a^{-1}` gives `<X_0, h> = F`.

A second witness is `X_0 = <b^{-2}, b a^{-1} b^{-1} a b>`, with
`g = baBBABabbAB`, `h = ab`.

There were 79 (W)-violations among the 11494 E(2)-hits of
`run_s2_g5_l8.txt`. Further violations are listed in `run_s3_g3_l10.txt`
and `run_s4_g6_l5.txt`, for 295 across the three runs (§5).

**What dies.** Any proof of (Mon_φ) or (G_1) that goes through "the
completing element can be taken to be `a` or `t`" is dead. Two things
survive:
- the weaker transfer (Mon_φ), whose witness `h` need not be a
  generator;
- Prop O of w19. It is a statement about rank-2 overgroups, not about
  which element completes.

## 5. Exact censuses at k = 1 (all g at once)

Random `X_0` with 1 to `G` generators, each of length at most `Lm`.

**(Mon_φ) and (W)** (`monphi_k1.py seed trials G Lm`). Column A counts
`X_0` with `<φX_0, g> = F` for some `g`; column B counts `X_0` with
`<X_0, h> = F` for some `h`.

| run | X_0 tested | A (E(2) hits) | B | A and not B (Mon_φ violations) | A and not W |
|---|---|---|---|---|---|
| seed 1, G=4, Lm=6, 2000 trials | 1969 | 1246 | - | 0 | 7 |
| seed 2, G=5, Lm=8, 20000 trials | 19883 | 11494 | 18728 | 0 | 79 |
| seed 3, G=3, Lm=10, 20000 trials | 19854 | 6558 | 15969 | 0 | 179 |
| seed 4, G=6, Lm=5, 20000 trials | 19754 | 16200 | 19439 | 0 | 37 |

Total: 0 Mon_φ violations among 35498 exact E(2)-hits. There are
302 (W)-violations: 295 in the three saved runs and 7 in the seed 1 run,
whose output file was not kept. The
converse fails often (B and not A, 19884 cases), as expected: `φ` loses
information.

**(RI_{L_j}) at k = 1** (`ri_k1.py j seed trials G Lm`). `J` counts the
distinct one-pair folds, `Y ≠ X` the cases where `J ∩ L_j` is larger than
`X`, and `Y = L_j` the cases where it is all of `L_j`.

| run | X | one-pair joins J | Y ≠ X | Y = L_j | violations |
|---|---|---|---|---|---|
| j=1, seed 1, G=4, Lm=5 | 300 | 4080 | 602 | 238 | 0 |
| j=1, seed 11, G=4, Lm=6 | 6000 | 142487 | 18307 | 4698 | 0 |
| j=2, seed 13, G=3, Lm=4 | 300 | 18313 | 491 | 250 | 0 |

- The seed-1 row's output file was not kept.
- A larger `j = 1` run (`G = 6`, `Lm = 8`) was stopped for time before it
  produced results.
- Saved outputs: `ri_j1_s11.txt` and `ri_j2_s13.txt`.

**Self-test** (`selftest_ri.py`, output in `selftest_ri.txt`). The
w19-last1 counterexample to (RI) is the host
`B = <b, a b^2 a^{-1}> = ψ(F)`, where `ψ(a) = b` and `ψ(b) = a b^2 a^{-1}`,
with `X = ψ(ker(F -> S_3))` for the regular action. Rank-7 `X` gives:
- 72 violating one-pair folds for the non-malnormal host `B`;
- 0 for the host `L_1` on the same kernel type.

So the exact procedure does detect the known failure. Since the arc case
is harmless for every rank-2 host, that failure must be a one-pair
phenomenon, and it is.

## 6. What remains, and the precise gap

1. **`k >= 2`.** For `rk(J : X) = 2`, the joins `<X, g_1, g_2>` include
   arc-then-fold combinations. The second element can fold into the arc
   created by the first, so the family is infinite and Lemma 1 does not
   reduce it to a finite list.
   - A two-step analogue is still available: `<X, g_1, g_2>` is a
     one-pair fold, or an arc, over `<X, g_1>`.
   - This is only useful combined with Lemma R of w19 (reduction to the
     top case `E(r)`) and an induction on `r`. That needs (Mon_φ) at
     every `r`, not just `k = 1`.
2. **A proof of (Mon_φ) at `k = 1`.** By the type lemma this is a
   statement about mixed pairs of `Exp(Γ_0)`: if the fold of one mixed
   pair is the rose, then `Γ_0` has a collapsing pair. The census has 0
   exceptions, but no transfer map is known, since simple projections
   fail about half the time (§3).
3. **Status.** (O) stays OPEN. Nothing here is a counterexample to (O).
   The contributions are:
   - the finite reduction at `k = 1`;
   - the death of (W);
   - the harmlessness of arcs for every rank-2 host;
   - the type lemma.

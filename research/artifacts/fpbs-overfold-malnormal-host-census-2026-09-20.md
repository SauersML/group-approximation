# Malnormal-host censuses for (RI) and the image / one-fibre split

Worker swarm-0917-w20-w20-fp-follow (compute scout), September 20, 2026.
Target: `fpbs-mal-overfold-merges-never-help` (O), through the chain
`(RI_{L_j}) => (G_j) => (O)` of w17 Prop 3 and w19 §7. The k = 1 layer
was made exact in `research/artifacts/fpbs-overfold-one-pair-joins-2026-09-19.md`
(w20-fp-last1).

Code and runs: `experiments/fpbs-overfold-malnormal-host-census-2026-09-17/`.
The code imports the folding kernel from
`experiments/fpbs-overfold-one-pair-2026-09-17/`.

Status: **OPEN.** Nothing here proves (O). This note does three things.

1. It extends the exact k = 1 census from the φ-levels to *random*
   malnormal rank-2 hosts, and to the (G_1) regime `X ≤_f.i. L_2`,
   `Y = J ∩ L_1`.
2. It certifies `rk(Y:X) ≤ 2` in every k = 2 case it sampled.
3. It splits (RI_B) into two combinatorial sub-claims, (A) and (B). The
   one known failure mechanism, the w19 non-malnormal host, breaks
   exactly one of them: (B).

## 0. Summary

1. **k = 1 census, exact per instance, 0 violations on malnormal hosts.**
   Each instance enumerates all `C(|V|,2)` one-pair joins
   `J = fold(Γ_X/(u~w))` and computes `Y = J ∩ B` by pullback.

   | host B | inst | joins | `Y≠X` | `Y=B` | viol | type of `Y≠X` |
   |---|---|---|---|---|---|---|
   | `L_1` | 400 | 26765 | 1446 | 520 | **0** | 1446 pair, 0 arc |
   | random malnormal, rank 2, inf. index | 562 | 205029 | 1500 | 620 | **0** | 1500 pair, 0 arc |
   | `L_1`, with `X ≤ L_2` (the (G_1) regime) | 371 | 133491 | 10947 | 354 | **0** | 10947 pair, 0 arc |
   | non-malnormal, rank 2 (calibration) | 148 | 29227 | 703 | 272 | **20** | 683 pair |

   On malnormal hosts every nontrivial `Y` was a one-pair fold of `Γ_X`.
   The arc certificate never occurred.
2. **k = 2 and k = 3, semi-decided.** Every sampled join had
   `rk(Y:X) ≤ npairs`: 0 uncertified and 0 over the bound.
   - In the (G_1) regime: 15067 two-pair joins with `Y ≠ X`. Of these, 823
     have `rk(Y:X) = 2` exactly, and all 823 are certified `≤ 2`.
   - A further 2512 joins with 2 or 3 pairs across four host types, all
     certified (§4).
3. **Image / one-fibre split (§5).** Let `m = (q, f) : Γ_X → P` with
   `P = core(Γ_J ×_based Γ_B)`, and `Z = π_1(m(Γ_X))`.
   - (A) says `Z = Y`.
   - (B) says `Z` is the fold of `Γ_X` by **one** pair taken from an
     `m`-fibre.
   - (A) and (B) together imply `rk(Y:X) ≤ 1`.
   - Proved: `ker m = ≈ ∩ ker f` is fold-closed, and if `f(u) = f(w)`
     then `Y = J` and both claims hold trivially. So all content is in
     pairs with `f(u) ≠ f(w)`.
4. **Data on the split.**
   - One-pair joins: 1912 joins with `Y ≠ X`, spread over the three
     malnormal host types and 60 non-malnormal instances.
     **(A) never failed, (B) never failed.**
   - Every known k = 1 violation satisfies (A) and **fails (B)**. That is
     the w19 non-malnormal counterexample, `B = <b, ab^2a^-1>` with
     `X = ker(B→S_3)`, plus all 20 violations of the non-malnormal
     census. So the known obstruction lives entirely in the "one fibre
     pair" claim.
   - Multi-pair joins: (A) fails in 22 of 1585 cases, all in the (G_1)
     regime. In each failure, `m` is injective (`Z = X`) and `Y` is
     `X` plus one arc. So `rk(Y:Z) + rk(Z:X) ≤ npairs` still holds in
     every case.
5. **An inductive route is dead (§6, proved).** The natural induction
   step is
   (RI'): `rk(<Z,g> ∩ B : Z ∩ B) ≤ 1` for arbitrary f.g. `Z`.
   It is false: take `Z = <b>`, `g = a`, `B = L_1`. So any induction on
   `k` has to carry the hypothesis `X ≤ B` through every intermediate
   step. It cannot pass through `J_1 = <X, g_1> ⊄ B`.

## 1. Setting and notation

- `F = F(a,b)`, `φ(a) = a`, `φ(b) = b a b^-2`, `L_j = φ^j(F)`. In the code
  `L_1 = <a, baBB>` and `L_2 = <a, φ^2(b)>`. Capitals are inverses.
- `(RI_B)`: for f.g. `X ≤ B` and any `J ≥ X`,
  `rk(J ∩ B : X) ≤ rk(J : X)`. Here `rk(Y:X)` is the least `k` with
  `Y = <X, g_1..g_k>`.
- k = 1 case: by Lemma 1 of w20-fp-last1, `J = <X,g>` is either an arc
  extension (harmless for every rank-2 `B`) or `Γ_J = fold(Γ_X/(u~w))`.
  So (RI_B) at k = 1 says: for every pair `u, w` of vertices of `Γ_X`,
  `rk(Y:X) ≤ 1`, where `Y = J ∩ B`.
- Throughout, `f : Γ_X → Γ_B` is the based immersion (`X ≤ B`), and
  `q : Γ_X → Γ_J` is the fold map, with kernel `≈`.
- `P` is the core of the based component of `Γ_J × Γ_B`, so
  `π_1(P) = Y`.

## 2. Method

- **Exact test for `rk(Y:X) ≤ 1`** (`census.relrank_le1`). It returns:
  - `eq` when `Y = X`;
  - `arc` when `rk Y = rk X + 1` and `Γ_X` embeds in `Γ_Y`;
  - `pair` when `Γ_Y = fold(Γ_X/(x~x'))` for some pair `x, x'` in one
    fibre of the immersion `Γ_X → Γ_Y`;
  - `None` otherwise.

  By Lemma 1 of w20-fp-last1, `None` is an exact certificate that
  `rk(Y:X) ≥ 2`. The fibre pruning is sound: if `Γ_Y` is a one-pair fold
  of `Γ_X`, then the pair is identified in `Γ_Y`, so it lies in one fibre.
- **Hosts** (`census.host`).
  - `rand`: `B = <u,v>` with `|u|, |v| ∈ [3,7]` random, graph rank 2,
    `Γ_B` not a covering (so infinite index), and malnormal.
    Malnormality is decided exactly: every off-diagonal component of
    `Γ_B × Γ_B` must be a forest.
  - `nonmal`: the same, but not malnormal.
  - `L1`: `B = L_1`.
  - `L1overL2`: `B = L_1`, and `X` is taken of finite index in `L_2`
    (not in `L_1`). This is exactly the regime of (G_1):
    `rk(M ∩ L_1 : M ∩ L_2)` with `M ∩ L_2` of finite index in `L_2`.
- **X** (`census.rand_X`). `X` has finite index in the sub-host `C`. It is
  either a point stabiliser of a random transitive action of `C` of
  degree 2–6, or the kernel of a random map `C → ⟨σ, τ⟩ ≤ S_m`
  (`m ≤ 5`, image order 3–24, regular action). `Γ_X` is capped at 160
  vertices (120 in `analyze*.py`).
- **Joins** are deduplicated by the canonical form of `Γ_J`. So "joins"
  in the tables counts distinct `J`, not pairs.
- **Selftest** (`census.py selftest`).
  - It reproduces the w19 non-malnormal violation.
  - It confirms `L_1` and `L_2` malnormal, and `<a, bab^-1>` not
    malnormal.

## 3. k = 1: exact censuses

Command: `census.py k1 <seed> <trials> <host>`. The final lines are in
`k1_*.txt`:

- `L1`, seed 13:
  `{'inst': 400, 'J': 26765, 'Yneq': 1446, 'YB': 520, 'viol': 0, 'pair': 1446}`.
- `rand`, seed 11:
  `{'inst': 562, 'J': 205029, 'Yneq': 1500, 'YB': 620, 'viol': 0, 'pair': 1500}`.
  The run hit its timeout at 562 of 600 trials. The line is the census
  up to that point.
- `L1overL2`, seed 14:
  `{'inst': 371, 'J': 133491, 'Yneq': 10947, 'YB': 354, 'viol': 0, 'pair': 10947}`.
  Timeout at 371 of 400.
- `nonmal`, seed 12:
  `{'inst': 148, 'J': 29227, 'Yneq': 703, 'YB': 272, 'viol': 20, 'pair': 683}`.

Remarks.

1. **The malnormal hosts are new here.**
   - w20-fp-last1 covered `L_1` and `L_2` with `X` of finite index in the
     host itself.
   - `rand` tests (RI_B) for 562 malnormal rank-2 hosts that are not
     φ-images. It is evidence that (RI_B) at k = 1 is a statement about
     malnormality, not about φ.
   - `L1overL2` is the (G_1) input. It has the highest rate of nontrivial
     `Y`: 8.2% of joins, against 5.4% for `L1` and 0.7% for `rand`. All
     10947 are one-pair folds.
2. **Arcs never occur.** On all hosts, including the non-malnormal ones,
   no nontrivial `Y` arose as an arc extension of `Γ_X`: every certified
   `Y` was `pair`.
3. **The calibration fails where it should.**
   - The 20 non-malnormal violations come from 3 of 148 hosts:
     `<BAbb, BAba>` and `<aba, AAB>` with `X` a regular 24-kernel
     (`rk X = 25`), and `<baB, BAb>` (two conjugates of `a`) with a regular
     6-kernel.
   - In each, `X` is normal in `B`, so there are many conjugate
     fibres. This is the w19 conjugation mechanism.
   - Violations have `rk Y ∈ {2, 5}`, and `Y = B` occurs.

## 4. k = 2 and k = 3: certified censuses

Command: `census.py k2 <seed> <trials> <host> <samples>`. Each sample is
the join of `Γ_X` with two random pairs.

- When the exact k = 1 test says `rk(Y:X) ≥ 2`, the join is certified
  `≤ 2` by `pair+1`: one fibre pair `p`, then the exact k = 1 test from
  `fold(Γ_X/p)` to `Y`.
- An arc search (`relrank_le2`) is available but was never needed.

Results:

- `L1overL2`, seed 21, 400 samples (`k2_L1overL2_s21.txt`):
  `{'inst': 140, 'J': 35415, 'Yneq': 15067, 'YB': 266, 'gt1': 823, 'cand': 0}`,
  with certificates `{'pair+1': 823}`.
  So all 823 joins with `rk(Y:X) = 2` exactly are certified `≤ 2`, and
  there are 0 candidates for `rk(Y:X) ≥ 3`.
- Smoke runs on `rand` and `nonmal` (5 instances each): `gt1 = 0`.

`analyze2.py` runs the same test through the intermediate `Z` of §5.
Every join is certified with `rk(Y:Z) + rk(Z:X) ≤ npairs`: 0 `UNCERT`,
0 `OVER`.

| run | host | pairs | inst | `Y≠X` | X→Z: pair / pair+1 / eq | Z→Y: eq / arc |
|---|---|---|---|---|---|---|
| s41 | `L1overL2` | 2 | 38 | 1585 | 1444 / 119 / 22 | 1563 / 22 |
| s42 | `rand` | 2 | 37 | 483 | 466 / 17 / 0 | 483 / 0 |
| s43 | `nonmal` | 2 | 28 | 322 | 304 / 18 / 0 | 322 / 0 |
| s44 | `L1` | 3 | 30 | 122 | 98 / 24 / 0 | 122 / 0 |

In the 22 cases with Z→Y `arc`, X→Z is `eq`. So `m` is injective and
`Y = <X, one arc>`.

Caveat: these are *random* samples. Two random pairs are usually far from
the extremal configurations that the w17 reduction feeds into (G_j).
They test typical behaviour, not the worst case.

## 5. The image / one-fibre split

Fix a one-pair join `Γ_J = fold(Γ_X/(u~w))`, so `≈ = ker q` is the least
fold-closed equivalence containing `(u,w)`. Define:

- `m = (q, f) : Γ_X → Γ_J × Γ_B`, which lands in `P`;
- `I = m(Γ_X)`;
- `Z = π_1(I, base)`.

**Lemma 5.1 (proved).**

(i) `ker m = ≈ ∩ ker f` is fold-closed.

(ii) `I = Γ_X / ker m` is folded, and
`Z = <X, h_{x,x'} : m(x) = m(x')> ≤ Y`.

(iii) For `x ≈ x'`, `h_{x,x'} := p_x p_{x'}^{-1}` lies in `B` iff
`f(x) = f(x')`.

(iv) If `f(u) = f(w)`, then `J ≤ B`, so `Y = J = Z` and `rk(Y:X) ≤ 1`.

*Proof.*

(i) Let `x ≈ x'` with `f(x) = f(x')`, and let `x -s-> y` and
`x' -s-> y'`. Then `y ≈ y'` because `≈` is fold-closed. Also
`f(y) = f(y')`, because `Γ_B` is folded and `f` is a morphism.

(ii) A quotient of a folded graph by a fold-closed equivalence is folded.
The graph `I` is the image of a morphism into the folded graph `P`, so
`I = Γ_X/ker m`. Its `π_1` is generated by `X` and the jumps across
`ker m`. It lies in `π_1(P) = Y`.

(iii) Reading `p_{x'}^{-1}` backwards from the base of the folded graph
`Γ_B` is deterministic and ends at `f(x')`. So `h_{x,x'}` closes up in
`Γ_B` iff `f(x) = f(x')`.

(iv) `J = <X, h_{u,w}>`, and `h_{u,w} ∈ B` by (iii). ∎

So the whole k = 1 question is about pairs with `f(u) ≠ f(w)`. It splits
into two claims:

- **(A) image claim:** `Z = Y`. Equivalently, `core(P) ⊆ I`: no reduced
  loop of `P` leaves the image of `Γ_X`.
- **(B) one-fibre claim:** `Z = fold(Γ_X/(x~x'))` for a *single* pair
  with `m(x) = m(x')`. Equivalently, the fold-closed equivalence
  `≈ ∩ ker f` is generated by one pair.

(A) and (B) together give `rk(Y:X) ≤ 1`.

**Data** (`analyze.py`, all one-pair joins with `Y ≠ X`):

| run | host | inst | `Y≠X` | A fails | B fails | max fibre pairs |
|---|---|---|---|---|---|---|
| s33 | `L1` | 60 | 189 | 0 | 0 | 54 |
| s31 | `L1overL2` | 54 | 1331 | 0 | 0 | 64 |
| s35 | `rand` | 55 | 129 | 0 | 0 | 96 |
| s12 | `nonmal` | 60 | 263 | 0 | 0 | 64 |
| w19 | `<b, ab^2a^-1>`, `X = ker→S_3` | 1 | 8 | **0** | **1** | 15 |
| viol | `<baB,BAb>`, reg 6 | 1 | 6 | **0** | **2** | 15 |
| viol | `<BAbb,BAba>`, reg 24 | 1 | 25 | **0** | **9** | 69 |
| viol | `<aba,AAB>`, reg 24 | 1 | 25 | **0** | **9** | 92 |

The three `viol` rows come from `analyze_viol.py`, which lifts the cap.
They are exactly the three violating instances of §3. Their
`2 + 9 + 9 = 20` (B)-failures are the 20 k = 1 violations of
`k1_nonmal_s12.txt`, and (A) holds in every one of them. So **every known
k = 1 violation of (RI_B) satisfies (A) and fails (B)**.

The s12 `nonmal` row contains no k = 1 violation. The cap of 120
vertices on `Γ_X` drops the 24-kernel violators of §3, so this row only
calibrates (A). The failure of (B) is shown by the w19 row.

The w19 line (`analyze_w19.py`) reads:
`FAIL A=True B=False pair=(0,6) rkX=7 rkY=2 rkZ=2`.

So `Y = Z = B` is reached from `X` (rank 7) through the `m`-fibres, but
no single fibre pair does it. The jump `h_{0,6}` has `f(0) ≠ f(6)`. It
leaves `B`, and in `J ∩ B` it is replaced by two independent fibre
elements. This is how conjugacy in a non-malnormal `B` lets one
generator of `J` become two of `J ∩ B`.

**Multi-pair joins.** `analyze.py <seed> <T> <host> 2 <samples>`.

- (A) failed in 22 of 1441 two-pair `L1overL2` joins (s34), and in 0 of
  440 `rand` joins (s32).
- All 22 have `rk Z = rk X` and `rk Y = rk X + 1`. This is the same
  pattern as the 22 arc cases of run s41 in §4 (a different seed):
  `Z = X` and `Y = <X, arc>`.
- The "B fails" counts in those runs (123 and 13) are expected and carry
  no information. With two pairs, `Z` may need two fibre pairs.
  `analyze2.py` certifies all of them with `pair+1` (§4).

**Reading.** In every observed case, `Y` is obtained from `X` in two
stages:

1. fold along `≈ ∩ ker f`;
2. then add at most `rk(Y:Z)` arcs.

The total cost of the two stages was always at most the number of pairs.
This suggests the conjecture:

> **(Int_B).** For `X ≤ B` f.g., `B` malnormal of rank 2, and `S` a set of
> pairs of vertices of `Γ_X` with fold closure `≈_S`:
> `r(≈_S ∩ ker f) + rk(Y : Z_S) ≤ |S|`,
> where `r(κ)` is the least number of pairs generating the fold-closed
> equivalence `κ`.

(Int_B) with `|S| = k` implies (RI_B) at level `k`, by subadditivity:
`rk(Y:X) ≤ rk(Y:Z) + rk(Z:X)` and `rk(Z:X) ≤ r(ker m)`.

(Int_B) is a statement about intersecting a *generated* fold-closed
equivalence with the kernel of an immersion. That is the same shape as
(O) itself: `deep` counts pairs generating a closure, and `law` counts
pairs generating its intersection with the kernel of `C_{j+1} → C_j`.
So the sub-claims are not easier in kind than (O). They are finer: they
isolate which half fails for non-malnormal `B`.

## 6. The one-step induction is false (proved)

A natural way to get general `k` from `k = 1` is to write
`J = <J_1, g_k>` with `J_1 = <X, g_1..g_{k-1}>` and use the one-step
bound

> (RI'): `rk(<Z,g> ∩ B : Z ∩ B) ≤ 1` for every f.g. `Z` and every `g`.

**(RI') is false.** Take `B = L_1 = <a, baBB>`, `Z = <b>` and `g = a`.

- Then `<Z,g> = F`, so `<Z,g> ∩ L_1 = L_1`.
- And `<b> ∩ L_1 = 1`. To see this, look at `Γ_{L_1}`. It has vertices
  `0, 1, 2`, an `a`-loop at 0, and edges `0 -b-> 1`, `1 -a-> 2`,
  `1 -b-> 2`.
  - Reading `b^n` from 0 visits `1, 2` and then stops, since vertex 2
    has no outgoing `b`-edge.
  - Vertex 0 has no incoming `b`-edge, so `b^{-1}` cannot be read from 0.
  - The pullback computation agrees: `rk(<b^n> ∩ L_1) = 0` for
    `n = 1..8`.
- So `rk(L_1 : 1) = 2 > 1`.

The induction therefore has to keep `X ≤ B` at every stage. The
intermediate `J_1` generally leaves `B`, and `J_1 ∩ B` can be much
smaller than the part of `J ∩ B` that `J_1` "pays for". Any proof of
(RI_B) for `k ≥ 2` must control all `k` pairs at once, as (Int_B) does,
or use a different decomposition of `J`.

## 7. Where this leaves (O)

- **Established here.**
  - The exact k = 1 censuses of §3: 0 violations on 1333 malnormal host
    instances, over 13893 nontrivial joins.
  - The certified k = 2 and k = 3 samples of §4.
  - Lemma 5.1, and the (A)/(B) diagnosis of the w19 counterexample.
  - The refutation of (RI') in §6.
- **Not established.**
  - (RI_B) itself, at any `k`, for malnormal `B`. At `k = 1` it is
    exactly (A) + (B) in the case `f(u) ≠ f(w)`.
  - (G_j), and (O).
- **Most promising next steps.**
  1. Prove (A) at `k = 1` for *all* `B`. It held in every non-malnormal
     case too, so malnormality should not be needed. A lift argument is
     needed: every reduced loop of `P` lifts to a path of `Γ_X` whose
     jumps lie in `ker m`.
  2. Prove (B) at `k = 1` for malnormal `B`: the fold closure of one pair,
     intersected with `ker f`, is again generated by one pair. The w19
     example shows exactly how this uses malnormality. A non-malnormal
     host lets `≈` meet two different conjugate fibres.
  3. A worst-case k = 2 search, instead of random sampling. For example,
     take the pairs of the w17 reduction on actual `Q^(j)` levels, and
     test `(Int_B)` with `|S| = 2`.

## 8. Reproduction

All commands run from `experiments/fpbs-overfold-malnormal-host-census-2026-09-17/`.

- Selftest: `python3 census.py selftest`.
- k = 1 census: `python3 census.py k1 13 400 L1`, `k1 11 600 rand`,
  `k1 14 400 L1overL2`, `k1 12 150 nonmal`. Outputs are in `k1_*.txt`.
- k = 2 census: `python3 census.py k2 21 150 L1overL2 400`. Output in
  `k2_L1overL2_s21.txt`.
- One-pair split: `python3 analyze.py 33 60 L1`, `31 60 L1overL2`,
  `35 60 rand`. Outputs in `analyze_*.txt`.
- w19 diagnosis: `python3 analyze_w19.py`. Output in `analyze_w19.txt`.
- Non-malnormal split: `python3 analyze.py 12 60 nonmal`. Output in
  `analyze_nonmal_s12.txt`.
- Split on the violating hosts: `python3 analyze_viol.py`. Output in
  `analyze_viol.txt`.
- Multi-pair split: `python3 analyze.py 34 40 L1overL2 2 100` and
  `32 40 rand 2 100`.
- Two-step certificates: `python3 analyze2.py 41 40 L1overL2 2 100`,
  `42 40 rand 2 100`, `43 30 nonmal 2 100`, `44 30 L1 3 80`.

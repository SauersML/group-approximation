# Independent chord graphings over a malnormal stage: union bound, relative positions, two-step rigidity

Worker `swarm-0917-w14-w14-fp-last1`, lane LAST MILE toward
`fpbs-fixed-price-universal`, attacking the survivor P2 (factor-of-iid long
chords) of `fpbs-mal-bernoulli-single-stage-floor`, restricted to its
simplest shape: **independent** chords with an **arbitrary** label law.
Code and outputs: `experiments/fpbs-iid-chord-union-bound-2026-09-17/`.

## 0. Setting

- `F = F(a, b)`, `K = <a, c>`, `c = b a b^{-2}`. `K` is malnormal of rank 2.
  Its Stallings core is `0 -a-> 0`, `0 -b-> 1`, `1 -a-> 2`, `1 -b-> 2`. This
  is the stage pair `H_n < H_{n+1}` of `Gamma_mal` with `b = b_{n+1}`.
- Take `F` acting on `(Z, nu)^F` by the Bernoulli shift, `nu` non-atomic, so
  the action is free. The orbit of `x` is identified with `F` via `y -> y x`.
  The `E_K`-class of the point `y x` is the right coset `K y`.
- **Independent chord graphing** `Theta(epsilon, p)`. Fix `epsilon in (0, 1]`
  and a probability `p` on `F \ K`. Every point `z` is *active* with
  probability `epsilon`, independently of everything else. An active point
  draws a label `h ~ p` and carries the edge `(z, h z)`. Realise this by
  reading a measurable function of `z(1)`: the orbit points `y x` read the
  distinct coordinates `x(y^{-1})`, so the choices are iid along each orbit.
  The measure of `Theta` is `epsilon`.
- The question is when `E_K v Theta(epsilon, p) = E_F`. This happens iff
  `(x, b x)` lies in `E_K v Theta` for a.e. `x`.

## 1. Union bound over vertex-simple class paths

**Class graph.** Its vertices are right cosets `Ky`. Each edge `(z, h z)`
of `Theta` joins `Kz` to `Khz`. `(x, bx) in E_K v Theta` iff `K` and `Kb`
are joined in this graph, which happens iff they are joined by a
*vertex-simple* path `K = C_0, C_1, ..., C_n = Kb`.

**Relative position.** For classes `A = Ky`, `B = Kz`, put
`D(A, B) = K z y^{-1} K`, a double coset in `K\F/K`. It is well defined,
invariant under right multiplication `C -> C g`, and `D(B, A) = D(A, B)^{-1}`.
The chord `(z, hz)` joins classes at relative position `KhK`. Conversely, a
class `C` with `D(A, C) = KhK` is reached from `A` by exactly one `h`-chord:
its source is a point `k y` of `A`, and two such points `ky`, `k'y` give the
same target iff `k k'^{-1} in h^{-1} K h ∩ K = 1` (malnormality, `h ∉ K`).

**Lemma 1 (union bound).** Let `q(D) = p(D) + p(D^{-1})` for each double
coset `D ≠ K`. Let `N_n(D_1, ..., D_n)` be the number of vertex-simple class
sequences `K = C_0, ..., C_n = Kb` with `D(C_{i-1}, C_i) = D_i`. Then

```text
P[(x, bx) in E_K v Theta]  <=  sum_{n>=1} epsilon^n  sum_{D_1..D_n} q(D_1)...q(D_n) N_n(D_1..D_n).
```

*Proof.* Fix a sequence `C_0..C_n` as above, with `C_{i-1} = K y`,
`C_i = K g y`, `g in D_i`.
1. A point `z = k y` of `C_{i-1}` has an edge into `C_i` iff it is active and
   its label lies in `L_z = K g k^{-1}`.
2. The sets `L_{ky}` (`k in K`) are pairwise disjoint: `Kgk^{-1} = Kgk'^{-1}`
   forces `k^{-1}k' in g^{-1}Kg ∩ K = 1`. Their union is `D_i`. Hence
   `sum_{z in C_{i-1}} p(L_z) = p(D_i)`.
3. Likewise, the points of `C_i` whose edge goes back into `C_{i-1}` have
   label sets that partition `D_i^{-1}`.
4. So step `i` is present only if some *source* `z_i` (a point of `C_{i-1}`
   or of `C_i`) is active with a label in its set. The weights of these
   events sum to `epsilon q(D_i)`.
5. Choose a source for every step. If two steps `i < j` share a source `z`,
   then `z` lies in a class common to both steps, so `j = i + 1` and
   `z in C_i`. Its single edge would then have to land in both `C_{i-1}` and
   `C_{i+1}`. These are distinct by vertex-simplicity, so the event is
   empty.
6. Distinct sources are independent. Summing the product of the weights over
   all source choices gives `epsilon^n prod q(D_i)` per class sequence.
   Summing over sequences and over `n` gives the bound. ∎

**Corollary 1.** Suppose `N_n(D_1..D_n) <= rho^n` for all `n` and all
`D_i`. Since `sum_D q(D) <= 2`, the bound of Lemma 1 is at most
`sum_n (2 epsilon rho)^n`. This is `<= 1/2` once `epsilon <= 1/(6 rho)`.
For such `epsilon`, `E_K v Theta(epsilon, p) ≠ E_F` for **every** label
law `p`, including laws with unbounded labels. The floor
`epsilon_0 = 1/(6 rho)` is uniform in `p`.

**Remark (label length drops out).** `N_n` depends on the labels only through
their double cosets. Uniformity "in label length" therefore means uniformity
over sequences in `K\F/K`, which is a countable set. Two labels
`h, k h k'` (`k, k' in K`) are the same chord type for connectivity purposes.

## 2. Tree picture and two-step rigidity

`T` is the right Cayley tree of `F`, and `F` acts on it freely by left
multiplication, preserving labels. `T_K` is the convex hull of the vertex
set `K`, that is, the lift of the core through `1`. To the class `Ky`
attach the hull `X(Ky) = y^{-1} T_K`. Then:
- **(S) Stabilizers.** `Stab_F(T_K) = K`. It contains `K` and acts freely and
  cocompactly on `T_K`, hence contains `K` with finite index. A finite-index
  overgroup of a malnormal subgroup is the subgroup itself: if `s` lies in
  the overgroup, then `sKs^{-1} ∩ K` has finite index in `K`, so it is
  nontrivial. So `Ky -> X(Ky)` is a bijection onto the translates of `T_K`.
  It intertwines right multiplication by `g` on classes with left
  multiplication by `g^{-1}` on hulls, and
  `Stab(X(Ky)) = y^{-1} K y` acts freely on the vertices.
- **(F1) Overlap.** Distinct translates share at most 3 vertices.
  - A common vertex has different core types in the two copies. If the types
    were equal, `v = k r_u = g k' r_u` would force `g in K`.
  - A common subtree immerses into the off-diagonal product graph of the
    core.
  - `overlap.py` shows that this graph has two components. Each is a tree on
    3 vertices.
  - An immersion of a tree into a finite tree is injective.
- **Projections.** For translates `X ≠ Y`, write `pi_X(Y) ⊆ X` for `X ∩ Y`
  when this is nonempty, and otherwise for the nearest vertex of `X`. By
  (F1), `|pi_X(Y)| <= 3`. If `g` stabilizes `X`, then
  `pi_X(gY) = g pi_X(Y)`.

**Lemma 2 (two-step rigidity).** Let `A ≠ B` be classes and `D, D' ≠ K`
double cosets. Then

```text
#{ C ∉ {A, B} : D(A, C) = D,  D(C, B) = D' }  <=  12.
```

*Proof.* Let `M` be this set and fix `C_0 in M`.
1. `Stab(A)` (right multiplication) acts transitively on
   `{C : D(A, C) = D}`, since `K h k y = (K h y)(y^{-1} k y)`. By
   malnormality it acts freely there.
2. Hence, in the tree, every `C in M` has `X_C = kappa X_{C_0}` for a unique
   `kappa in Stab(X_A)`. By the same argument `X_C = lambda X_{C_0}` with
   `lambda in Stab(X_B)`.
3. Put `P = pi_{X_A}(X_B)`, `Q_C = pi_{X_A}(X_C) = kappa Q_{C_0}` and
   `E = pi_{X_B}(X_A)`. Each has at most 3 vertices.
4. *Exceptional* `C` (`Q_C ∩ P ≠ ∅`): `kappa` sends some vertex of
   `Q_{C_0}` to some vertex of `P`. By freeness `kappa` is determined by that
   pair, so there are at most 9 such `C`.
5. *Generic* `C` (`Q_C ∩ P = ∅`): the tree geometry is as follows.
   - `X_C ∖ X_A` lies in the components of `T ∖ X_A` attached at `Q_C`.
   - `X_B ∖ X_A` lies in the components attached at `P`.
   - Therefore `X_C ∩ X_B = ∅`, and the bridge (unique geodesic) from `X_C`
     to `X_B` runs through `X_A` and ends at a vertex `e_C in E`.
   - `lambda` fixes `X_B` setwise and maps the bridge of `X_{C_1}` onto the
     bridge of `X_C`, for any generic reference `C_1`. So
     `lambda e_{C_1} = e_C`. Because the action on vertices is free,
     `lambda`, and hence `C`, is determined by `e_C in E`.
   - So there are at most 3 generic `C`.
6. In total `|M| <= 9 + 3 = 12`. ∎

The bound is uniform in `D`, `D'` and in the position of `A`, `B`. So two
chords of arbitrary length can close a detour between two given classes in
at most 12 ways. This is the `n = 2` case of the uniform count that
Corollary 1 needs: `N_2(D_1, D_2) <= 12` for all `D_1`, `D_2`. It says more
than that case, because Lemma 2 allows arbitrary endpoints.

## 3. Counting data

`simple.py` counts `N_n` directly. It enumerates vertex-simple class paths
meet-in-the-middle, and the `K`-syllables `k` are truncated at length `L`.
Two truncations are compared.

| run | result |
|---|---|
| `two_step.py 3 3 8 10`: `N_2`-type count, 21 target classes, 46 labels with `\|h\| <= 3` | values in `{0, 1, 2}`, max 2 at `(t, h_1, h_2) = (b, B, bab)`; 382 of 44436 entries still move between `L = 8` and `10` (`two_step_out.txt`) |
| `r2_scan.py`, `r2_long.py` (naive `R_2`, which equals `N_2` since `n = 2` walks are simple) | `R_2 <= 2` for all labels with `\|h\| <= 3`, and for 60 built long pairs of length up to 14, stable between `L = 12` and `16` |
| `simple.py 1 3 8 12` (label `b` only) | max `N_3 = 2`, sum over the 8 signed sequences 12, stable |
| `simple.py 1 4 8 10` (label `b` only) | max `N_4 = 5`, sum 60, stable. The sums 12 and 60 agree with the single-label nerve counts of `fpbs-mal-stage-block-sprinkling-threshold` (3, 12, 60, 336, 2016). |
| `s3_long.py 2 30 8 10`: random, folding and periodic long labels, `n = 3`, `\|h\| <= 16` | max `N_3 = 1`, 12 sequences tested, all stable (`s3_long_out.txt`) |
| `s3_mid.py 6 8 10`: middle label `h_2 = u k v` with a buried `K`-syllable `k` of length `ell`, `n = 3` | `ell = 1`: max `N_3 = 3` at `(B, bab, B)`; `ell = 2`: max `N_3 = 3` at `(B, baab, B)`; both stable. Runs with `ell >= 3` did not finish within the time budget (`s3_mid_out.txt`) |

The runs `simple.py 2 3 8 10` (all labels with `|h| <= 2`, `n = 3`) and
`simple.py 1 5 8 10` timed out and are not reported.

**Walks versus simple paths.** Non-backtracking walks are not enough. With
the single label `b`, the non-backtracking walk count `R_4^{nb}(b, b, B, b)`
is already 1803 at `L = 12` (`rn_nb_b4_out.txt`; only one truncation was
run), against the simple count of at most 5. The naive walk count `R_3`
grew with `L`. The excess walks revisit classes: they wind around triangles
of the class graph. Vertex-simplicity is essential, and Lemma 1 is set
up so that it needs only simple paths.

## 4. The open hole and where it could fail

**Hole.** `fpbs-mal-simple-chain-count-uniform`: `N_n(D_1..D_n) <= rho^n`
uniformly in the double cosets. Lemma 2 is its `n = 2` case.

**Why Lemma 2 does not iterate directly.** Lemma 2 pins a middle class `C`
by one vertex of a projection of size at most 3. For `n >= 3` the chain
`X_0, ..., X_n` of hulls can be arranged so that the bridge between two
consecutive hulls runs *along* a third hull `X_j` of the chain. This
happens when the reduced label contains a long path of the core, that is
a long buried `K`-syllable. The overlap is then not bounded by (F1),
because it is a bridge meeting `X_j`, not two hulls meeting each other. The
attachment point along that segment has about `|h|` possible positions, and
freeness of `Stab(X_j)` does not remove that choice, because the other end
of the bridge is not fixed by `Stab(X_j)`.

**Consequence.** Iterating the projection argument gives only
`N_n <= C^n prod_i (1 + |h_i|)^{O(1)}`, and even this is not written out as a
proof. A polynomial count does not give a floor uniform in `p`: with it,
Lemma 1 bounds `P[x ~ bx]` by `sum_n (C epsilon)^n (E(1+|h|)^{O(1)})^n`,
which is only a moment condition.

**Evidence.** In every scan, including buried syllables of length 1 and 2,
`N_3 <= 3` and `N_4 <= 5`, with no growth. So the attachment offsets seem
to be killed by some further rigidity, most likely because the bridge
must also leave `X_j` inside a projection of size at most 3. This is not
proved.

**Test that would refute.** A family `(h_1, h_2, h_3)` with `N_3` growing in
`|h_2|` would refute the uniform count and kill the uniform union-bound
route. It would not refute the floor itself, since Lemma 1 is only an upper
bound.

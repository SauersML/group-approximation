# Depth-shift reduction for overfold domination (O)

Worker: swarm-0917-w17-w17-fp-break (belief breaker), 2026-09-19.
Target: `fpbs-mal-overfold-merges-never-help` (O). Status of target: OPEN.
Scripts and outputs: `experiments/fpbs-overfold-breaker-2026-09-17/`.

## Summary

1. **Coincidence levels.** Every seed type (off-diagonal component of the
   pair graph `C_{j+1} ×_R C_{j+1}`) has a *level* `i ∈ {0, …, j}`: the
   largest `i` with equal images in `C_i`. Level `j` is the lawful type.
   Level `≥ i` means `u_c u_{c'}^{-1} ∈ L_i`.
2. **Depth-shift identity (Lemma D).** Write `deep_j^{≥i}(Q)` for the least
   number of seeds of level `≥ i` whose closure contains `ker m`. Then

   ```text
   deep_j^{≥i}(Q) = deep_{j-i}(Q^{(i)})      and      law_j(Q) = law_{j-i}(Q^{(i)}).
   ```

   Proved below for every `j ≤ 4` and `L_{j+1}`-transitive `Q` (all depths
   used anywhere in the census), modulo the relative-rank form.
   For general `j`, the proof needs one finite combinatorial input (T_j),
   which is checked by computer for `j ≤ 4`.
3. **Consequence (reduction of (O)).** Wherever Lemma D holds (so for
   `j ≤ 4` and `L_{j+1}`-transitive `Q`, and for all `j` given (T)), (O)
   for all `j, Q` is equivalent to

   ```text
   (O')  for every j ≥ 1 and every finite L-set Q:  deep_j(Q) = deep_j^{≥1}(Q),
   ```

   i.e. only the level-0 overfold types (images in `C_1` already differ)
   ever need to be ruled out. All deeper overfold types are handled by
   induction on `j`.
4. **Measure form (proved, all j, no (T) needed).**
   `Q_j(X) ≤ Q_{j-1}(X^{(1)})` and `Q_j^law(X) = Q_{j-1}^law(X^{(1)})`. For
   the Bernoulli shift `ρ`, `ρ^{(1)} ≅ ρ`, so `j ↦ Q_j(ρ)` is
   non-increasing, `Q_j^law(ρ) = Q_0(ρ)`, and (O) at `ρ` is the statement
   that this non-increasing sequence is constant.
5. **Census.** No counterexample in the law ≤ 3 regime at the largest sizes
   reached so far (tables below).

## 1. The type table (computed, `pb.py`, `reduction_check.py`)

Here `C_j` is the Stallings core of `L_j = <a, t_j>`, and `ι` is the
immersion `C_{j+1} → C_j`. "Types" are unordered off-diagonal components
of `C_{j+1} ×_R C_{j+1}`; each is a finite tree (malnormality).

| depth `j` | `|C_{j+1}|` | types | lawful types (size `T_j`) |
|---|---|---|---|
| 0 | 3   | 1    | 1 (3)  |
| 1 | 8   | 12   | 1 (7)  |
| 2 | 20  | 88   | 1 (16) |
| 3 | 49  | 560  | 1 (38) |
| 4 | 119 | 3381 | 1 (91) |

Self-similarity: at depth `j`, the number of types of level `i` is
`N_{j-i}`, with `N = 1, 11, 76, 472, 2821` (so `N_0 = 1` is the lawful
type and `N_j` counts the level-0 types). The largest tree among level-`i`
types has size `T_i`. Level-0 types always have tree size `≤ 3`.
Hence the types of level `≥ 1` at depth `j` number
`1 + 11 + … + N_{j-1}`, which is the total at depth `j − 1`
(1, 12, 88, 560 for `j = 1..4`).

Principal vertices (those of `C_{j+1}` over the base `o` of `C_1`) number
3, 7, 17, 41 for `j + 1 = 2..5`. That is fewer than `|C_j| = 3, 8, 20, 49`.
So the (a, t_1)-core of `L_{j+1}` has vertices that are not in the
(a, b)-core. This is why Lemma D needs input (T) and is not a literal
graph isomorphism.


## 2. Lemma D and its proof (case `i = 1`; iterate for general `i`)

**Scope.** `Q` is a finite `L`-set that is transitive under `L_{j+1}`
(i.e. `Γ_{j+1}(Q)` is connected), and `j ≥ 1`. This is the scope of the
relative-rank form proved in the fp-last1 attempt on the target node. The
random and exhaustive censuses are almost all in this scope.

**Notation.**
- `H = L_{j+1}`.
- `C = C_{j+1}` is the (a, b)-core of `H`.
- `C'` is the core of `H` in the free basis `(a, t_1)` of `L_1`. Via the
  isomorphism `φ : L → L_1`, `C'` is the labelled graph `C_j` with `b`
  read as `t_1`.
- Fix `p ∈ Q`. Then `S = Stab_L(p)`, `K = S ∩ L_{j+1}` and
  `K' = S ∩ L_j`.
- `U_j ⊂ L` is the union of the nontrivial double cosets `H g H` realised
  by pairs of vertices of `C`, one for each type.

**Cited (relative-rank form, target node, fp-last1 attempt).**

```text
deep_j(Q) = min{ k : g_1..g_k ∈ S ∩ U_j,      ⟨K, g⟩ ⊇ K' },
law_j(Q)  = min{ k : g_1..g_k ∈ K' ∩ D_law,   ⟨K, g⟩ = K'  }.
```

A seed with loop `g = u_c u_{c'}^{-1}` has level `≥ 1` iff
`L_1 u_c = L_1 u_{c'}` iff `g ∈ L_1`. Hence

```text
deep_j^{≥1}(Q) = min{ k : g_i ∈ S ∩ L_1 ∩ U_j, ⟨K, g⟩ ⊇ K' }.
```

**Transport.** `Q^{(1)}` has stabiliser `S^{(1)} = φ^{-1}(S ∩ L_1)`, and
`φ^{-1}` carries `K` and `K'` to `K^{(1)} = S^{(1)} ∩ L_j` and
`K'^{(1)} = S^{(1)} ∩ L_{j-1}`. `Q^{(1)}` is transitive under `L_j` because
`Q` is transitive under `L_{j+1} = φ(L_j)`. `φ` also carries `U_{j-1}`
onto `U'`, the union of double cosets `H g H` (with `g ∈ L_1`) realised by
pairs of vertices of `C'`. Applying the cited form at depth `j − 1` and
pushing forward by `φ`:

```text
deep_{j-1}(Q^{(1)}) = min{ k : g_i ∈ (S ∩ L_1) ∩ U', ⟨K, g⟩ ⊇ K' }.
```

Subgroup generation and inclusion are the same in `L_1` and in `L`.

**Input (T_j): `U_j ∩ L_1 = U'`.** Given (T_j), the two minima range over
the same sets, so `deep_j^{≥1}(Q) = deep_{j-1}(Q^{(1)})`. The lawful double
coset `D_law ⊂ L_j` corresponds likewise, since level `j ≥ 1`. So
`law_j(Q) = law_{j-1}(Q^{(1)})`, which is also the known identity
`law_j(Q) = r(Q^{(j)})`. For general `i`, use `U_j ∩ L_i =
φ(U_{j-1} ∩ L_{i-1})`, which is (T_j) intersected with `L_i`. This gives
`deep_j^{≥i}(Q) = deep_{j-1}^{≥ i-1}(Q^{(1)})`, and so on down. The
general case uses `(T_j), (T_{j-1}), …, (T_{j-i+1})`.

**Why (T_j) is a real condition, and how it is checked.**
- Types are the `L`-orbits on off-diagonal pairs of `H\L`. The orbit of
  `(Hx, Hg^{-1}x)` corresponds to `HgH` and is a copy of the Cayley tree
  (malnormality). A pair lies in `V(C)^2` iff `x ∈ T_H ∩ g T_H`. Here `T_H`
  is the minimal `H`-invariant subtree of the Cayley tree `T(L; a, b)`:
  `Hx ∈ V(C)` iff the reduced word `x` is readable in `C` from the base.
  So `HgH` is realised in `C` iff `T_H ∩ g T_H ≠ ∅`. For `C'` the same
  holds in `T(L_1; a, t_1)`.
- Minimal subtrees depend on the basis, so (T_j) is not automatic.
- **Dead end, recorded.** The obvious proof, "every level-≥1 type contains
  a pair of principal vertices and translates to `C'`", is false. There
  are 1, 9 and 64 level-≥1 types with no principal pair at `j = 2, 3, 4`
  (`principal_types.py`, `principal_types_j4.txt`). The (a, t_1)-core has
  vertices outside the (a, b)-core: 3, 7, 17, 41 principal vertices,
  against `|C_j| = 3, 8, 20, 49`.
- **Test.** Let `A`, `B` be subtrees with `1 ∈ A`, and `b ∈ B`. Then
  `A ∩ B ≠ ∅` iff `proj_A(b) ∈ B`. With `A = T'_H` and `B = g T'_H`, write
  `g = p s` in `(a, t_1)`-letters, where `p` is the longest prefix readable
  in `C'`. Then `proj_A(g) = p`, and `p ∈ g T'_H` iff `s^{-1}` is readable
  in `C'`.
- **Result (`doublecoset_check.py`, `doublecoset_j4.txt`).** For
  `j = 1..4`:
  - every level-≥1 type of `C_{j+1}` (1, 12, 88, 560 of them) has its
    double coset realised in `C'`;
  - `C'` has exactly as many types (1, 12, 88, 560).

  The map type ↦ double coset is injective, so the two sets are equal.
  **(T_j) holds for `j ≤ 4`.**
- **Control.** On random `g ∉ H` at `j = 2`, the test accepts 464 of 1404.
  So it discriminates.
- **Independent numerical check** (`reduction_check.py`: 16 random `Q` in
  saved outputs, with `(j, i) = (2,1), (3,1), (3,2)`, plus 6 more at
  `(2,1)` with `n = 4` in an unsaved first run). On every `Q` these agree between the
  level-`≥ i` seeds at depth `j` and all seeds at depth `j − i` on
  `Q^{(i)}`:
  - the number of distinct single-seed closures;
  - the number of those that promote;
  - the number of promoting pairs when no single seed promotes.

  Outputs: `redcheck_*.txt`.

**Status of Lemma D.**
- Proved for `j ≤ 4` and every `i ≤ j`, for `L_{j+1}`-transitive `Q`,
  modulo the cited relative-rank form.
- For general `j` it is reduced to the finite statement (T_j), which is
  open in general. Evidence: the self-similar counts of §1.

## 3. Reduction of (O) to level-0 domination

**Corollary R.** Let `J ≤ 5`, so that Lemma D holds for all `j < J`. For
all `j < J` and all `L_{j+1}`-transitive `Q`, (O) at `(j, Q)` is implied by

```text
(O'_j)   deep_j(Q) = deep_j^{≥1}(Q),
```

together with (O) at `(j−1, Q^{(1)})`.

*Proof.* Chain the equalities:
- `deep_j(Q) = deep_j^{≥1}(Q)` by (O'_j);
- `deep_j^{≥1}(Q) = deep_{j-1}(Q^{(1)})` by Lemma D;
- `deep_{j-1}(Q^{(1)}) = law_{j-1}(Q^{(1)})` by (O) at `(j−1, Q^{(1)})`;
- `law_{j-1}(Q^{(1)}) = law_j(Q)` by Lemma D.

Conversely (O) implies (O'_j), since `deep ≤ deep^{≥1} ≤ law`. ∎

So (O) holds at all depths iff, at every depth, the level-0 seeds (whose
two ends already differ in `C_1`) are useless. These form `N_j` of the
types (11, 76, 472, 2821 at `j = 1..4`). Every one of them has tree size at
most 3. At `j = 1`, (O'_1) is (O) itself.

**What this changes.**
1. The target is no longer a statement about a growing family of
   increasingly deep overfold types. It is one statement per depth about
   the thin level-0 types: tree size `≤ 3`, i.e. each such seed forces at
   most 3 identifications before transitivity inside the fibres.
2. **Compounding risk for the weak form.** The weak form
   `deep_j ≥ c · law_j` with `c` uniform in `j` does *not* follow from a
   weak level-0 statement `deep_j ≥ c · deep_j^{≥1}`: iterating gives only
   `deep_j ≥ c^j law_j`. The weak form needs either (O'_j) exactly
   (`c = 1`) or a direct argument across all levels at once.
3. A counterexample to (O) must exist already at the *shallowest* depth
   where it appears, with a level-0 seed in every minimal witness. So the
   search space for a break can be restricted to witnesses containing a
   level-0 seed.

## 4. Measure form: `Q_j(ρ)` is non-increasing in `j`

This needs no (T). The definitions are those of
`fpbs-mal-depth-promotion-equals-overfold-merge-number`: `Q_j(X)` is the
least cost of a graphing `Ψ ⊂ E_{X|L}` with
`E_{X|L_{j+1}} ∨ Ψ ⊇ E_{X|L_j}`, and `Q_j^law` restricts `Ψ` to labels in
`L_j`.

**Proposition M.** Let `X^{(1)}` be the `L`-action `x·w := x·φ(w)`. Then

```text
Q_j(X) ≤ Q_{j-1}(X^{(1)})   and   Q_j^law(X) = Q_{j-1}^law(X^{(1)})   (j ≥ 1).
```

*Proof.*
- `E_{X^{(1)}|L_i} = E_{X|L_{i+1}}` for every `i`, because
  `φ(L_i) = L_{i+1}`.
- A graphing `Ψ ⊂ E_{X^{(1)}|L} = E_{X|L_1}` with
  `E_{X^{(1)}|L_j} ∨ Ψ ⊇ E_{X^{(1)}|L_{j-1}}` is a graphing inside
  `E_{X|L}` with `E_{X|L_{j+1}} ∨ Ψ ⊇ E_{X|L_j}`, of the same cost. So the
  first inequality holds.
- For the law version, the admissible graphings on the two sides are
  literally the same sets (subsets of `E_{X|L_j}`), so equality holds. ∎

**Bernoulli.** For `ρ = [0,1]^L`, the restriction to `L_1` is the
Bernoulli shift of `L_1` with base `([0,1]^{L_1\L}, Leb)`. This base is a
standard nonatomic probability space, because `[L : L_1] = ∞`. So
`ρ^{(1)} ≅ ρ` as `L`-actions, via `φ`. Hence:

```text
Q_0(ρ) ≥ Q_1(ρ) ≥ Q_2(ρ) ≥ …      and      Q_j^law(ρ) = Q_0(ρ) for all j.
```

Consequences for the route `fpbs-mal-depth-floor-from-overfold-domination`:
- The floor asked for, `inf_j Q_j(ρ) > 0`, is the limit of a
  non-increasing sequence.
- (O) at `ρ`, i.e. `Q_j(ρ) = Q_j^law(ρ)`, is the statement that this
  sequence is constant.
- Any overfold saving at one depth `j_0` persists at every depth
  `j ≥ j_0`.
- The floor fails iff the one-step savings `Q_{j-1}(ρ) − Q_j(ρ) ≥ 0`
  sum to `Q_0(ρ)`.
- Proposition M is the measure shadow of Lemma D: graphings in `E_{X|L_1}`
  are the level-`≥ 1` seeds.

## 5. Census in the law ≤ 3 regime (pullback model, `smallk.py`)

`smallk.py` builds `Γ_{j+1}(Q) = Q ×_R C_{j+1}` and lists one seed per
(type, point of `Q`). By the translation invariance of fold closure, this
covers every single-seed closure. It then decides:
- `L1` / `D1`: some single lawful / arbitrary seed promotes;
- `L2` / `D2`: the same for pairs of seeds (deduplicated by single
  closure).

A **FLAG** (certified `deep < law`) is `D1 ∧ ¬L1` or `D2 ∧ ¬L2`.

Validation: `exh 2 5` reproduces the earlier exact census
(`exh_n5_j2.txt`: 38 / 50 / 9). That run was interactive, and its output
was not saved.

| run | levels | law = 1 | law = 2 | law ≥ 3 (deep ≥ 3) | FLAG |
|---|---|---|---|---|---|
| exh `j=1, n=7` (all classes) | 4163 | 393 | 3278 | 492 | 0 |
| exh `j=2, n=6` (all classes) | 624 | 90 | 433 | 101 | 0 |
| exh `j=3, n=4` (all classes) | 26 | 16 | 8 | 2 | 0 |
| exh `j=4, n=3` (all classes) | 7 | 4 | 3 | 0 | 0 |
| rand `j=1, n=14` | 300 | 0 | 105 | 195 | 0 |
| rand `j=2, n=9` | 100 | 0 | 73 | 27 | 0 |
| rand `j=3, n=8`, singles only | 100 | 4 | — (96 have law ≥ 2, deep ≥ 2) | — | 0 |
| rand `j=4, n=5`, singles only | 40 | 10 | — (30 have law ≥ 2, deep ≥ 2) | — | 0 |

In the singles-only rows, "law ≥ 2, deep ≥ 2" means no single seed of any
type promotes. So no single overfold seed beats the lawful count there.

## 6. Where the break attempt stands

- **No counterexample.** 5 exhaustive and 4 random censuses (above) give
  0 FLAGs. The largest are: every transitive `Q` with `n = 7` at `j = 1`;
  `n = 6` at `j = 2`; `n = 4` at `j = 3`; `n = 3` at `j = 4`.
- **The break must be level-0.** By Corollary R, a minimal counterexample
  (least `j`) has every minimal witness using a level-0 seed. These seeds
  have tree size `≤ 3`. A future hunt should restrict to witnesses that
  mix level-0 seeds with lawful ones.
- **Weak form is fragile.** A uniform constant `c` in `deep ≥ c · law`
  cannot be obtained level by level (compounding `c^j`). Either prove
  (O'_j) exactly, or bound all levels at once.
- **Open inputs of this artifact.**
  - (T_j) for `j ≥ 5`.
  - Lemma D for `Q` that are not `L_{j+1}`-transitive. This is the
    groupoid version of the relative-rank form. It is not claimed here.

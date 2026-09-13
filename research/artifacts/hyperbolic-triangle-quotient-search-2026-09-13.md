# Complete quotient searches for the four (A_7, A_7, A_8) hyperbolic triangle candidates

Lane `ex-hyperbolic-triangle-search`, 2026-09-13. Computed on MSI with GAP 4.14
(`module load sagemath/10.7`, `sage -gap`). Code and raw output are in
`experiments/hyperbolic-triangle-search/`. Everything here is evidence about
`hyperbolic-simple-triangle-group-without-finite-quotients`. It does not decide that claim.

## 1. The groups

`G_i = < p, q, r | R_A(p,q), R_B(q^e1, r), R_C(r^e2, p^e3) >` for `i = 1..4`:
- vertex groups `A = <p,q> ≅ A_7`, `B = <q,r> ≅ A_7`, `C = <r,p> ≅ A_8`;
- edge groups `Z/7`, trivial face group, half-girth type `(3,3,4)`.

The data are copied verbatim from `simple-vertex-triangle-quotient-search-2026-09-12.md` §2
into `cands.g`. `R_X(u,v)` are the relators of `X` in its generating pair `(x_X, y_X)`.
Every nontrivial homomorphism `G_i -> S` is injective on `A`, `B` and `C`, because they are simple and
share nontrivial edge groups.

## 2. Method: embedding classes and double cosets

Notation: `x^g = g^{-1} x g`; for a homomorphism `β` put `β^g(y) = β(y)^g`.

**Lemma (completeness).** Let `S` be a finite group. Fix representatives `α` of the
`S`-classes of homomorphisms `A -> S`, and `β_0` of those `B -> S`. For fixed `α`, set:
- `t = α(y_A)^{e1}`, `v = α(x_A)^{e3}`;
- `C_t = C_S(t)` and `V = C_{C_t}(v)`.

For each `β_0` with `β_0(x_B)` conjugate to `t`, fix `g_0` with `β_0(x_B)^{g_0} = t`. Put
`β_1 = β_0^{g_0}` and `U = C_S(β_1(B))`, which lies in `C_t`. Then the homomorphisms
`G -> S` extending `α` correspond bijectively to the pairs `(β_0, U h)` with `h ∈ C_t` such that
`u = (β_1(y_B)^h)^{e2}` and `v` satisfy `R_C`. This condition depends only on the double coset `U h V`.

*Proof.* A homomorphism `G -> S` extending `α` is the same as a homomorphism
`β: B -> S` with `β(x_B) = t` such that `x_C -> β(y_B)^{e2}`, `y_C -> v` defines a
homomorphism `C -> S`. Here `r = β(y_B)`.
1. Write `β = β_0^g` for its class representative `β_0`.
2. `β_0(x_B)^g = t = β_0(x_B)^{g_0}` gives `g ∈ C_S(β_0(x_B)) g_0 = g_0 C_t`, so `β = β_1^h` with `h ∈ C_t`.
3. `β_1^h = β_1^{h'}` iff `h' h^{-1}` centralizes `β_1(B)`, that is `h' ∈ U h`.
4. For `w ∈ V`, `β_1^{hw}(x_B) = t`, and the new pair is `(u^w, v) = (u, v)^w`. Relators hold on a pair iff they hold on a conjugate. ∎

Hence
`|Hom(G,S)| = Σ_α |S : C_S(α(A))| · Σ_{β_0} Σ_{passing U h V} |U h V| / |U|`.
The search visits every double coset in `U \ C_t / V`, listed by GAP `DoubleCosetRepsAndSizes`.

**Targets.**
- **`S = S_n`.** Classes of homomorphisms `A -> S_n` are the `A`-sets of degree `n`: multisets of
  transitive types, one per conjugacy class of subgroups of index at most `n`, padded with fixed
  points.
  - For `A_7` the indices up to 30 are `7, 15, 15, 21` (GAP `ConjugacyClassesSubgroups`).
  - Only `A`-sets and `B`-sets are enumerated; `C` is tested by its relators.
  - Every homomorphism into `S_n` from these groups lands in `A_n`, because its image is perfect.
- **Other `S`.** The classes come from GAP `AllHomomorphismClasses`.

**Tests.**
- A cheap necessary filter compares the orders of `uv`, `uv^{-1}`, `u^2 v` and `[u,v]` with those
  in `C`. This is valid because the map on `C` is injective.
- Pairs that pass are checked against all relators of `C` from `IsomorphismFpGroupByGenerators`.
- Every homomorphism reported is checked again against all three relator sets.

## 3. Calibration

- **C1: counts against brute force** (`cal1.g`, `cal1.out`). Take the literal `(A_7, A_7, A_7)` triple of
  `tri_cal2.g` with `e = [1,1,1]`. For `n = 7, 8, 9, 10`, the per-`α` counts from double cosets
  agree with a naive scan over all 7-cycles of `S_n` (2 = 2 each).
- **C2: transitive degree 15.** The same triple into `S_15` yields 4 transitive
  homomorphisms: `A_7` acting on the cosets of both classes of `L_3(2)`. It also yields the
  expected intransitive ones.
- **Lie type** (`run_amb.g`). A literal `(A_8, A_8, A_8)` triple (seed 20260913) maps into
  every target that contains `A_8`. Passing double cosets found:

  | target | `Sp_6(2)` | `L_5(2)` | `O_8^+(2)` | `O_8^-(2)` | `L_4(4)` |
  |---|---|---|---|---|---|
  | passing double cosets | 1 | 2 | 9 | 1 | 2 |
- **Not yet run in this version:**
  - the twisted-exponent calibration `cal2.g`;
  - a total-count cross-check between `SearchSn` and `SearchAmb`.

## 4. Results

| target | homomorphisms from each of `G_1..G_4` | double cosets per candidate | time per candidate |
|---|---|---|---|
| `S_14` to `S_22` | 0 | 35 to 21,679 per degree | under 1 s |
| `S_23` to `S_27` | 0 | 29,911 per degree | 1 to 5 s |
| `S_28`, `S_29`, `S_30` | 0 | 92,547; 272,279; 1,494,241 | 8 s; 11 s; 40 s |
| `Sp_6(2)`, `L_5(2)`, `O_8^+(2)`, `O_8^-(2)`, `L_4(4)` | 0 | 7; 84; 63; 7; 126 | up to 16 s |

No double coset for a candidate passed even the order filter. The double coset counts are the
same for all four candidates, as they should be: they depend only on the orbit types.

**Computational conclusion (calibrated).**
- None of `G_1, …, G_4` acts nontrivially on a set of at most 30 points.
- None maps nontrivially into `Sp_6(2)`, `L_5(2)`, `O_8^+(2)`, `O_8^-(2)` or `L_4(4)`.

## 5. What the zeros mean

- **Degrees up to 14 are forced.**
  - For `n <= 13`, see the support argument in the predecessor artifact, §4.
  - For `n = 14`, the only `C`-set of degree 14 is `8 + 6` fixed points, so `p` is a single 7-cycle.
    Then `A`-orbit types force `A` and `B` to act naturally on `supp p = supp q = supp r`.
    So `C` would preserve a 7-subset of its 8-point orbit, which is impossible.
- **From degree 15 on, no argument I know forces the zero.** `A_7` and `A_8` both act
  transitively on 15 points, and C2 shows that transitive degree-15 homomorphisms are found when
  they exist.
- **Heuristic scale.** Counting in the free-orbit regime gives about `|S|^{-χ_orb}` epimorphism classes onto `S`, with
  `χ_orb = 11537/20160 ≈ 0.572`. The count is larger when edge generators fix many
  points (predecessor artifact). So zeros at this scale are expected whether or not `G_i` has
  a finite quotient. They count against structured quotients, and those are what the
  Lie-type and linear searches target.
- **Scale of earlier searches.** Caprace–Conder–Kaluba–Witzel searched alternating quotients up to degree
  30, sometimes 40, and simple quotients up to order `5·10^7`.
- **`Sp_6(2)` is dead for this shape in general,** not only for these candidates.
  - Around `p`, a configuration needs two copies of `A_7` that contain a common 7-element and are
    not inside one `A_8`.
  - Suppose a 7-element of a group lies in a unique `A_7`, and every `A_7` containing it lies in
    an `A_8` containing it. Then `A = <p,q>` and `B = <q,r>` both sit in the `A_8` that contains `q`,
    and so does `C`.
  - This needs checking for each target and is recorded here only as a heuristic reading
    of the `Sp_6(2)` zero.

## 6. In progress

- **Exact linear representations in characteristic 2, dimension 4** (`lin4.py`). This is a Gröbner
  basis decision over the algebraic closure of `F_2`, covering every `L_4(2^m)` at once.
- **More Lie-type targets:** `Sp_8(2)`, `O_7(3)`, `U_6(2)`, `L_6(2)`, `L_4(8)`.

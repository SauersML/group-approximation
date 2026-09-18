# Sharp test `abaBabcdcDcd`: one-side-kept subgraphings and the `Gamma_mal` overgroup

Worker `swarm-0917-w10-w10-fp-pull`, 2026-09-18. Target node:
`fpbs-morse-deficit-vanishes-for-full-presentations`. The node stays OPEN.

## 0. Setup

- `G = A *_Z B` with `A = F(a,b)`, `B = F(c,d)`, `u = abaBab`, `v = cdcDcd`, and `Z = <u> = <v^-1>`.
  This is the one-relator group of the sharp test `m({abaBabcdcDcd}) = 0?`.
- `S = {a,b,c,d}`. The target is `C_sub(S) = 1 + beta_1^(2)(G) = 3` on Bernoulli.
- A *one-side-kept* subgraphing is `Psi = Phi_{a,b} ∪ F` with `F ⊆ Phi_{c,d}`.
  - It keeps every `a`- and `b`-edge, which has mass 2.
  - For Morse matchings, it matches every cell to a `c`- or `d`-edge.

## 1. Proposition 1: reduction to a relative Cayley problem in `F_2`

**Statement.** Take any free p.m.p. action of `G`. Then `Psi` generates `R_G` iff `F ∪ R_<v>` generates the orbit
relation `R_B` of the restricted `B`-action.

**Proof.**

(<=)
- `<Phi_{a,b}> = R_A`, and `R_<v> = R_<u>` lies in `R_A`.
- So `<Psi>` contains both `R_A` and `R_B`.
- These two generate `R_G`.

(=>)
1. **A path as a word.** Take a `Psi`-path from `x` to `beta x` with `beta` in `B`. By freeness it gives a word
   `w = a_0 g_1 a_1 ... g_k a_k = beta` in `G`.
   - Each `a_i` in `A` is one maximal `Phi_{a,b}` segment.
   - Each `g_j` in `B` is one maximal segment in `F ∪ R_<v>`.
2. **The normal form forces a reduction.** Take `k >= 2`, or `k = 1` with `a_0` or `a_1` outside `Z`. The normal
   form theorem for amalgams then gives one of two cases:
   - an interior `a_i` lies in `Z`;
   - some `g_j` lies in `Z`.
3. **Case: interior `a_i` in `Z`.** Replace that `A`-segment by one `R_<v>`-move. This merges `g_i` and `g_(i+1)`.
4. **Case: `g_j` in `Z`.** Its endpoints are `A`-related. So `a_(j-1) g_j a_j` becomes one `A`-segment.
5. **Induction.** Each case lowers `k`. At the end, `k = 1` with `a_0` and `a_1` in `Z`, or `k = 0`.
   - When `k = 0`, `beta = a_0` lies in `A ∩ B = Z`.
   - In both cases the path lies in `F ∪ R_<v>`. □

**Corollary (intrinsic form).** Restricted to `B`, the `G`-Bernoulli shift is a `B`-Bernoulli shift with nonatomic
base. `B` acts freely on `G`, so `[0,1]^G ≅ ([0,1]^{B\G})^B`. Therefore:

```text
inf { mass(Psi) : Psi one-side-kept, generating } = 2 + RC(v),
RC(v) := inf { mass(F) : F ⊆ Phi_{c,d}, <F ∪ R_<v>> = R }   on the F(c,d)-Bernoulli shift.
```

The lower bound is `RC(v) >= relC(R; R_<v>) >= C(R) - 1 = 1`, because `R_<v>` is hyperfinite.

So this family meets the sharp test's cost exactly when `RC(v) = 1`. That is a question about the rank-2 free group
alone, relative to one cyclic subgroup, with the letters `a, b` gone. For Morse matchings the same reduction works,
because acyclicity is checked coset by coset on the Bass–Serre tree.

## 2. Proposition 2: letter-subgroup certificates exist iff `v` is primitive

**Sufficiency.** Take `S' ⊆ {c,d}` with `H' = <S', v>` of finite index. Then `RC(v) <= |S'|`.
1. Let `N` be the normal core of `H'`. Then `R_N ⊆ <Phi_{S'} ∪ R_<v>>`.
2. Apply Lemma B of `research/artifacts/fpbs-infinite-centralizer-price-one-2026-09-16.md` to `N`, which is normal of
   finite index. The finitely many coset representatives `gamma_j` go on sets `A_j` with `mu(A_j) <= eps 2^-j`.
3. Realise each `gamma_j|A_j` along its Cayley path. This costs at most `|gamma_j| mu(A_j)`.

**Obstruction.** Reaching `RC(v) = 1` this way needs `|S'| = 1`.
- A rank-2 subgroup of finite index `k` in `F_2` has `k = 1`, by the Schreier rank formula `r = k + 1`.
- So `{s, v}` must be a basis, i.e. `v` must be primitive.
- If `v = w^n` with `w` primitive, sparse extra edges suffice as well.

**`v = cdcDcd` is not primitive.**
- Whitehead type-2 moves take its cyclic length from 6 to 5 (`dcDcd`), and no further move shortens it
  (`experiments/fpbs-amalgam-sharp-test-2026-09-17/whitehead.py`).
- By Whitehead's theorem, a primitive word would reduce to length 1.
- The cyclic word is not periodic, so `v` is not a proper power.
- By symmetry the same holds for `u`.

**What this kills.** Every certificate of the form "all edges of one letter, plus sparse edges" dies for both sides.
In Morse language, keeping the `c`-edges and matching each cell to its three `d`-edges is the single-letter matching
of `fpbs-single-letter-morse-matchings-die-on-bernoulli` (`k = 3`). That theorem already kills it.

**What survives.** The sharp test, when restricted to this family, needs *position-varying* matchings of cells to both
`c`- and `d`-edges inside `F(c,d)` relative to `<v>`. This is where the need for a cross-letter invariant
(w9, Prop D) now lives, and it no longer involves `a` or `b`.

## 3. Dead end: the ascending-HNN overgroup `M` of `Gamma_mal`

- **Two generators.** `M = <a,b,t | [t,a], t b t^-1 = b a b^-2>`. Put `a = b^-1 t b t^-1 b^2`. A Tietze move gives
  `M ≅ <b,t | [t, b^-1 t b t^-1 b^2]>`, so every free `M`-action has cost at most 2.
- **The forward direction is vacuous.** Lemma B gives `C(M-action) <= C(Gamma_mal-restriction)`. The `M`-cost is
  already at most 2, so the bound says something new only when the restriction has cost below 2. It says nothing
  about finiteness. On Bernoulli the finite value would be `C(beta) = 2`, by
  `fpbs-mal-fixed-price-iff-bernoulli-finite-cost`.
- **The backward direction is circular.** The pivot hoped that an `M`-action of cost `> 1` would force infinite cost
  on its `Gamma_mal`-restriction. That needs an action-wise statement (S): a free action of `N ⋊ Z` whose
  `N`-restriction has finite cost has cost 1.
  - (S) implies the OPEN `fpbs-bounded-cost-outer-cyclic-extension-price-one`.
  - For `N = Gamma_mal`, the hypothesis (H) of that node is the flagship instance itself.
  - So this route is circular. It joins the class killed by `fpbs-extension-routes-to-finite-cost-are-circular`.

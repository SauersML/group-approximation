# hl-kl-rank-density — rank density for amplified roots (2026-09-14)

Lane target: gap G2-new of `research/artifacts/hl-kl-etale-g1-2026-09-14.md`,
which feeds `amplified-algebraic-roots-in-characteristic-zero` and then
`kl-holds-for-char-zero-linear-sofic-groups`. Everything here is unreviewed.

## 1. The premise and the reduction as the graph uses them

- **ARR(L)** (`linear-sofic-kl-from-amplified-algebraic-roots`): for every tuple
  `a` in `GL_n(L)^k`, every `w` with nonzero exponent sum `m` in `x` and every
  `epsilon > 0` there are `r` and `T` in `GL_{nr}(L)` with
  `rho(w(T ; a (x) 1_r) - 1) <= epsilon`, where `rho` is normalized rank.
- **G2-new (rank density).** For every `a`, `w` and `delta > 0` there are `r` and
  `a'` in `GL_{nr}(L)^k` with `rho(a'_j - a_j (x) 1_r) <= delta` for all `j` such
  that `w(x ; a') = 1` has an exact root.
- **(R1), rechecked at printed generality.** If `rho(a'_j - a_j (x) 1_r) <= delta`
  and `w(T ; a') = 1`, then `rho(w(T ; a (x) 1_r) - 1) <= l_c delta`, where `l_c`
  is the number of constant letters of `w`. Proof: write both values of `w` as
  products of their letters; `rank(prod X_i - prod Y_i) <= sum_i rank(X_i - Y_i)`
  by telescoping, the letters `x^{+-1}` agree, and
  `rank(X^{-1} - Y^{-1}) = rank(X^{-1} (Y - X) Y^{-1}) = rank(X - Y)`. So the bound
  holds for every field and every word.
- **Converse for words with a lonely constant (elementary).** If some constant
  letter `c = a_j^{+-1}` occurs exactly once in `w`, write `w = P c Q`. Given an
  approximate root `T` with defect `epsilon`, replace `a_j (x) 1_r` by
  `a'_j = a_j (x) 1_r h^{+-1}` with `h = P(T)^{-1} w(T ; a (x) 1_r)^{-1} P(T)`
  arranged so that `P h c Q = 1` (for `c = a_j^{-1}` use `h^{-1}` on the other
  side). Then `rank(h - 1) = rank(w - 1) <= epsilon N`, so the approximate premise
  at `(a, w)` is equivalent to rank density at `(a, w)`. For constants occurring
  several times this correction changes every occurrence and the equivalence is
  not claimed.

## 2. Theorem K: rank-close tuples cannot carry new etale roots

Landed as `rank-close-commutant-roots-restrict-to-level-one-roots` with route
`rank-close-commutant-roots-level-one-proof`.

- **Statement.** If `n sum_j rank(a'_j - a_j (x) 1_r) < r` and `T` is a root of
  `w(T ; a') = 1` commuting with every matrix that commutes with all `a'_j`, then
  on a slice `L^n (x) S` of dimension at least `n (r - n sum_j rho_j)` the root is
  `t (x) 1` with `w(t ; a) = 1`.
- **Corollary L.** Etale roots are commutant-compatible (Theorem G), so for
  `delta < 1/(k n^2)` an etale root of a rank-close tuple gives an exact root of
  `a` at level one.
- **Meaning for G2-new.** On tuples with no level-one root, rank density needs
  exact roots that are neither etale nor commutant-compatible. The etale locus
  being Zariski open and dense, Hensel lifting (Theorem E) and genericity of
  unitary tuples all produce etale roots, so none of them can supply rank
  density there.
- **Exact check (Step 3 of the route).** Script
  `research/artifacts/hl-kl-rank-density-2026-09-14-kcheck.py` (standard-library
  `fractions`, about a second), run locally:

```text
X commutes with A: True
X commutes with B+E: True
E rank-one nonzero: True
X does NOT commute with E if u violates S1 (control):
  control commutes with B+E: False
```

## 3. Level-one root scan (in progress)

- Script `research/artifacts/hl-kl-rank-density-2026-09-14-rootscan.py` (Sage 10.7
  in the MSI Singularity image, `sage -python`): for 2 x 2
  rational tuples and all cyclically reduced words of length at most 7 in
  `a^{+-1}, b^{+-1}, x^{+-1}` with exponent sum 1 in `x` and at least one `x^{-1}`,
  decide over the algebraic closure of `Q` whether `w(x ; a) = 1` has a root,
  through a Groebner basis of the entries of `w(T ; a) - 1` and `TY - 1`.
- Tuples: two unitary controls (the dihedral group of order 8, the trivial tuple),
  the `BS(1,2)` affine tuple, the `SL_2(Z)` unipotents, two reflections with a
  hyperbolic product, `(diag(2,1), 1 + E_21)`, the cat map with a unipotent, and a
  generic rational pair.
- The smoke run at length 4 had no words, correctly, since the shortest such
  cyclically reduced word has length 5 (for example `xaXbx`).
- **Length-7 run (MSI job 791703, 41 s):** 1200 words up to rotation. For every
  tuple, every word has a root at level one:

```text
MAXLEN 7 words 1200
TUPLE control_dihedral8 level1_unsolvable 0 of 1200 secs 2.2
TUPLE control_trivial level1_unsolvable 0 of 1200 secs 1.7
TUPLE bs12_affine level1_unsolvable 0 of 1200 secs 2.5
TUPLE sl2z_unipotents level1_unsolvable 0 of 1200 secs 2.8
TUPLE reflections_hyperbolic_product level1_unsolvable 0 of 1200 secs 2.6
TUPLE diag2_lower_unipotent level1_unsolvable 0 of 1200 secs 2.3
TUPLE cat_map_unipotent level1_unsolvable 0 of 1200 secs 3.1
TUPLE generic_rational level1_unsolvable 0 of 1200 secs 4.9
SCAN_DONE
```

- **Caveat.** This run has no unsolvable control, so it does not yet show the
  pipeline can report unsolvability. A second run adds the characteristic-3
  dihedral instance of `amplified-roots-fail-in-odd-characteristic`, where a root
  at level one is known not to exist.
- **What it suggests (not landed as a claim).** Conjecture S: for every `n`, every
  tuple in `GL_n(C)^k` and every `w` with nonzero exponent sum, `w(x ; a) = 1` has
  a root in `GL_n(C)`. That would give `ARR(C)` with `r = 1` and `epsilon = 0`,
  hence `kl-holds-for-char-zero-linear-sofic-groups`. It is at least as strong as
  the unitary case, and no argument is known here.

## 4. Barriers carried over

- **B1 (spectral persistence).** For every word `g` in the constants and every
  `lambda`, `dim ker(g(a') - lambda)` differs from `r dim ker(g(a) - lambda)` by at
  most `(length of g) sum_j rho_j`. So a rank-close tuple keeps every
  non-unimodular eigenvalue of every word of `a` with large multiplicity and is
  never unitarizable when `a` has such a word.
- **B3 (fusion).** Conditional on the unitary root theorem, conjugacy in the
  adjunction descends to similarity of images, so no single-conjugacy consequence
  obstructs in characteristic 0. The generalization to simultaneous conjugacy of
  tuples follows the same way, since similarity of tuples is a linear condition
  plus nonvanishing of a determinant, which is preserved under reduction at a
  dense set of maximal ideals.

# Word problems of elementary groups over minimal subshift algebras

Lane `ex-kazhdan-simple-hyperlinear`, 2026-09-12. Notation as in
`simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md`: `X` is an infinite minimal subshift over
`A`, `R_X = LC(X,F_q) ⋊ Z`, `G_X = EL_3(R_X)`, `S_X = G_X / Z(G_X)`. Word problems are taken with
respect to the finite generating set `e_ij(1)`, `e_ij(u^(±1))`, `e_ij(chi_[x_0=a])`. Changing the
finite generating set does not change the Turing degree.

## Theorem

```text
WP(G_X)  ≡_T  L(X)  ≡_T  WP(S_X).
```

**`WP(G_X) <=_T L(X)`.** Multiply out a word. Each matrix entry is kept in normal form
`sum_(|j|<=r) F_j u^j`, where `F_j` is a table of values on `A^(2r+1)`. The product rule is
`(F u^i)(F' u^j) = (F · F'(shifted by i)) u^(i+j)`, on tables of window length `2r+1+2|i|`. An entry
is `0` in `R_X` iff every `F_j` vanishes on `L_(2r+1)(X)`, and the oracle decides this. So "the
word is `I_3`" is decidable relative to `L(X)`. So is "the word is a scalar `λ I_3`", which gives
`WP(S_X) <=_T L(X)`.

**`L(X) <=_T WP(G_X)` and `L(X) <=_T WP(S_X)`.** For `w = w_0 ... w_(m-1)`:
- `u^(-i) chi_[x_0=a] u^i = chi_[x_i=a]`;
- `chi_w = prod_i chi_[x_i = w_i]` is nonzero iff `w ∈ L(X)`.

A group word for `e_12(chi_w)` is computable from `w`. Products come from `e_12(ab) = [e_13(a), e_32(b)]`,
and conjugation by `u^(±i)` from `[e_13(u^(-i)), e_32(c)] = e_12(u^(-i) c)` followed by
`[e_12(u^(-i) c), e_23(u^i)] = e_13(u^(-i) c u^i)` and a permutation. A nontrivial elementary matrix
is never scalar. So `w ∈ L(X)` iff this word is `!= 1` in `G_X`, iff it is `!= 1` in `S_X`.

## Sturmian subshifts realize every Turing degree

For irrational `α ∈ (0,1)`, let `X_α` be the Sturmian subshift of slope `α`.
- `L(X_α) <=_T α`. A word of length `n` occurs iff the corresponding cell of the circle partition
  by `{-kα mod 1 : k <= n}` is nonempty. That is a finite set of strict comparisons of reals, and
  never an equality.
- `α <=_T L(X_α)`. Sturmian words are balanced: every factor of length `n` has
  `|#1 - nα| < 1`. So `L_n(X_α)` computes `α` to within `1/n`, and an irrational real is computable
  from such approximations.

So `L(X_α) ≡_T α`. Every Turing degree contains an irrational in `(0,1)`.

**Corollary.** For every Turing degree `d` there is an infinite, finitely generated, LEF Kazhdan
group without nontrivial finite quotients, namely `G_(X_α)`, whose word problem has degree `d`.
Isomorphic finitely generated groups have Turing-equivalent word problems, and there are
uncountably many degrees. So these groups fall into uncountably many isomorphism classes. The
Fibonacci subshift, or any Sturmian subshift with computable slope, gives decidable word problem.

**Conditional on `simple-kazhdan-lef-group-from-minimal-subshift` (under review).** The same holds
for the infinite simple Kazhdan LEF groups `S_(X_α)`. They form uncountably many isomorphism
classes, every Turing degree occurs, and the computable-slope ones are finitely generated simple
groups with solvable word problem. Such a group embeds in a finitely presented group
(Boone--Higman--Thompson), and the Boone--Higman conjecture asks for a finitely presented *simple*
overgroup. No such overgroup is known here. Any finitely presented simple overgroup is not LEF,
and whether one can be sofic is exactly the open finitely presented question.

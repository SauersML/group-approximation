---
rg: 2
id: minimal-free-z2-sfts-have-arbitrarily-hard-row-languages
kind: claim
title: For every recursive bound some nonempty minimal free Z^2-SFT has a row language that no algorithm decides within that bound
distinct_from:
  sturmian-language-is-turing-equivalent-to-angle: that is the Turing equivalence L(X_α) ≡_T α for one-dimensional Sturmian shifts, with no time bounds and no finite type; this is a quantitative lower bound for two-dimensional minimal free shifts of FINITE type, and uses the Sturmian node only as its one-dimensional input.
  durand-romashchenko-minimal-sft-simulation: that realizes an effective minimal Z^d-shift as a column projection of a minimal Z^(d+1)-SFT and says nothing about freeness or complexity; this adds freeness (for aperiodic inputs, d = 1) and pushes a time lower bound through the projection.
  full-group-word-problem-iff-recursive-language: that is decidability of the full-group word problem of a minimal Z-subshift iff its language is recursive; this is about time complexity of languages of minimal Z^2 shifts of finite type, with no group attached.
---

**ESTABLISHED** by `minimal-free-z2-sfts-have-arbitrarily-hard-row-languages-proof`.

For a subshift `X ⊆ Σ^(Z^2)` let the **row language** `L_row(X)` be the set of
words `r = r_0 ... r_(n-1) ∈ Σ^n` (`n >= 1`) such that some `f ∈ X` has
`f(i, 0) = r_i` for `0 <= i < n`. Its input size is `n`. For recursive
`R : N -> N`, `F(R)` is the class of sets decidable in time
`C*R(C*n) + C*n + C` for some constant `C` (the convention of
`fp-simple-groups-with-arbitrarily-complex-word-problem` and
`scale-preserving-hard-half-finite-permutations-exist`).

**Theorem.** For every recursive `R : N -> N` there are a finite alphabet `Σ`
and a nonempty subshift of finite type `X ⊆ Σ^(Z^2)` such that

1. `X` is minimal;
2. `Z^2` acts freely on `X` (no configuration has a nonzero period);
3. `L_row(X)` is not in `F(R)`.

Every nonempty minimal SFT `X` has decidable pattern language, so clause 3 is a
pure time lower bound. (A pattern `p` is outside `L(X)` iff for some `N` no
locally admissible `N × N` square around it exists, by compactness; and `p` is
in `L(X)` iff for some `N` every locally admissible `N × N` square contains `p`,
by minimality (uniform recurrence) and compactness. Both are enumerable.) Since a row word is a pattern on `[0,n) × {0}`, the full
pattern language of `X` is at least as hard.

**Consequences.**
- There is no uniform recursive time bound for the languages of nonempty
  minimal free `Z^2`-SFTs. So any kill that bounds the host's word problem
  through a uniform language algorithm for minimal SFTs over `Z^2` (the table
  algorithm of `decidable-group-algebras-have-fp-cantor-crossed-hosts`,
  Attempt 6) does not apply at the level of the subshift alone; it must use
  finite presentation of the host.
- With `alternating-v-full-group-wp-computes-sft-language`, it reduces
  `fp-simple-groups-with-arbitrarily-complex-word-problem` to premise (P2) of
  `boone-higman-via-v-times-aperiodic-sft-full-groups`
  (route `arbitrarily-complex-fp-simple-via-hard-minimal-sft-v-full-groups`).

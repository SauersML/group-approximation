# Model test of the universal-seed identities

2026-09-07.  Independent machine recheck of every identity the universal-seed
region asserts, run on MSI.  This is a *model* test: the ring `C` is realized
concretely and each identity is evaluated there, so a PASS confirms the
identity holds in that model and a FAIL would refute it outright.  The
non-identities below (`s_0t_0 + s_1t_1 != 1`, `a^2 != 1`, `n.1 != 0`) are the
ones that genuinely *need* a model — they cannot be read off the presentation.

Nothing here is Lean.  A green run is evidence, not certification.

## The model

`C = Z<s_0,s_1,t_0,t_1 | t_i s_j = delta_(ij)>` is realized as endomorphisms
of the free abelian group on finite binary words: `s_i` prefixes the letter
`i`, and `t_i` deletes a leading `i` and kills every word that does not start
with `i`.  Elements are represented as total maps on finitely supported
integer combinations of words, so no truncation enters and every operator is
defined on the whole basis.  Equality is tested on all `31` words of length
at most four.  Matrices over `C` are lists of such operators with the usual
product.

## What was checked, and the result

All checks PASS; `FAILURES: 0`.

**The presentation and what it omits.**

- `t_i s_j = delta_(ij)` for all four pairs.
- `s_0t_0 + s_1t_1 != 1` — the model's witness is the empty word, which the
  left side kills.  So the presentation really is the Cohn-type one and not
  the Leavitt one, and `C` is not `M_2(C)`.
- `5.1 != 0`, so `C` has characteristic zero.

**The manuscript hypothesis inside `C`.**

- `e = 1 - s_0t_0` is idempotent, `t_0s_0 = 1`, and `t_1 e s_1 = 1`, the
  single-product fullness witness.

**The signed swap in `EL_4(C)`.**

- `a = e_12(1)e_21(-1)e_12(1)` equals `[[0,1],[-1,0]] (+) I` on the nose, and
  `a a^(-1) = 1`.
- `a^4 = 1` and `a^2 != 1`, so the order is exactly four over `C`.
- For six coefficients `r` — `1`, `s_0`, `t_1`, `s_0t_1`, `s_1t_0 + 2`, `-s_1`
  — all three of

  ```text
  [e_13(r), a] = e_13(r) e_23(r),
  [e_12(1), [e_13(r), a]] = e_13(r),
  ```

  and the fully unwound four-letter word

  ```text
  e_13(r) = ( e_12(1) . e_13(r) a e_13(r)^(-1) a^(-1) . e_12(1)^(-1) )
            . ( a e_13(r) a^(-1) e_13(r)^(-1) )
  ```

  hold.  The last line is the conjugate count itself, checked as an identity
  rather than inferred from the two commutators, which is the part a reader
  is most likely to doubt.

**The corner embedding.**

- The sixteen relations `T_i S_j = delta_(ij)` for the four length-two words.
- `Psi(e_(ij)(r)) = diag(1 + S_i r T_j, 1)` and
  `Psi(e_(ij)(r)) = [e_12(S_i r), e_21(T_j)]` for `(i,j)` in
  `{(0,2),(2,0),(1,3)}` and three coefficients each.
- `jmath` is multiplicative on a sampled pair.

## What this does not check

The MF statements, the compactness step behind `delta_0`, and the
finitely presented cover are analytic and are not touched.  The bound of
sixteen is checked only through its two halves: the four-conjugate swap word
above, and the four-conjugate rank-two bound, which is
`properly-infinite-unit-rank-two-normal-generator` and was rechecked in
`research/artifacts/rank-two-descent-review-2026-09-07.md`, not here.

Faithfulness of the word model is not asserted and is not needed: the
identities are consequences of `t_i s_j = delta_(ij)` and hold in every
model, while the three non-identities are witnessed by this one.

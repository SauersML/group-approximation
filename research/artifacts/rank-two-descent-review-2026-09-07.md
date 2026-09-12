# Rank two for the general ring theorem

2026-09-07.  Audit of a fourth forwarded dossier, a rank descent taking
Theorem B of `non_mf_groups_exist.tex` from `n >= 4` to `n >= 2`.  Every
identity below was re-derived here.  The argument is correct and the
strengthening is new to both the manuscript and the graph.

## What was checked

Throughout `R` is countable unital, `ts = 1`, `e = 1 - st`, `ReR = R`, so
`e^2 = e`, `es = 0`, `te = 0`.

**Two disjoint copies.**  With `sum_(j<m) a_j e b_j = 1`,

```text
v_0 = s^m,  w_0 = t^m,
v_1 = sum_(j<m) s^j e b_j,   w_1 = sum_(j<m) a_j e t^j.
```

The computation rests on `e t^i s^j e = delta_(ij) e` for `0 <= i,j < m`,
which holds because `t^i s^j` is `s^(j-i)` or `t^(i-j)` and `es = te = 0`
kill the off-diagonal cases.  Then `w_0v_0 = w_1v_1 = 1` and
`w_0v_1 = w_1v_0 = 0`.  Conversely `w_1(1 - v_0w_0)v_1 = 1`, so the
complementary idempotent of `s = v_0`, `t = w_0` is full.  The two
conditions are equivalent, and `p_i = v_iw_i` are orthogonal idempotents
each equivalent to `1`, which is proper infiniteness of the unit.  No
relation `v_0w_0 + v_1w_1 = 1` is needed, and that omission is the whole
point: the two copies need not exhaust `R`.

**The rank-two normal generator.**  For `wv = 1`, `ba = 1`, `bv = 0`,

```text
D = diag(1 + vb, 1) = [e_12(v), e_21(b)],
```

verified by multiplying out the four factors: the `(1,1)` entry is
`(1+vb)^2 - vb = 1 + vb + v(bv)b = 1 + vb`, and the three others collapse
on `bv = 0`.  `1 + vb` is a unit with inverse `1 - vb`.  Then
`[D, e_12(ar)] = e_12((vb)(ar)) = e_12(vr)` on `ba = 1`.

For `f = 1 - vw` one has `f^2 = f`, `fv = wf = 0`, and `f`, `vfw` are
orthogonal idempotents equivalent through `vf` and `fw`
(`(fw)(vf) = f`, `(vf)(fw) = vfw`).  Their exchange is

```text
z = vf + fw + 1 - f - vfw,   z^2 = 1,   zf = vf,
```

checked by the standard partial-isometry bookkeeping:
`(1-f-vfw)`, `vf`, `fw` annihilate each other in the required pattern,
`(vf)^2 = (fw)^2 = 0`, `(vf)(fw) = vfw`, `(fw)(vf) = f`.  Since `z^2 = 1`,
`diag(z,z) = diag(z,z^(-1))` lies in `EL_2(R)` by the Whitehead
factorization, and conjugating `e_12(fr)` by it gives `e_12(vfrz)`, which
is in `vR`.  With `r = vwr + fr` every `e_12(r)` is reached, and the signed
permutation reaches the lower roots.  Every elementary generator is a
product of at most four conjugates of `D^(+-1)`.

**Higher rank inside rank two.**  Binary words of a common length in the
`v_i`, with reversed words in the `w_i`, give `T_iS_j = delta_(ij)` for as
many indices as wanted.  With `p = sum_i S_iT_i`,
`jmath(A) = 1 - p + sum_(i,j) S_iA_(ij)T_j` is multiplicative, because
`(1-p)S_k = 0`, `T_j(1-p) = 0` and `T_jS_k = delta_(jk)`, and injective
because `A_(ij) = T_i jmath(A) S_j`.  For `i != j`,
`Psi(e_(ij)(r)) = diag(1 + S_irT_j, 1) = [e_12(S_ir), e_21(T_j)]`, using
`T_jS_i = 0`.  So `Psi` embeds `EL_m(R)` in `EL_2(R)`, and
`Psi(e_12(1)) = D` with `v = S_1`, `w = T_1`, `a = S_2`, `b = T_2`.

**The theorem.**  Given `rho : EL_2(R) -> M` with `M` MF, the rank-four
theorem kills `rho . Psi`, so `rho(D) = 1`, so `rho` is trivial.  For
`n >= 2` each root subgroup of `EL_n(R)` sits in a standard `EL_2(R)` block,
so `rho` kills all of them.

## What is new and what is not

NEW, and authored as nodes:

- `full-idempotent-ring-has-properly-infinite-unit`
- `properly-infinite-unit-rank-two-normal-generator`
- `elementary-rank-descent-to-two`
- `full-defect-ring-non-mf-at-rank-two`
- `properly-infinite-unit-group-is-not-mf`
- `full-defect-ring-rank-two-maximal-cstar-infinite`

ALREADY THERE:

- `binary-leavitt-all-ranks-full-mf-radical` covers `L_(F_2)(1,2)` at every
  rank including one to three, through prefix-code self-similarity.  That
  route needs `sum_u s_ut_u = 1`, so the copies exhaust the unit and
  `R = M_n(R)`; the general ring theorem here needs no such exhaustion and
  no matrix-ring isomorphism.  So §6 of the dossier is a second proof of a
  statement the graph already has, and the manuscript already prints the
  Khanh--Thanh footnote `GL_n(R) = EL_n(R) = R^x` for `n >= 2` in the binary
  case.  Writing the headline as `EL_2(L_(F_2)(1,2))` is therefore already
  licensed by the printed text; the dossier's `R = M_2(R)` route confirms it
  independently.
- `dedekind-infinite-ring-elementary-maximal-cstar-infinite` gives the
  proper isometry at `n >= 4` under the weaker hypothesis that `R` is not
  directly finite, with no fullness.  The new rank-two version is
  incomparable: smaller rank, stronger ring hypothesis.

## Not asserted

No literature priority for the rank-descent lemma, as the dossier says.
Nothing here is formalized; the symbolic checks it reports are not Lean.
A rank-two rewrite of Theorem B would move the printed statement away from
the rank recorded in the existing Lean markers, and those markers do not
transfer.

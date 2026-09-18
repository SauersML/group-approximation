---
rg: 2
id: binary-jacobson-rank-two-lef-proof
kind: route
title: Fold the half-line window onto itself through the inverse-transpose automorphism
target: binary-jacobson-rank-two-elementary-group-is-lef
requires:
  - jacobson-shift-representation-is-faithful
  - lef-implies-operator-mf
artifacts:
  - experiments/jacobson-rank-two-2026-09-17/mirror_lef.py
---

## Proof

Notation is that of the target. `V = C^((N))` has basis `e_0, e_1, ...`, and
`S e_k = e_(k+1)`, `T e_k = e_(k-1)`, `T e_0 = 0`. An element `g` of `M_n(J_C)`
acts on `V^n`. We write `g[p,q] in M_n(C)` for its `(p,q)` block, `p,q >= 0`. By
`jacobson-shift-representation-is-faithful` this representation is faithful,
and the monomials `S^i T^j` form a `C`-basis of `J_C`. So `g` is determined by
its blocks, and everything below is a statement about operators.

**Step 0: band form.** `S^i T^j e_q = e_(q-j+i)` for `q >= j`, and it is `0` for
`q < j`. Its only matrix entries are `1` at the positions `(q-j+i, q)`,
`q >= j`. The Toeplitz matrix of `z^(i-j)` would put `1` at every position
`(p,q)` with `p - q = i - j`. The two differ exactly at positions with `q < j`,
and there `p = q - j + i < i`.

So for each `g in M_n(J_C)` there is `r` such that

```text
g[p,q] = 0                      if |p - q| > r,
g[p,q] = a_(p-q)                if p >= r or q >= r,                     (B)
```

where `π(g) = sum_m a_m z^m` with `a_m in M_n(C)`. In words, `g` is the Toeplitz
operator of its symbol off the corner `[0,r)^2`. Call the least such `r` the
*size* of `g`.

**Step 1: the automorphism.** The anti-involution `*` of `J_C` with `S <-> T` is
well defined, since `(TS)^* = S^* T^* = TS = 1`, and under the faithful action
it is the operator transpose. For `g in M_n(J_C)`, `g^T` means the block
transpose with `*` applied to the entries, which is again the operator
transpose. Transposition reverses products, so for `c in GL_n(C)` the map

```text
φ(g) = c^(-1) (g^T)^(-1) c = c^(-1) (g^(-1))^T c
```

is an automorphism of the group `GL_n(J_C)`.

For symbols, `(B)` shows that the transpose of a Toeplitz matrix with symbol
`a` has symbol `ã^T`, where `ã(z) = a(z^(-1))`. So `π(g^T) = π(g)~^T` and

```text
π(φ(g)) = c^(-1) ((ã)^T)^(-1) c,       a = π(g).
```

This equals `ã` iff `ã^T c ã = c`. Applying `~`, which fixes the constant `c`,
this holds iff `a^T c a = c`, that is `a in O_c(A_C)`.

For `n = 2` and `c = w = [[0,1],[-1,0]]`, every `b` with `det b = 1` satisfies
`(b^(-1))^T = w b w^(-1)`. Hence `O_w = SL_2`, and `T_C = π^(-1) O_w(A_C)`. On
generators, `φ(x_12(t)) = x_12(t^*)` and `φ(x_21(t)) = x_21(t^*)`. For example,
`x_12(t)^(-1)` has transpose `x_21(-t^*)`, and `w^(-1) E_21 w = -E_12`.

Fix `c` and put `H = π^(-1) O_c(A_C)`. It is a subgroup, and on `H`

```text
π(φ(g)) = π(g)~       for every g in H.                                  (Φ)
```

**Step 2: the fold.** Take a finite set `F` in `H` with `1 in F`, and let `r` be
at least the size of every `g`, `φ(g)`, `gh` and `φ(gh)` for `g, h in F`. Take
`N >= 8r + 2`. For `g in F`, define `θ(g) = θ_N(g)` on `C^([0,N) x {1..n})` by
`(FOLD)` in the target. We write `a = π(g)`, `b = π(h)`, and `a_m`, `b_m` for
their coefficients.

*Lemma 1 (band and middle agreement).* `θ(g)[i,j] = 0` if `|i-j| > r`. If
`i, j` lie in `[r, N-1-r]`, then `θ(g)[i,j] = a_(i-j)` whichever branch of
`(FOLD)` applies.

*Proof.* The band statement follows from `(B)` for `g` and for `φ(g)`. For
the lower branch, `i >= r` and `(B)` give `g[i,j] = a_(i-j)`. For the upper
branch, `N-1-i >= r`, so `(B)` for `φ(g)` and `(Φ)` give

```text
φ(g)[N-1-i, N-1-j] = (ã)_((N-1-i)-(N-1-j)) = (ã)_(j-i) = a_(i-j).   □
```

*Lemma 2 (exact multiplicativity).* For `g, h in F`,
`θ(g)θ(h) = θ(gh)`.

*Proof.* Fix `(i,k)` in `[0,N)^2` and consider

```text
Σ = sum_(j in [0,N)) θ(g)[i,j] θ(h)[j,k].
```

By Lemma 1 only indices `j` with `|i-j| <= r` and `|j-k| <= r` contribute.

*Case `i + k <= N-1-2r`.* For every such `j`, `i + j <= i + k + r <= N-1`
and `j + k <= N-1`. So `θ(g)[i,j] = g[i,j]` and `θ(h)[j,k] = h[j,k]`. Every
`j >= 0` with `g[i,j] h[j,k] != 0` satisfies
`j <= min(i,k) + r <= (i+k)/2 + r <= N-1`, so it lies in the window. Hence
`Σ = (gh)[i,k]`, the true operator product. Since `i + k <= N-1`, this is
`θ(gh)[i,k]`.

*Case `i + k >= N-1+2r`.* Put `i' = N-1-i`, and similarly `j'` and `k'`. Then
`i' + k' <= N-1-2r`. For contributing `j`, `i + j >= N-1+r >= N`, and likewise
for `j + k`. So `Σ` equals the sum over `j'` of
`φ(g)[i',j'] φ(h)[j',k']`. By the previous case, run with `φ(g)` and `φ(h)`,
this is `(φ(g)φ(h))[i',k'] = φ(gh)[i',k']`, since `φ` is a homomorphism. That
is `θ(gh)[i,k]`.

*Case `|i + k - (N-1)| < 2r`.* If `|i-k| > 2r`, no `j` contributes, so
`Σ = 0`. Also `θ(gh)[i,k] = 0`, because `r` bounds the size of `gh` and
`φ(gh)`. Otherwise `i` and `k` lie in `[(N-1)/2 - 2r, (N-1)/2 + 2r]`, and
every contributing `j` lies in `[(N-1)/2 - 3r, (N-1)/2 + 3r]`. Since
`N >= 8r + 2`, this is inside `[r, N-1-r]`. So Lemma 1 applies to `g`, to `h`
and to `gh`, and the symbol is multiplicative:

```text
Σ = sum_j a_(i-j) b_(j-k) = (ab)_(i-k) = π(gh)_(i-k) = θ(gh)[i,k].
```

The first equality holds because every `j` with a nonzero term lies in the
window. The three cases exhaust `[0,N)^2`.   □

*Lemma 3 (unit, invertibility, injectivity).* `θ(1) = I`, since `1` and
`φ(1) = 1` are the identity. If `F = F^(-1)`, Lemma 2 gives
`θ(g)θ(g^(-1)) = θ(1) = I`, so `θ(F) <= GL_(nN)(C)`. If `g != h` in `F`, then
by faithfulness `g[p,q] != h[p,q]` for some `(p,q)`. Once `N > p + q + 1`,
the lower branch gives `θ(g)[p,q] = g[p,q] != h[p,q] = θ(h)[p,q]`.   □

**Step 3: conclusions.** We may assume `r >= 1`.

*`C` finite.* Let `F` be finite and symmetric with `1 in F`. Enlarge `N` until
Lemma 3 separates `F`. Then `θ_N : F -> GL_(nN)(C)` is injective. It satisfies
`θ(gh) = θ(g)θ(h)` whenever `g, h in F`, and so whenever `g, h, gh in F`. The
target is a finite group. This is the definition of LEF, so `H` is LEF.

*`C = Z`.* Reduction `ρ_m : J_Z -> J_(Z/m)` is a ring homomorphism commuting
with `*` and with `π`, and `c mod m` is invertible for every `m`. So `ρ_m` maps
`π^(-1) O_c(A_Z)` into `π^(-1) O_c(A_(Z/m))` homomorphically. Given `F`, choose
`m` dividing none of the finitely many nonzero integers
`g[p,q]_(st) - h[p,q]_(st)` that witness `g != h` for `g, h in F` (for example,
`m` larger than all of them in absolute value). Then `ρ_m` is injective on `F`,
and the finite case applied to `ρ_m(F)` gives the model.

*Items 1 and 3* of the target are proved: take `n = 2`, `c = w` for item 1,
and general `(n, c)` for item 3.

*Item 2.* `x_12(t)` and `x_21(t)` have symbols in `SL_2(A_C)`, so
`EL_2(J_C) <= T_C`. LEF passes to subgroups. An LEF group is sofic, via the left
regular permutation representations of the finite targets: distinct elements
of a finite group act on it without common fixed points, and the models are
exact partial homomorphisms. It is hyperlinear for the same reason. It is
operator MF by `lef-implies-operator-mf`.

For `C = F_2`, an operator-MF group `G` has an injective homomorphism into its
MF target, so `Rad_MF(G) = 1`. By `(JR3)` of
`binary-jacobson-mark-dichotomy-holds-from-rank-two`, this is its first
branch.

The head `x_12(Q)`, with `Q = e_0 e_0^*`, satisfies
`φ(x_12(Q)) = x_12(Q^*) = x_12(Q)`. So `(FOLD)` puts `E_12` at the blocks
`(0,0)` and `(N-1,N-1)`, and `θ_N(x_12(Q)) - I` has rank `2`.

**Why rank two, and the negative control.** The fold needs an automorphism of
the group whose symbol is `z -> z^(-1)`: the upper branch of `(FOLD)` is read
from the reflected end. Without it, the untwisted fold `φ = id` realizes the
opposite boundary convention `ST = 1`, `TS = 1 - E_(N-1,N-1)` near `N-1`. The
artifact confirms that the untwisted fold fails multiplicativity on 65 of 200
random words, while the twisted fold passes all 200.

`(Φ)` holds with a constant twist exactly when the symbol group preserves the
form `c`. For `n >= 3`, `EL_n(A_C)` contains `SL_n(C)`. For `C = F_q`, the
natural module of `SL_n(F_q)`, `n >= 3`, is not isomorphic to its dual, so the
group preserves no nondegenerate bilinear form, and no constant twist exists.
This matches `cohn-elementary-group-is-not-lef` (not LEF for `n >= 4`).

**Artifact.** `experiments/jacobson-rank-two-2026-09-17/mirror_lef.py`, run with
`OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1` in about 45 s. Over `F_2`, with 26
generators and 200 random words of length at most 6 at `N = 64`, it checks:

* the formula for `φ` on words;
* exact multiplicativity;
* agreement on the anti-diagonal;
* nontriviality of the images of the head and of the 196 nontrivial words;
* the failure of the untwisted control.

It prints `ALL CHECKS PASSED`.

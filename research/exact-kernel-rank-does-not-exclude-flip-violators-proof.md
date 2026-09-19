---
rg: 2
id: exact-kernel-rank-does-not-exclude-flip-violators-proof
kind: route
title: Swap n disjoint line pairs per J-copy (degrees kept, unit-vector sums), show the homogeneous kernel is zero by line redundancy in 3-spaces, bound the kernel-dirty tuple mass by a block-law count, and rerun Theorem O on kernel-clean tuples, since every use of Phi(x_e) = 0 is local to the tuple
target: exact-kernel-rank-does-not-exclude-flip-violators
requires:
  - star-list-structure-is-circular-on-decodable-yes-inputs
  - dkkms-list-seed-needs-lists-exponential-in-l
  - value-free-star-list-references-put-np-in-rp
artifacts:
  - experiments/ugc-kernel-swap-2026-09-17/check_swapped_j_kernel.py
---

The notation is that of the target. "Theorem O", "Step i of O" and "CIRC" refer
to `star-list-structure-is-circular-on-decodable-yes-inputs` and its route.
"LS Lemma i" refers to the route of `dkkms-list-seed-needs-lists-exponential-in-l`.
Identify each J-copy with `F_2^n \ 0` and write `pts` for its points.

## Step 1: J'-copies exist for n >= 7 (greedy)

Process `i = 1, ..., n` in turn, and keep the set `S` of points already used,
with `|S| <= 6(i-1) < 6n`.
1. **Pick `q`.** Choose `q` with `q, q + e_i ∉ S` and `q ∉ {0, e_i}`. At
   least `2^n - 2 - 2|S| > 2^n - 2 - 12n > 0` points qualify.
2. **Pick the first line.** Choose a line `{a, b, q}` with `a, b ∉ S`
   and `a, b ≠ q + e_i`. The `2^(n-1) - 1` lines through `q` meet only at `q`,
   so each forbidden point blocks at most one of them. Fewer than `6n + 1`
   are blocked.
3. **Pick the second line.** Put `p := q + e_i`, and choose a line
   `{c, d, p}` with `c, d ∉ S ∪ {a, b, q}`. Fewer than `6n + 3` of the lines
   through `p` are blocked.
4. **Swap.** Swap `{a, b, a+b = q}` with `{c, d, c+d = p}`, and add all six
   points to `S`.

Both counts leave a free line once `2^(n-1) - 1 > 6n + 3`, which holds for
`n >= 7`. Then `a + b + c + d = q + p = e_i`, and the `2n` lines are pairwise
disjoint.

**Regularity.** A swap removes one occurrence each of `a, b, a+b, c, d, c+d` and
adds one occurrence of each. So all degrees stay `2^(n-1) - 1`.

**No duplicates.** The new triple `{a, b, c+d}` is not a line, because
`a + b = q ≠ p = c + d`. New triples from different swaps have disjoint
`{a, b}` parts. So the J'-copy is a simple 3LIN system: `M_c` distinct
equations on `2^n - 1` variables, with `M_c = (2^n - 1)(2^n - 2)/6`.

The artifact runs this greedy for `n = 6, ..., 9`, where it succeeds even at
`n = 6`, and checks all of the above (Part A).

## Step 2: the homogeneous kernel is zero

Let `z : pts -> F_2` satisfy every homogeneous equation of a J'-copy. Let `R`
be the set of the `2n` swapped-out lines. Then `z` satisfies
`z(u) + z(v) + z(u+v) = 0` on every line outside `R`.

**Line redundancy.** Take a line `{u, v, u+v} ∈ R` and a point
`w ∉ <u, v>`. The 3-space `<u, v, w>` contains the three lines

```text
{v, w, v+w},   {u, v+w, u+v+w},   {u+v, w, u+v+w}.
```

If none of them is in `R`, adding their three equations gives
`z(u) + z(v) + z(u+v) = 0`. Any line other than `{u, v, u+v}` lies in at most
one 3-space containing `<u, v>`, namely the span of the plane and that line.
There are `2^(n-2) - 1` such 3-spaces, and the other `2n - 1` lines of `R`
block at most `2n - 1` of them. For `n >= 6`, `2^(n-2) - 1 > 2n - 1`, so some
`w` works.

Hence `z(u+v) = z(u) + z(v)` for all distinct `u, v`. So `z` is additive, and
`z = <omega, .>` for some `omega ∈ F_2^n`. The swapped equations then give
`0 = z(a_i) + z(b_i) + z(c_i + d_i) = <omega, e_i> = omega_i` for each `i`.
So `omega = 0`, and `z = 0`.

Copies share no variables, so the kernel of a J'-instance is the direct sum of
the kernels of its copies, which is `0`. The coordinates of an exact kernel map
are homogeneous solutions, so every exact kernel map is `0`. All right-hand
sides are `0`, so `x = 0` satisfies everything, and the instance is a YES input
of value `1`. So J'-instances lie in `P_0 ⊆ P_r` for every `r`.

The artifact checks this by GF(2) rank for `n = 6..9` (Part B). It checks line
redundancy separately, for the swapped-out set and for random sets of `2n`
deleted lines: the kernel is exactly the `n` linear functions (Part C).

## Step 3: the approximate kernel map and its dirty mass

On each copy put `Phi(e_p) := p ∈ F_2^n`, and sum over copies. Every
unswapped equation is a line, so `Phi(x_e) = u + v + (u+v) = 0` there. A
swapped equation has `Phi(x_e) = a + b + c + d = e_i ≠ 0`. So exactly `2n`
equations per copy are dirty, a fraction
`rho = 2n / M_c = 12n / ((2^n - 1)(2^n - 2)) < 13 n 4^(-n)` for `n >= 7`
(Part D prints it).

**Block law.** Consider a tuple `U` of `k` equations with disjoint variable
sets, and let `M = N M_c` and `D = 2^(n-1) - 1`. For a fixed equation `e` and
block `j`, the number of legitimate tuples with `e` in block `j` lies between
`(M - 3kD)^(k-1)` and `M^(k-1)`: each later block avoids at most `3kD`
equations, those sharing a variable with earlier blocks. So

```text
Pr[block j = e]  <=  (1/M) (1 - 3kD/M)^(-(k-1)).
```

This holds whether tuples are drawn i.i.d. with a legitimacy condition or
uniformly among legitimate tuples. Here `3kD/M <= 9k/(N 2^n) <= 9 * 2^(-n)`
for `N >= k`, and `k * 9 * 2^(-n) -> 0` at `n = k - c`. So the factor is
`<= 2` at large `k`. A union bound over blocks and over the `2nN` dirty
equations gives

```text
delta_K  <=  k * 2nN * 2/M  =  2k rho  <  26 k n 4^(-n).
```

The `G_multi` law weights a tuple by its number of edges. That number is the
same for every legitimate tuple, because it depends only on `(k, l, beta)` and
on `dim X_U = 3k`. So the tuple marginal is the one bounded above.

**Genericity.** A J'-instance and the J-instance on the same variables have
the same legitimate tuples with no block in the `2nN` dirty (respectively
removed) equations. On those tuples the two tuple laws agree up to
normalisation. The block-law bound applies to both instances, so the total
variation between the two tuple laws is at most `2 delta_K`. The smoothed
tuple `V` and the map `Phi` depend only on the tuple and the variables. So
`beta_bad(J') <= beta_bad(J) + 2 delta_K`, and `beta_bad(J) < 2^(n-k+1)` by
Step 7 of O.

## Step 4: Theorem O' (Theorem O on kernel-clean tuples)

Call a tuple `U` **good** if it is kernel-clean (`Phi(x_e) = 0` for every
equation `e` of `U`) and `Phi` is onto `X_V`. On tuples that are not good,
define `o*` arbitrarily, for instance balanced at every label.

**Every use of `Phi(x_e) = 0` is local to the tuple.** Going through the routes
of Theorem O and LS, the kernel property is used only in these places.
* **LS Step 1.** `Phi` kills `H'` and `H_U`, and so induces `Phī` on
  `Q = X_V/H'`. LS Lemmas 5 and 7 and (4.1) are per-`V` statements about
  `Phī`, and `H' ⊆ H_U`.
* **LS Step 2.** `y_d(x_e) = x(x_e)` is used for the equations of `U`. LS
  Lemma 3(a) uses `Phi(H_U) = 0` for the member's own `H_U`. LS Lemma 3(b)
  uses the equations of `U`.
* **The growth set.** In LS Lemma 4 and Step 0 of O, `W_U ⊇ L' + H_U` uses
  `phi(H_U) = 0`. This inclusion is what Steps 1, 3 and 5 of O use: the
  free-copy count, the uniformity of `x_e` on `X_U \ W_U`, and the flat-star
  counts.

Everything else uses no kernel property:
* the surjectivity of `Phi` on `X_V`;
* Lemma A;
* Hoeffding;
* the dual injectivity of Step 4 of O, which uses only `Phi(X_U) = F_2^n`;
* the case lemma of Step 5;
* the cross-star term (5.2), which is about the graph law and `sigma` only.

So each per-star and per-copy statement of Theorem O holds verbatim at every
star whose tuple is good. This includes LS Lemma 3 at the A-vertex `(U, L)`
itself: for good `U`, `c(R_C) = c(L)`, and the unfolding of `h_C` at `(U, L)`
is `y_(G(c(L)))|_L`, whatever the other members of `C` are.

**Values are copy masses.** The value of a lift labelling is the `mu` mass of
lift-satisfied constraints. These are the copies, as in the Setting of
`value-free-star-list-references-put-np-in-rp`, and Steps 2 and 6 of O sum
exactly these masses. So a copy at a good tuple is scored by itself, and no
folded conjunction couples it to copies at bad tuples.

**Summation.**
* **Item 1.** Score copies at kernel-dirty tuples as `0`. Step 2 of O then
  gives `val >= v(l) - 2^(l-k) - beta_bad - delta_dirty - delta_K`.
* **Item 2.** Score stars at kernel-dirty tuples as `Pr[T | star] <= 1`. This
  costs at most `delta_K / 2` over the bound `1/2`, next to the `beta_bad`
  line of Step 6 of O. So
  `val <= 1/2 + D_L + E + delta_K <= 1/2 + D^C_L + E + delta_K`.

Here `E` is computed with `beta_bad` of the instance at hand. ∎

## Step 5: Corollary R

Take the CIRC parameters: `l >= 8`, `2^(2-l) <= gamma' < gamma <= 0.105`,
`L <= gamma'^2 2^(k-l-16)`, `c = ceil(log2(1/gamma')) + 12`, `n = k - c` and
`s = n - l`. Take a J'-instance with `N >= k` copies, `x = 0`, and the map
`Phi` of Step 3.

**The error term.** CIRC bounds the terms of `E` that do not vanish:
`1/(2^l - 1) < gamma'/2`, `(L + 1) 2^(-s-1) <= gamma'/16 + 2^(-s-1)`, and
`beta_bad(J) < gamma'/2^11`. Their sum is `< 0.57 gamma'`, and the other terms
tend to `0` as `k -> oo`. By Step 3, `beta_bad(J') <= beta_bad(J) + 2 delta_K`
and `delta_K < 26 k n 4^(-n) -> 0`. So
`E(J') + delta_K < gamma'` for all large `k`.

**Value.** `delta_dirty = 0`, since `x = 0` satisfies everything. Item 1 of O'
gives `val(U_o*) >= 0.6096 - 2^(l-k) - 2^(n-k+1) - 3 delta_K >= 0.605` at
large `k`, because `2^(n-k+1) = 2^(1-c) <= 2^(-11)`. And
`0.605 > 1/2 + gamma` for `gamma <= 0.105`.

**Violation.** Let `W'` be any lift labelling of `U_o*` with
`val >= 1/2 + gamma`, and `Lambda` any list of at most `L` references. Item 2
of O' gives `D^C_L(proj W', Lambda) >= gamma - E(J') - delta_K > gamma - gamma'`.
So the conclusion of (P2) fails at this input.

The J'-instance lies in `P_0 ⊆ P_r` for every `r` (Step 2). As `N` ranges over
the integers `>= k`, this gives infinitely many inputs in `P_r` at which (P2)
fails. So "all but finitely many" fails, (P2) fails for every `r`, and (SF_P)
is false in the CIRC range.

**The splice.** A component with `2^n - 1` variables is recognised as a
J'-copy in constant time. The component has constant size, so brute force
finds an identification with `F_2^n \ 0` under which all but `2n` of its
equations are lines, with the swap structure of Step 1. So Proposition S runs
unchanged with `Phi` from Step 3. ∎

## What the artifact checks

`experiments/ugc-kernel-swap-2026-09-17/check_swapped_j_kernel.py` prints
`ALL PASS` and exits `0` in about 1 second. It covers `n = 6..9`:
* **Part A.** Greedy swaps with fresh points and unit-vector sums; unchanged
  degrees; new triples that are distinct non-lines.
* **Part B.** Swapped kernel `0`, against J-kernel `n`.
* **Part C.** Kernel exactly `n` after deleting the swapped-out lines, or `2n`
  random lines.
* **Part D.** `Phi(v) = v` is dirty exactly on the `2n` new triples, and the
  script prints `rho`.

What is not machine-checked: the Theorem O and LS lemmas, which are quoted
from their routes, and the block-law count of Step 3.

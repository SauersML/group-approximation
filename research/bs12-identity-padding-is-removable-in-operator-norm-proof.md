---
rg: 2
id: bs12-identity-padding-is-removable-in-operator-norm-proof
kind: route
title: Excise deep binary runs by a gauge-spread swap, bound the energy leak blockwise, then split off the padding
target: bs12-identity-padding-is-removable-in-operator-norm
requires: []
---

All norms are operator norms. `P_X` is the orthogonal projection onto a subspace `X`.
An *exact packet* is a pair of unitaries with `C Z C^* = Z^2`. Unitary conjugation of an
exact packet, and orthogonal direct sums of exact packets, are exact packets.

## Step 0. Normal form of an exact packet

Let `(C,Z)` be an exact packet on a finite-dimensional space `K`.

*Spectrum.* `Z` and `Z^2` are unitarily equivalent, so squaring maps the finite set
`spec(Z)` onto itself. It is therefore a bijection, every eigenvalue has a finite
squaring orbit, and `lambda^(2^L) = lambda` forces `lambda` to be a root of unity of odd
order. For `lambda` in `spec(Z)`, write `sqrt(lambda)` for the unique element of
`spec(Z)` whose square is `lambda`. If `Z x = lambda x`, then
`Z^2 (C x) = C Z x = lambda C x`, so `C x` lies in `ker(Z^2 - lambda) = E_(sqrt lambda)`.
Here `E_mu = ker(Z-mu)`. Since `C` is injective and the two eigenspaces have equal
dimension, `C E_lambda = E_(sqrt lambda)`.

*Fixed part.* `sqrt(1) = 1`, so `F = ker(Z-1)` is invariant under `C`, and hence
reducing. `C|F` is an arbitrary unitary.

*Cyclic blocks.* Let `lambda_0 != 1` have squaring orbit
`lambda_j = lambda_0^(2^j)`, `j in Z/L`. Then `C^L` maps `E_(lambda_0)` unitarily onto
itself. Pick an orthonormal eigenbasis `b` of `C^L|E_(lambda_0)`, with `C^L b = mu b`.
For each such `b`, the vectors `e_(-t) = C^t b`, `0 <= t < L`, are orthonormal, since
they lie in the distinct eigenspaces `E_(lambda_(-t))`. They span a subspace invariant
under `C` and `Z`, hence reducing, and different `b` give orthogonal blocks.

On a block, `Z e_j = lambda_j e_j` and `C e_j = w_j e_(j-1)` (indices mod `L`, `|w_j|=1`),
with `lambda_(j-1)^2 = lambda_j`. Conjugating by a diagonal unitary commutes with `Z`
and moves the weights freely, keeping their product `mu`. So we may put all weights
equal to `1`, except one edge of our choice, which carries `mu`.

*Words and depth.* Write `lambda_j = exp(2 pi i theta_j)` with `theta_j` in `[0,1)`.
Since `lambda_0` has odd order `o` dividing `2^L - 1`, `theta_0 = a/(2^L-1)`. Its binary
expansion is purely periodic, given by a cyclic word `w = w_0 ... w_(L-1)`, and
`theta_j = 2^j theta_0 mod 1` is the reading of `w` starting at position `j`. The word
contains both digits, because `lambda_0 != 1`.

A *run* is a maximal cyclic block of equal digits, occupying positions
`d, ..., d+z-1` with `w_(d-1) != w_d`. The *depth* of site `d+i` is `z-i`, the length of
the constant initial block of its reading. So `d` is the deepest site of its run, and
`d-1` is the last site of the previous run and has depth `1`.

A site of depth `q` has reading `0^q 1...` or `1^q 0...`, so `theta` or `1-theta` lies
in `[2^(-q-1), 2^(-q)]`. Since `4t <= 2 sin(pi t) <= 2 pi t` for `t` in `[0,1/2]`,

```text
4^(1-q) <= |lambda_j - 1|^2,        |lambda_j - 1| <= 2 pi 2^(-q).        (D)
```

For `q = 1`, the stronger bound `|lambda-1|^2 >= 2` holds, since then `theta` lies in
`[1/4,3/4]`. Put the weight `mu` on the edge leaving a depth-`1` site. Every run has
one, namely its last site.

## Step 1. Run excision

Fix integers `r >= 1`, `s >= 1`. Work on one cyclic block, in the gauge of Step 0.
Call a run *long* if its length satisfies `z >= s+4r+1`. For each long run
`d, ..., d+z-1`, put

```text
c = d + r,        p = z - s - 2r  (so p >= 2r+1),
segment S = {c, c+1, ..., c+p-1}.
```

The segment starts `r` sites after the start of the run and ends `s+r` sites before
its end. Different long runs give disjoint segments.

*The new packet `(C',Z')`.* Define `C'` to agree with `C` except on the two basis
vectors `e_c` and `e_(c+p)` of each long run, where

```text
C' e_c = e_(c+p-1),        C' e_(c+p) = e_(c-1).
```

Neither edge `c -> c-1` nor `c+p -> c+p-1` carries `mu`, because both leave sites of
depth at least `s+1 >= 2`. So `C e_c = e_(c-1)` and `C e_(c+p) = e_(c+p-1)`, and hence
`C' = C S`. Here `S` is the product, over long runs, of the transpositions
`e_c <-> e_(c+p)`. So `C'` is unitary. It splits the block into cycles:

- for each long run, the *segment cycle* `c+p-1 -> c+p-2 -> ... -> c -> c+p-1`;
- the *rest cycle*, which runs through all sites outside segments in their cyclic
  order, and which jumps from `c+p` to `c-1`.

Define `Z'` to be diagonal, with `Z' = 1` on segment sites. On the rest cycle, let
`Z' e_j = lambda'_j e_j`, where `lambda'_j = exp(2 pi i theta'_j)`. Here `w'` is the
word obtained from `w` by deleting the digits at all segment positions, and
`theta'_j` is the reading of `w'` starting at the position of `j`. The word `w'` still
contains both digits, since each long run keeps `s+2r` of its digits and no other run
is touched.

*Exactness.* On a segment cycle, `Z' = 1`, so `C'Z'C'^* = 1 = Z'^2`. On the rest
cycle, `C'` maps each site to its predecessor in `w'`. The reading of `w'` from the
predecessor, doubled mod `1`, is the reading from the site itself. So
`lambda'_(pred j)^2 = lambda'_j`, which is `C'Z'C'^* = Z'^2` there. The fixed part and
the other blocks are untouched. Hence `(C',Z')` is an exact packet.

*Eigenvalue error.* Let `j` be a rest site. Compare the reading of `w` from `j` with
the reading of `w'` from `j`.
- They agree up to the first segment met, say at index `t_0 >= 1`. Index `0` is `j`
  itself, which is not in a segment.
- From there, `w` continues with `b^(p+s+r) x` and `w'` continues with `b^(s+r) x`.
  Here `b` is the digit of that run and `x != b`.
- So the first discrepancy is at index at least `t_0 + s + r >= s+r+1`.

Two binary expansions that agree in their first `N` digits differ by at most
`2^(-N)`, so `|theta_j - theta'_j| <= 2^(-s-r-1)`. A segment site has depth at least
`s+r+1`, so by `(D)`, `|lambda_j - 1| <= 2 pi 2^(-s-r-1)`. Since
`|exp(2 pi i t)-1| <= 2 pi |t|`,

```text
||Z' - Z|| <= pi 2^(-s-r) <= pi 2^(-s).                                    (1.1)
```

## Step 2. Spreading the swap by a gauge

`C'` differs from `C` by a swap, so `||C'-C||` can be as large as `2`. Conjugate it
away gradually.

*Pairs.* For each long run and each `i` with `-r <= i < r`, let `P_i` be the
two-dimensional space spanned by `e_(c+i)` and `e_(c+p+i)`, in that order.
- The first strands `c+i` fill `[d, d+2r)`. These sites have depth at least
  `z-2r+1 >= s+2r+2`.
- The second strands `c+p+i` fill `[d+z-s-2r, d+z-s)`. These sites have depths
  `s+2r, ..., s+1`.
- Since `p >= 2r+1`, the `2r` pairs of one long run use `4r` distinct sites, all in
  `[d, d+z-s)`. Pairs of different long runs are disjoint.

For `-r < i < r`, both `C` and `C'` map `P_i` onto `P_(i-1)`, weights being `1` there.
In the ordered bases, `C'` acts by the `2x2` matrix `c'_i`, with `c'_0 = sigma` (the
swap matrix) and `c'_i = 1` for `i != 0`, while `C` acts by `1`.

*The gauge.* Let `u = exp(i pi (1-sigma) / (2(2r-1)))`. It is a unitary, since
`(1-sigma)/2` is a projection, and

```text
u^(2r-1) = exp(i pi (1-sigma)/2) = sigma,      ||u - 1|| = |exp(i pi/(2r-1)) - 1| <= pi/(2r-1).
```

Put `g_(-r) = 1` and `g_i = c'_i^* g_(i-1) u` for `-r < i < r`. Then
- `g_i = u^(i+r)` for `i < 0`;
- `g_i = sigma u^(i+r)` for `i >= 0`;
- in particular, `g_(r-1) = sigma u^(2r-1) = sigma^2 = 1`.

Let `W` act as `g_i` on each `P_i` and as the identity on all other basis vectors. Put

```text
C_1 = W^* C' W,        Z_1 = W^* Z' W.
```

This is a unitary conjugate of an exact packet, so it is an exact packet.

*The error in `C`.* Compare `C_1` with `C` on each basis vector.
- *Sources outside all pairs whose targets are outside all pairs.* Here `C_1 = C' = C`.
- *Sources outside all pairs whose targets lie in some `P_(r-1)`.* These are
  `c+r` and `c+p+r`. Here `C_1 = g_(r-1)^* C = C`.
- *Sources in `P_(-r)`.* The targets `d-1` and `c+p-r-1` lie outside all pairs, and
  `g_(-r) = 1`. So `C_1 = C`. The site `c+p-r-1` is a segment site not in a pair,
  because `p >= 2r+1`.
- *Sources in `P_i` with `-r < i < r`.* Here `C_1` maps `P_i` to `P_(i-1)` by
  `g_(i-1)^* c'_i g_i = u`, while `C` acts by `1`.

So `C_1 - C` is a direct sum, over these `2r-1` edges of each long run, of the blocks
`u-1`, with pairwise orthogonal sources and pairwise orthogonal targets. Hence

```text
||C_1 - C|| = ||u - 1|| <= pi/(2r-1).                                       (2.1)
```

*The error in `Z`.* `W` is the identity off the pairs, and every pair site has depth at
least `s+1`. So by `(D)`, `||(Z-1)|_pairs|| <= pi 2^(-s)`, and hence

```text
||W^* Z W - Z|| = ||[Z-1, W]|| <= 2 pi 2^(-s).
```

Together with `(1.1)`,

```text
||Z_1 - Z|| <= ||W^*(Z'-Z)W|| + ||W^* Z W - Z|| <= 3 pi 2^(-s).              (2.2)
```

*The new fixed space.* `F_1 = ker(Z_1 - 1) = W^* ker(Z'-1)` contains the old fixed part
`F`. It also contains every `e_j` with `j` a segment site outside the pairs, since `W`
fixes those vectors. So for every long run,

```text
e_j in F_1   for   d+2r <= j < d+z-s-2r.                                    (2.3)
```

Steps 1 and 2 are applied to every cyclic block of `(C,Z)` at once, with the same `r`
and `s`, and leave `F` alone. The result is an exact packet `(C_1,Z_1)` on `K`
satisfying `(2.1)`, `(2.2)` and `(2.3)` blockwise. The bounds hold globally, because
the constructions respect the orthogonal block decomposition.

## Step 3. The energy leak

Put `E(y) = ||(C-1)y||^2 + ||(Z-1)y||^2`. Both `C` and `Z` preserve the block
decomposition of Step 0, and so does `P_(F_1)`. So both `E(y)` and
`||(1-P_(F_1))y||^2` are sums over blocks, and it suffices to prove the following
lemma on one cyclic block. On `F`, the leak is `0`.

**Lemma 3.1.** On a cyclic block, every vector `y` satisfies
`||(1-P_(F_1)) y||^2 <= a E(y)`, where `a = 4^(s+2r-1) + (2r+1)^2`.

*Proof.* Write `y = sum_j y_j e_j`, `zeta_j = ((Z-1)y)_j = (lambda_j - 1) y_j`, and
`kappa_j = ((C-1)y)_j`. By `(2.3)`,

```text
||(1-P_(F_1)) y||^2 <= sum over excluded j of |y_j|^2.
```

The *excluded* sites are all sites except the ranges `[d+2r, d+z-s-2r)` of the long
runs. Split them into two kinds.

*(i) Shallow sites, of depth `q <= s+2r`.* By `(D)`,
`|y_j|^2 <= 4^(q-1) |zeta_j|^2 <= 4^(s+2r-1) |zeta_j|^2`. At a depth-`1` site, the
stronger bound `|y_j|^2 <= |zeta_j|^2 / 2` holds.

*(ii) Deep excluded sites, of depth `> s+2r`.* In a run of length `z`, the sites of
depth `> s+2r` are `d, ..., d+z-s-2r-1`. If the run is long, the excluded ones among
them are `[d, d+2r)`. If the run is not long, then `z <= s+4r`, so there are at most
`2r` of them. Either way, the deep excluded sites of a run are `d+i` for
`0 <= i < t`, with `t <= 2r`.

Since `(Cy)_(j-1) = w_j y_j` with `|w_j| = 1`, we get
`|y_j| <= |y_(j-1)| + |kappa_(j-1)|`. Telescoping from the depth-`1` site `d-1`, and
using Cauchy--Schwarz on `i+2` terms,

```text
|y_(d+i)|^2 <= ( |y_(d-1)| + |kappa_(d-1)| + ... + |kappa_(d+i-1)| )^2
            <= (i+2) ( |zeta_(d-1)|^2 / 2 + sum_{-1 <= l < t-1} |kappa_(d+l)|^2 ).
```

Summing over `0 <= i < t`, with `sum_{i<2r} (i+2) = r(2r+3) <= (2r+1)^2`, gives

```text
sum_{0<=i<t} |y_(d+i)|^2 <= r(2r+3) ( |zeta_(d-1)|^2 / 2 + sum_{-1 <= l < t-1} |kappa_(d+l)|^2 ).
```

*Disjointness.* The `kappa`-window of a run is `[d-1, d+t-2]`. It is non-empty only
if `t >= 1`, which forces `z > s+2r >= 2r >= t`. So the window lies inside
`[d-1, d+z-2]`. These intervals, over all runs, partition `Z/L`, so the windows of
different runs are disjoint. Each `zeta_(d-1)` is used by exactly one window, namely
that of the run starting at `d`.

*Total.* Add (i) and (ii). The coefficients are as follows.
- Each `|kappa_j|^2` gets a coefficient at most `r(2r+3)`.
- Each `|zeta_j|^2` at a site of depth `>= 2` gets at most `4^(s+2r-1)`.
- Each `|zeta_j|^2` at a depth-`1` site gets at most `1/2 + r(2r+3)/2`.

All three are at most `a`, so the sum is at most `a E(y)`. QED.

**Corollary 3.2.** Let `V` be a subspace with `E(x) <= 2 eps^2` for every unit
`x in V`. Then `theta := ||(1-P_(F_1)) P_V|| <= sqrt(2a) eps`.

*Proof.* Apply Lemma 3.1 to each block component of `x`, and sum. QED.

## Step 4. Split off the padding and rotate

Let `(A,B)`, `(C,Z)` and `eps` be as in the theorem, and let `V = 0 (+) C^k` be the
padding space, so `V^perp = C^n`. For a unit `x in V`, `(A (+) 1_k) x = x`. So
`||(C-1)x|| <= eps`, and likewise for `Z`, which gives `E(x) <= 2 eps^2`.

Build `(C_1,Z_1)` by Steps 1--2 with parameters `r, s`, and put
`delta_C = pi/(2r-1)` and `delta_Z = 3 pi 2^(-s)`. By Corollary 3.2,
`theta <= sqrt(2a) eps`. Assume `theta <= 1/2`.

*4a. The target subspace.* Put `V_1 = P_(F_1) V`. For a unit `v in V`,
`||P_(F_1) v|| >= sqrt(1-theta^2) > 0`, so `dim V_1 = k`. Let `P = P_V` and
`Q = P_(V_1)`. For projections, `||P - Q|| <= max(||(1-Q)P||, ||(1-P)Q||)`.
Indeed, `P - Q = P(1-Q) - (1-P)Q`, and the two terms have orthogonal ranges, so
`||(P-Q)x||^2 = ||P(1-Q)x||^2 + ||(1-P)Qx||^2`. Also `||P(1-Q)|| = ||(1-Q)P||`, by
taking adjoints.
- `||(1-Q) P|| <= theta`, because `P_(F_1) v` lies in `V_1`.
- A unit vector of `V_1` has the form `w = P_(F_1) v / ||P_(F_1) v||` with `v in V`
  a unit vector. Its distance to `V` is at most `||w - v/||P_(F_1)v|| || =
  ||(1-P_(F_1))v|| / ||P_(F_1)v|| <= theta/sqrt(1-theta^2)`.

So

```text
q := ||P - Q|| <= theta / sqrt(1-theta^2) <= 1.16 theta.                     (4.1)
```

*4b. Make `V_1` trivial.* `F_1` reduces `C_1` (Step 0), and `U = C_1|F_1` is unitary.
For a unit `w in V_1`,

```text
||(C_1 - 1) w|| <= ||C_1 - C|| + ||(C - 1) P|| + ||C - 1|| ||P - Q||
               <= delta_C + eps + 2q =: alpha.
```

Here `||(C-1)P|| <= eps` was shown above, and the last term uses `w = Pw + (Q-P)w`.
Write `U` in blocks with respect to `F_1 = V_1 (+) V_1'`, where `V_1' = F_1 ⊖ V_1`:

```text
U = [ U_11  U_12 ]
    [ U_21  U_22 ]
```

- The first column `(U-1)|V_1` has norm at most `alpha`.
- `U_22^* U_22 = 1 - U_12^* U_12`. Let `T = |U_22|` and `U_22 = O T` be a polar
  decomposition, with `O` unitary on `V_1'`.
- Unitarity gives `U_11^* U_11 + U_21^* U_21 = 1` and `U_11 U_11^* + U_12 U_12^* = 1`.
  Since `U_11^* U_11` and `U_11 U_11^*` have the same spectrum on the finite-dimensional
  space `V_1`, `||U_12|| = ||U_21|| <= alpha`.
- So `T^2 >= 1 - min(alpha,1)^2`, and for a unit `x in V_1'`,

```text
||U_12 x||^2 + ||(U_22 - O) x||^2 = <(1 - T^2) x, x> + <(1-T)^2 x, x> = <2(1-T) x, x>
                                  <= 2 (1 - sqrt(1 - min(alpha,1)^2)) <= 2 alpha^2.
```

Put `U_2 = 1_(V_1) (+) O`. Then `U - U_2` has first column of norm at most `alpha`
and second column of norm at most `sqrt 2 alpha`. For a column split
`M = [M_1 M_2]`, `||M||^2 <= ||M_1||^2 + ||M_2||^2`, so `||U - U_2|| <= sqrt 3 alpha`.

Let `C_2` equal `C_1` on `F_1^perp` and `U_2` on `F_1`. Then `(C_2, Z_1)` is exact,
because `Z_1 = 1` on the reducing subspace `F_1`, where the relation reads
`C_2 C_2^* = 1`. Also `V_1` reduces both `C_2` and `Z_1`, and both are the identity on
it. Finally,

```text
||C_2 - C_1|| <= sqrt 3 alpha <= 2 alpha.                                   (4.2)
```

*4c. Rotate `V_1` onto `V`.* Let `X = PQ + (1-P)(1-Q)`. Then
`X - 1 = (1-2P)(P-Q)`, and `1-2P` is unitary, so `||X - 1|| = q <= 0.58 < 1` and `X`
is invertible. Let `Omega = X |X|^(-1)`. `X^* X = QPQ + (1-Q)(1-P)(1-Q)` commutes with
`Q`, so `|X|^(-1)` preserves `V_1`. Also `X` maps `V_1` into `V`, so
`Omega V_1 = V` by dimension. The singular values of `X` lie in `[1-q, 1+q]`, so

```text
||Omega - 1|| <= ||Omega(1 - |X|)|| + ||X - 1|| <= 2q.                        (4.3)
```

Put `C_3 = Omega C_2 Omega^*` and `Z_3 = Omega Z_1 Omega^*`. This is an exact packet,
`V` reduces it, and both are the identity on `V`. Let `(C_0, Z_0)` be its restriction
to `V^perp = C^n`. It is an exact packet in `U(n)`.

*4d. Errors.* `C_3 - (A (+) 1_k) = (C_0 - A) (+) 0`. By `(2.1)`, `(4.2)` and `(4.3)`,

```text
||C_0 - A|| <= ||C_3 - C_2|| + ||C_2 - C_1|| + ||C_1 - C|| + ||C - (A (+) 1)||
           <= 4q + 2(delta_C + eps + 2q) + delta_C + eps
            = 3 delta_C + 3 eps + 8q,
||Z_0 - B|| <= ||Z_3 - Z_1|| + ||Z_1 - Z|| + ||Z - (B (+) 1)||
           <= 4q + delta_Z + eps.
```

*4e. Parameters.* Take `r = s = m = floor(log_4(1/eps)/4)`, so `m >= 2` for
`eps <= 4^(-8)`, and `4^m <= eps^(-1/4)`.
- `a = 4^(3m-1) + (2m+1)^2 <= 4^(3m)/2`, since `(2m+1)^2 <= 4^(3m-1)` for `m >= 1`.
- So `sqrt(2a) eps <= 8^m eps = 4^(3m/2) eps <= eps^(5/8) <= 4^(-5)`. The assumption
  `theta <= 1/2` holds, and `q <= 1.16 eps^(5/8)` by `(4.1)`.

Substituting gives

```text
||C_0 - A|| <= 3 pi/(2m-1) + 3 eps + 10 eps^(5/8),
||Z_0 - B|| <= 3 pi 2^(-m) + eps + 5 eps^(5/8),
```

which implies `(R)`. QED for the theorem.

## The corollary

*Only if.* Assume `(TPC)`. Given `eta > 0`, choose `eps <= 4^(-8)` so small that
the right-hand sides of `(R)` are at most `eta`. Let `delta` be the `(TPC)` modulus
for `eps`. For `A, B in U(n)` with `||A B A^* - B^2|| <= delta`, `(TPC)` gives an
exact `(C,Z)` in `U(n+k)` with `(P)`. The theorem then gives an exact pair in `U(n)`
within `eta` of `(A,B)`. That is same-dimension stability.

*If.* Same-dimension stability is `(TPC)` with `k = 0`. QED.

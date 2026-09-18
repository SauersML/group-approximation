---
rg: 2
id: kazhdan-centralizer-commuting-conjugates-proof
kind: route
title: Replace finite averaging by the Kazhdan spectral projection of D and transport its rank-normalized corner through the compressor
target: kazhdan-centralizer-commuting-conjugates-kill-derived-subgroup
requires:
  - locally-finite-centralizer-derived-subgroup-is-mf-invisible
  - sofic-groups-kill-rigid-compression-defects
  - normal-kazhdan-defect-non-mf
artifacts:
  - research/artifacts/compression-locally-finite-centralizer-criterion-2026-09-08.md
---

## Conventions

- All HS norms are unnormalized.  An unadorned norm is the operator norm.
- `V_n : G -> U(d_n)` is an operator-norm asymptotic representation, with
  `V_n(1) = I`.  That is, `||V_n(gh) - V_n(g)V_n(h)|| -> 0` for all fixed
  `g,h`.  Corona homomorphisms give such sequences by polar lifting, as in
  Section 1 of the artifact.
- `o(1)` means a norm-null sequence, depending on finitely many fixed group
  elements.
- A statement "for large `n`" may be read along any subsequence.

We use only one result from the prerequisite
`locally-finite-centralizer-derived-subgroup-is-mf-invisible`: the
finite-dimensional compression lemma of Section 2 of its artifact.  That
lemma needs exactly `L` Kazhdan and `uLu^-1 <= L`.  Neither the exact
correction of finite groups (its Section 3) nor the finite average (its
Section 4) is used.

## Step 1. The Kazhdan projection of D has an asymptotic gap

Fix a Kazhdan pair `(S, kappa)` of `D`, with `S = S^-1` finite, and put

```text
A_n = sum_(s in S) (V_n(s) - I)^* (V_n(s) - I),     0 <= A_n <= 4|S|.
```

**Claim 1.1.**  For every `eps > 0`, for all large `n`:

```text
spec(A_n) intersect [eps, 3 kappa^2 / 4] is empty.
```

*Proof.*  Suppose not.  Then along a subsequence there are unit
eigenvectors `A_n xi_n = mu_n xi_n` with `mu_n -> mu` in
`[eps, 3kappa^2/4]`.  Take a free ultrafilter and form the Hilbert
ultraproduct `H_omega` of the `C^(d_n)`.  The maps `V_n` induce an exact
unitary representation `V` of `G` on it, because the operator-norm defects
vanish.  The operator `A_omega = sum_s (V(s) - I)^*(V(s) - I)` has
eigenvector `[xi_n]` with eigenvalue `mu`.

By the Kazhdan inequality for `D`:
- `A_omega >= kappa^2` on the orthogonal complement of the `D`-fixed
  vectors;
- `A_omega = 0` on the `D`-fixed vectors.

So `mu` lies in `{0} u [kappa^2, oo)`, a contradiction.  ∎

Put `p_n = 1_[kappa^2/2, oo)(A_n)`, the high-energy projection, and
`r_n = rank(p_n)`.  Fix a continuous `g` on `[0, 4|S|]` with:
- `g = 0` on `[0, kappa^2/4]`;
- `g = 1` on `[kappa^2/2, 4|S|]`.

By Claim 1.1 with `eps = kappa^2/4`, we have `p_n = g(A_n)` exactly for
large `n`.

## Step 2. The projection asymptotically commutes with the normalizer of D

**Claim 2.1.**  Let `q_n = I - p_n`, the low-energy projection.  For every
fixed `t in D`, `||(V_n(t) - I) q_n|| -> 0`.

*Proof.*  Since `p_n = g(A_n)` with a spectral gap, `q_n` is the spectral
projection of `A_n` for the part of the spectrum in `[0, eps]`, for every
`eps > 0` and all large `n`.  So `||A_n q_n|| -> 0`, and hence
`||(V_n(s) - I) q_n|| -> 0` for `s in S`.

A fixed `t in D` is a fixed word in `S`.  Telescoping this word and using
the asymptotic multiplicativity of `V_n` gives `||(V_n(t) - I) q_n|| -> 0`.
Along the telescoping, the partial products applied to `q_n` stay within
`o(1)` of `q_n`.  ∎

Unlike the prerequisite's (2), this needs no ultraproduct.  The gap has
already been established.

The spectral definition of `p_n` gives, for every vector `eta`,

```text
||p_n eta||^2 <= (2 / kappa^2) <A_n eta, eta>
             = (2 / kappa^2) sum_(s in S) ||(V_n(s) - I) eta||^2.      (2.2)
```

**Claim 2.3.**  If `g in G` normalizes `D`, then `||[V_n(g), p_n]|| -> 0`.

*Proof.*  The unit vectors `eta = V_n(g) q_n xi` satisfy
`||(V_n(s) - I) eta|| <= ||(V_n(g^-1 s g) - I) q_n|| + o(1)`.  This is
`o(1)` uniformly in `xi`, by Claim 2.1, because `g^-1 s g` lies in `D`.

Then (2.2) gives `||p_n V_n(g) q_n|| -> 0`.  The same argument for `g^-1`,
together with `V_n(g^-1) = V_n(g)^* + o(1)`, gives
`||p_n V_n(g)^* q_n|| -> 0`.  Taking adjoints,
`||q_n V_n(g) p_n|| -> 0`.  Finally,

```text
[V_n(g), p_n] = q_n V_n(g) p_n - p_n V_n(g) q_n.
```

∎

Both `C` and `L` normalize `D`:
- `C` does by hypothesis;
- `L` centralizes `C`, which contains `D`.

So `[V_n(x), p_n] -> 0` for every fixed `x in C u L`.

**Claim 2.4 (polynomial form).**  For every `delta > 0` there are:
- a finite set `F_delta` of elements of `D`;
- complex numbers `alpha_w`, for `w in F_delta`;

such that `||p_n - sum_w alpha_w V_n(w)|| <= delta + o(1)`.

*Proof.*  Weierstrass gives a polynomial `P` with `|g - P| <= delta` on
`[0, 4|S|]`.  So `||p_n - P(A_n)|| <= delta` for large `n`.  Expand
`P(A_n)` as a fixed noncommutative polynomial in the `V_n(s)`, `s in S`,
and their adjoints.  Replace `V_n(s)^*` by `V_n(s^-1)`, and each product
of lifts by the lift of the product.  Each replacement costs `o(1)`.  ∎

## Step 3. The rank-normalized corner

For `c in C`, put `T_(c,n) = V_n(c) p_n`.  It has rank `r_n`, and
`||T_(c,n)||_HS = sqrt(r_n)`.

**Claim 3.1.**  Suppose `r_n > 0` along a subsequence.  For each fixed
`s in L`,

```text
||V_n(s) T_(c,n) V_n(s)^* - T_(c,n)||_HS / sqrt(r_n) -> 0.
```

*Proof.*  The element `c` commutes with `s`, and `[V_n(s), p_n] -> 0` by
Claim 2.3.  So `||[V_n(s), T_(c,n)]|| -> 0`.

The operator `[V_n(s), T_(c,n)]` has rank at most `2 r_n`, so its HS norm
is at most `sqrt(2 r_n)` times its operator norm.  Finally,
`V_n(s) T V_n(s)^* - T = [V_n(s), T] V_n(s)^*`.  ∎

Let `R_n(g) T = V_n(g) T V_n(g)^*`, acting on `M_(d_n)` with the HS inner
product.  This is an operator-norm asymptotic representation of `G` on a
finite-dimensional Hilbert space.

The unit vectors `xi_n = T_(c,n) / sqrt(r_n)` are asymptotically fixed by
each element of `L`, by Claim 3.1.  The compression lemma (Section 2 of
the artifact) needs only `L` Kazhdan and `uLu^-1 <= L`, with no bound on
dimension.  It shows that `R_n(u) xi_n` is asymptotically fixed by each
element of `L`.  So, with

```text
a_(c,n) = V_n(u) T_(c,n) V_n(u)^*,
b_(c,n) = V_n(ell) a_(c,n) V_n(ell)^*,
e_n     = V_n(u) p_n V_n(u)^*,
```

we have

```text
||a_(c,n) - b_(c,n)||_HS = o(sqrt(r_n)).                               (3.2)
```

## Step 4. Operator-norm commutation of the two conjugate corners

**Claim 4.1.**  For fixed `c, c' in C`, `||[a_(c,n), b_(c',n)]|| -> 0`.

*Proof.*  Fix `delta > 0` and apply Claim 2.4.  Up to `delta + o(1)` in
norm:
- `a_(c,n)` equals `A'_n = sum_w alpha_w V_n(u c w u^-1)`;
- `b_(c',n)` equals `B'_n = sum_w alpha_w V_n(ell u c' w u^-1 ell^-1)`.

Here `c w` and `c' w` lie in `C`, because `w in D <= C`.  By (KC0), each
`u c w u^-1` commutes in `G` with each `ell u c' w' u^-1 ell^-1`, so
`||[A'_n, B'_n]|| = o(1)` for each fixed `delta`.  Also
`||A'_n|| <= 1 + delta + o(1)`.  Hence

```text
limsup ||[a_(c,n), b_(c',n)]|| <= 2(delta) + 2(1 + delta)(delta).
```

Now let `delta -> 0`.  ∎

This is the only place where (KC0) is used.  It replaces the finite group
average of the prerequisite's Section 4 by the polynomial form of the
Kazhdan projection.

## Step 5. Corner calculus and the trace contradiction

**Claim 5.1 (corner representation).**  For fixed `c, c' in C`, in
operator norm:
- `a_(c,n) a_(c',n) = a_(c c',n) + o(1)`;
- `a_(c^-1,n) = a_(c,n)^* + o(1)`;
- `a_(1,n) = e_n`;
- `a_(c,n)` lies in the corner `e_n M_(d_n) e_n` up to `o(1)`.

*Proof.*  Since `[V_n(c'), p_n] -> 0` (Claim 2.3), we get
`V_n(c) p_n V_n(c') p_n = V_n(c c') p_n + o(1)`.  Conjugating by
`V_n(u)` gives the first item.  The others are similar.  ∎

The corner `e_n M e_n` has dimension `r_n`.  So every `o(1)` in operator
norm inside it is `o(sqrt(r_n))` in HS norm.

**Claim 5.2.**  For fixed `c, c' in C`,

```text
||[a_(c,n), a_(c',n)]||_HS = o(sqrt(r_n)).
```

*Proof.*  Write

```text
[a_c, a_c'] = [a_c, b_c'] + [a_c, a_c' - b_c'].
```

- The first term has operator norm `o(1)`, by Claim 4.1.  It has rank at
  most `2 r_n`, since `a_c` has rank at most `r_n`.  So its HS norm is
  `o(sqrt(r_n))`.
- The second term has HS norm at most `2 ||a_c|| ||a_c' - b_c'||_HS`.
  This is `o(sqrt(r_n))`, by (3.2).

∎

**Claim 5.3.**  For fixed `h in [C,C]`, `||a_(h,n) - e_n||_HS = o(sqrt(r_n))`.

*Proof.*  Write `h` as a fixed product of commutators `[c_i, c'_i]` with
`c_i, c'_i in C`.  By Claim 5.1, `a_([c,c'],n)` equals
`a_c a_c' a_c^* a_c'^*` up to `o(sqrt(r_n))` in HS.  By Claim 5.2, this
is within `o(sqrt(r_n))` of `a_c' a_c a_c^* a_c'^*`, which is `e_n` up to
the same error.  Telescoping over the fixed product, with every factor of
norm at most `1 + o(1)`, finishes the proof.  ∎

**The contradiction.**  Suppose `r_n > 0` along a subsequence.  For `s in S`
(which lies in `D <= [C,C]`), the definitions give exactly

```text
a_(s,n) - e_n = V_n(u) (V_n(s) - I) p_n V_n(u)^*.
```

Claim 5.3 then gives `||(V_n(s) - I) p_n||_HS = o(sqrt(r_n))`.  Summing
over `S`,

```text
Tr(p_n A_n p_n) = sum_(s in S) ||(V_n(s) - I) p_n||_HS^2 = o(r_n).
```

But `A_n >= kappa^2/2` on `ran(p_n)`, so `Tr(p_n A_n p_n) >= (kappa^2/2) r_n`.
This is a contradiction.

Hence `p_n = 0` for all large `n`, so `q_n = I`, and Claim 2.1 gives
`||V_n(t) - I|| -> 0` for every `t in D`.  This is (KC1).  The kernel of
a corona homomorphism is normal, so it contains `<<D>>_G`, which gives the
MF-radical form.

## Step 6. The corollaries

**(KC2).**  A Kazhdan group has finite abelianization.  So `[C,C]` has
finite index in `C`.  It is therefore Kazhdan, normal in `C`, and
nontrivial when `C` is nonabelian.

**(KC3).**  Apply `sofic-groups-kill-rigid-compression-defects` with:
- `Gamma = L`, infranormal in the Kazhdan group `G_0`;
- ambient sofic group `H`;
- `g = u in G_0`;
- `z = c in C <= C_H(L)`.

It gives `[u c u^-1, l] = 1` for all `l in L`.  So
`ell u C u^-1 ell^-1 = u C u^-1`, and (KC0) says `u C u^-1` commutes with
itself.  Hence `C` is abelian and `D <= [C,C] = 1`.

**(KC4).**  Put `x = u c u^-1` and `y = u c' u^-1`, with `c, c' in C`.
The defect generator is `z = [x, ell] = x (ell x ell^-1)^-1`.  The
element `ell x ell^-1` commutes with `y`, by (KC0).  Hence

```text
[z, y] = x (ell x^-1 ell^-1) y (ell x ell^-1) x^-1 y^-1
       = x y x^-1 y^-1 = [x, y].
```

The element `u` lies in `Comp_G(L)` and `c` in `C_G(L)`, so `z` is a
generator of `D_G(L)`.  Therefore `[x,y]` lies in `D_G(L)`, and so does
`[uCu^-1, uCu^-1] = u[C,C]u^-1`.  Conjugating back, `[C,C] <= D_G(L)`.

More precisely, `[z, y] = z (y z^-1 y^-1)`, so `[x, y]` lies in the
normal closure of the defect elements `[u c u^-1, l]`, `l in L`, of the
**single** root `c`.

Suppose some normal Kazhdan subgroup `K` of `G` lies inside the normal
closure of the commutators `[u c u^-1, u c' u^-1]` for one fixed `c`.
For example, `<<[u c u^-1, u C u^-1]>>_G = K`.  Then `K` lies in the
defect normal subgroup of the single core `(L, u, c)`.  So
`normal-kazhdan-defect-non-mf` gives `K <= Rad_MF(G)` without Steps 1--5.

With several roots, this needs the multi-root form of that theorem, which
is not recorded here.  The claim asserts subsumption only in the
single-root case.  ∎

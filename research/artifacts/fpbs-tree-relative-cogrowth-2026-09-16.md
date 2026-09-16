# Relative thresholds of normal subgroups on free-group trees, and failure of the divergence crux

Date: 2026-09-16. Written by the swarm agent `swarm-fpbs-residual-price-one-non-ah`
while working on `fpbs-residual-price-one-non-ah-class-nonuniqueness`.

Computations: `experiments/fpbs-tree-relative-cogrowth-2026-09-16/verify_cogrowth_identity.py`,
with its output in `output.txt` in the same folder.

## 0. Purpose

Section 7(d) of `research/artifacts/fpbs/docs/benjamini-schramm-frontier-map.md`
isolates the statement

```text
D(I):   chi^I_p -> infinity   as   p ↑ p_c(I;G),
```

that relative susceptibility diverges at the relative threshold. Together with
critical relative finiteness `chi^I_(p_c(G)) < infinity`, it would force
`p_c(G) < p_c(I;G)`, and so `p_c(G) < p_u(G)`.

This artifact computes `p_c(N;T)` and `chi^N_p` exactly when `T` is the
standard Cayley tree of a free group and `N` is a normal subgroup.
- The relative threshold is the inverse cogrowth of `N`.
- The relative susceptibility at that threshold is an explicit multiple of the
  Green function of the quotient walk at the inverse spectral radius.
- So it is finite exactly when the quotient walk is rho-transient.

Consequences for the crux:
1. For `N = [F_3,F_3]` on the 6-regular tree,
   `p_c(N;T) = p_c(T) = 1/5` and `chi^N_(1/5) = (4/5) G_(Z^3)(1) ≈ 1.2131`.
   Critical relative finiteness holds, `D(N)` fails, and there is no relative
   gap.
2. For the normal closure `N` of the third basis letter in `F_3`, the relative
   gap holds, `p_c(N;T) ≈ 0.232461 > 1/5`, and `D(N)` still fails.
3. For `N = [F_2,F_2]` on the 4-regular tree, `D(N)` holds and there is no gap.

So on trees `D(N)` is decoupled from the gap. It holds exactly when the
quotient walk is rho-recurrent. Critical relative finiteness at `p_c(G)` does
not imply a relative gap.

## 1. Setting and statements

**Free group and tree.**
- `d >= 2`, and `F_d` is free on `a_1, ..., a_d`.
- `S = {a_1^(±1), ..., a_d^(±1)}`, `q = 2d - 1`, and `T = Cay(F_d, S)` is the
  `(q+1)`-regular tree. The root is `o = e`.
- `|g|` is the length of the reduced word of `g`, which is also the graph
  distance from `o` to `g`.

**Cogrowth.** For a subgroup `H <= F_d`, put

```text
f_n(H) = #{h in H : |h| = n},     F_H(s) = sum_(n>=0) f_n(H) s^n,
```

and let `R_H` be the radius of convergence of `F_H`. The cogrowth of `H` is
`alpha_H = 1/R_H = limsup_n f_n(H)^(1/n)`.

**Quotient walk.** For `N ◁ F_d`, let `Q = F_d/N` with projection `pi`.
- `mu = (1/2d) sum_(s in S) delta_(pi(s))` is the image of the uniform measure
  on `S`, counted with multiplicity. So `pi(s)` may be trivial, or may repeat.
- `p_n = mu^(*n)(e_Q)`, and `rho_Q = limsup_n p_n^(1/n)` is the spectral
  radius.
- `G_Q(w) = sum_n p_n w^n` is the Green function, with radius `1/rho_Q`.
- `mu` is *rho-transient* when `G_Q(1/rho_Q) < infinity`, and rho-recurrent
  otherwise.
- `rho_T = 2 sqrt(q)/(q+1)` is the spectral radius of the tree.

**Two functions.** For real `s` put

```text
z(s) = s/(1 + q s^2),        phi(s) = (1 - s^2)/(1 + q s^2).
```

On `[0, 1/sqrt(q)]`, `z` increases strictly from `0` to `1/(2 sqrt(q))`, since
`z'(s) = (1 - q s^2)/(1 + q s^2)^2`. Also `z(1/q) = 1/(q+1)`.

**Percolation.** `P_p` is Bernoulli(p) bond percolation on `T`, and `K_o` is
the cluster of `o`.
- `chi^H_p = E_p|K_o ∩ H|`.
- A cluster `K` is H-infinite when `|K ∩ H| = infinity`.
- `p_c(H;T) = inf{p : a.s. there is an H-infinite cluster}`. This is
  Hutchcroft–Pan Definition 1.2, as recorded in
  `research/artifacts/fpbs/docs/relative-susceptibility-reduction.md`.
- `p_c(T) = 1/q`. The cluster of `o` is a Galton–Watson tree with root
  offspring `Bin(q+1,p)` and later offspring `Bin(q,p)`. It is infinite with
  positive probability iff `qp > 1`.

**Theorem A.** Let `N ◁ F_d` with `rho_Q > rho_T`, and let `s_N` be the smaller
root of `q s^2 - (q+1) rho_Q s + 1 = 0`:

```text
s_N = ( (q+1) rho_Q - sqrt((q+1)^2 rho_Q^2 - 4q) ) / (2q).
```

Equivalently, `s_N` is the unique `s in (0, 1/sqrt(q))` with
`(q+1) z(s) = 1/rho_Q`. Since `rho_Q <= 1`, monotonicity of `z` gives
`1/q <= s_N < 1/sqrt(q)`. Then:

- **(A1)** `chi^N_p = F_N(p)` for every `p in [0,1]`, and `R_N = s_N`. For
  `0 <= p <= s_N`, in `[0, infinity]`,

  ```text
  chi^N_p = phi(p) G_Q( (q+1) z(p) ),
  ```

  and `chi^N_p = infinity` for `p > s_N`.
- **(A2)** `p_c(N;T) = s_N = 1/alpha_N`.
- **(A3)** `chi^N_(s_N) = phi(s_N) G_Q(1/rho_Q)`. This equals
  `lim_(p ↑ s_N) chi^N_p`, and it is finite iff `mu` is rho-transient. Hence
  `D(N)` holds iff `mu` is rho-recurrent.
- **(A4)** `p_c(T) < p_c(N;T)` iff `rho_Q < 1`.

**Remarks.**
- By Kesten's criterion (Kesten 1959), `rho_Q < 1` iff `Q` is nonamenable. This
  is used only to interpret (A4).
- The hypothesis `rho_Q > rho_T` excludes `N = 1`. So `N` is infinite, because
  nontrivial subgroups of free groups are infinite.
- Kesten 1959 also proves `rho_Q > rho_T` for every `N ≠ 1`. This is not
  re-verified here, and the examples of Section 6 check the hypothesis
  directly.
- (A1) is Grigorchuk's cogrowth formula written as a generating-function
  identity. See Grigorchuk 1980, Woess 1983, Northshield 2004 and Ortner–Woess
  2007 in Section 9. A proof is included because the value at the endpoint
  `s_N` is what matters here.
- Lemma 2.1, Lemma 2.3 and Lemma 4.1 hold for every subgroup `H`, with the
  Schreier graph in place of `Q`. Normality is used only in Lemma 4.2.

**Corollary B (no gap, no divergence).** Let `d = 3` and `N = [F_3,F_3]`, so
`Q = Z^3` and `mu` is simple random walk. Then
- `p_c(N;T) = p_c(T) = 1/5`;
- `chi^N_(1/5) = (4/5) G_(Z^3)(1) = 1.21310...`, while `chi^N_p = infinity` for
  `p > 1/5`.

So `D(N)` fails, `chi^N_(p_c(T)) < infinity`, and `p_c(T) = p_c(N;T)`.

**Corollary C (gap, no divergence).** Let `d = 3` and let `N` be the normal
closure of `a_3`, so `Q = F_2` and `mu = (1/3) delta_e + (2/3) nu`, with `nu`
simple random walk on `F_2`. Then
- `rho_Q = (1 + sqrt 3)/3 ≈ 0.910684`, and `mu` is rho-transient with
  `G_Q(1/rho_Q) = 3 + sqrt 3`;
- `p_c(N;T) = s_N = (2 + 2 sqrt 3 - sqrt(8 sqrt 3 - 4))/10 ≈ 0.232461`, which
  is larger than `p_c(T) = 1/5`;
- `chi^N_(s_N) = phi(s_N) (3 + sqrt 3) ≈ 3.5241 < infinity`.

So the relative gap holds and `D(N)` fails.

**Corollary D (no gap, divergence).** Let `d = 2` and `N = [F_2,F_2]`, so
`Q = Z^2`. Then `p_c(N;T) = p_c(T) = 1/3` and `chi^N_(1/3) = infinity`. So
`D(N)` holds and there is no gap.

## 2. The non-backtracking identity

Fix `N ◁ F_d` with quotient `Q` and projection `pi`. The *label graph* is the
multigraph on `Q` with one edge `x -> x pi(s)` for each `x in Q` and `s in S`.
Its adjacency matrix is

```text
A(x,y) = #{ s in S : x pi(s) = y }.
```

`A` is symmetric because `S = S^(-1)`, and it is row-finite with every row sum
equal to `q+1`. Row-finite matrices on `Q` form an associative algebra, since
every entry of a product is a finite sum. Polynomials in `A` form a commutative
subalgebra.

For `n >= 0` let `A_n(x,y)` be the number of reduced words `w` of length `n`
with `x pi(w) = y`. Each element of `F_d` has exactly one reduced word, and
`w in N` iff `pi(w) = e`. So

```text
f_n(N) = A_n(e,e).                                              (2.0)
```

**Lemma 2.1 (recursion).** `A_0 = I` and `A_1 = A`. Moreover
`A_1 A = A_2 + (q+1) I`, and `A_n A = A_(n+1) + q A_(n-1)` for `n >= 2`. So
every `A_n` is a polynomial in `A`.

*Proof.* `(A_n A)(x,y)` counts pairs `(w,s)` with `w` reduced of length `n`,
`s in S`, and `x pi(ws) = y`.
- For `n = 0`, `ws = s`, and the count is `A(x,y)`.
- Let `n >= 1`. If `s` is not `last(w)^(-1)`, then `ws` is reduced of length
  `n+1`. Every reduced word of length `n+1` arises this way exactly once, so
  these pairs contribute `A_(n+1)(x,y)`.
- If `s = last(w)^(-1)`, then `ws` equals the reduced word `w'` obtained by
  deleting the last letter of `w`, and `pi(ws) = pi(w')`. A reduced word `w'`
  of length `n-1` arises from the pairs `(w't, t^(-1))`, where `w't` is reduced.
  There are `q+1` choices of `t` when `n = 1`, and `q` choices when `n >= 2`.
  So these pairs contribute `(q+1) A_0(x,y)` when `n = 1`, and `q A_(n-1)(x,y)`
  when `n >= 2`. QED.

**Lemma 2.2 (formal identity).** In formal power series in `s` with
coefficients in the algebra of polynomials in `A`, put `B(s) = sum_n A_n s^n`.
Then

```text
B(s) ( (1 + q s^2) I - s A ) = (1 - s^2) I,
B(s) = phi(s) sum_(m>=0) z(s)^m A^m.                            (2.1)
```

Taking the `(e,e)` entry, as formal power series in `s`,

```text
F_N(s) = phi(s) Gamma_N(z(s)),     Gamma_N(z) = sum_m (q+1)^m p_m z^m.   (2.2)
```

*Proof.* The coefficient of `s^n` in the left side of the first equation is
`A_n + q A_(n-2) - A_(n-1) A`, with `A_(-1) = A_(-2) = 0`.
- For `n = 0` it is `I`.
- For `n = 1` it is `A - A = 0`.
- For `n = 2` it is `A_2 + qI - A_2 - (q+1)I = -I`.
- For `n >= 3` it is `0`, by Lemma 2.1.

Now `z(s) = s (1+qs^2)^(-1)` is a formal power series with zero constant term.
So `C(s) = sum_m z(s)^m A^m` is well defined: the coefficient of `s^n` involves
only `m <= n`. Also `(I - zA) C = I`, and everything commutes. Since
`(1+qs^2) I - sA = (1+qs^2)(I - zA)`, multiplying the first equation on the
right by `(1+qs^2)^(-1) C` gives the second.

For (2.2), `A = (q+1) P`, where `P` is the transition matrix of the walk with
step law `mu`. So `A^m(e,e) = (q+1)^m p_m`, and (2.0) finishes. QED.

(2.2) is Grigorchuk's cogrowth formula. The script checks the coefficients of
(2.2) against brute-force enumeration of `f_n` for two examples (Section 8).

**Lemma 2.3 (analytic identity and radius).** Assume `rho_Q > rho_T`, and let
`z_Q = 1/((q+1) rho_Q)` be the radius of convergence of `Gamma_N`. This is
Cauchy–Hadamard, because `limsup_m p_m^(1/m) = rho_Q`. Let `s_N` be as in
Theorem A. Then:

1. `z(s_N) = z_Q`, `z'(s_N) > 0`, and `phi(s_N) > 0`.
2. (2.2) holds as an identity of convergent series for `|s| < r_0`, for some
   `r_0 > 0`.
3. `R_N >= s_N`.
4. `F_N(p) = phi(p) Gamma_N(z(p))` for `0 <= p < s_N`.
5. `F_N(s_N) = phi(s_N) Gamma_N(z_Q)` in `[0, infinity]`.
6. `R_N <= s_N`.

So `R_N = s_N`.

*Proof.*

*Step 1.* By hypothesis `z_Q < 1/(2 sqrt q) = z(1/sqrt q)`. Since `z` is
continuous and strictly increasing on `[0, 1/sqrt q]`, there is a unique
`s_N in (0, 1/sqrt q)` with `z(s_N) = z_Q`. Expanding `(q+1) z(s) = 1/rho_Q`
gives the quadratic of Theorem A with its smaller root. `z'(s_N) > 0` because
`q s_N^2 < 1`. `phi(s_N) > 0` because `s_N < 1`.

*Step 2.* Write `g_m = (q+1)^m p_m >= 0`. Expanding
`z(s)^m = sum_i (-1)^i C(m+i-1,i) q^i s^(m+2i)` and
`phi(s) = (1 - s^2) sum_j (-q)^j s^(2j)`, the triple series has absolute
values dominated, for `|s| = r < 1/sqrt q`, by

```text
((1 + r^2)/(1 - q r^2)) sum_m g_m ( r/(1 - q r^2) )^m.
```

This is finite once `r/(1 - q r^2) < z_Q`, which holds for all small `r`. For
absolutely convergent series any rearrangement has the same sum. So collecting
powers of `s` gives the coefficients of the formal product, and (2.2) holds
pointwise for `|s| < r_0`.

*Step 3.* Suppose `R_N < s_N`. The set

```text
U = { s in C : 1 + q s^2 ≠ 0,  |z(s)| < z_Q }
```

is open. `H(s) = phi(s) Gamma_N(z(s))` is holomorphic on `U`, and `U`
contains `[0, s_N)`, since `z([0, s_N)) = [0, z_Q)`. So `U` contains
`V = {s : dist(s, [0, R_N]) < eps}` for some `eps > 0`. `V` is convex, so
`V ∩ D(0, R_N)` is convex, hence connected. It contains a small disc around
`0`, on which `F_N = H` by Step 2. By the identity theorem `F_N = H` on
`V ∩ D(0, R_N)`. Then `F_N` on `D(0,R_N)` and `H` on `V` glue to a holomorphic
function on a neighbourhood of `R_N`.

`F_N` has nonnegative coefficients, so Pringsheim's theorem says `R_N` is a
singular point of `F_N`. This is a contradiction.

*Step 4.* `F_N` is holomorphic on `D(0, s_N)` by Step 3, and `H` is holomorphic
on `U`. Let `W` be the connected component of `U ∩ D(0, s_N)` containing `0`.
It contains the connected set `[0, s_N)` and a small disc around `0`, where
`F_N = H`. By the identity theorem, `F_N = H` on `W`, and in particular on
`[0, s_N)`.

*Step 5.* Let `p ↑ s_N`.
- `F_N(p) ↑ F_N(s_N)` by monotone convergence.
- `z(p) ↑ z_Q`, so `Gamma_N(z(p)) ↑ Gamma_N(z_Q)`, again by monotone
  convergence.
- `phi(p) -> phi(s_N) in (0, infinity)`.

Step 4 then gives the claim, in `[0, infinity]`.

*Step 6.* Suppose `R_N > s_N`, so `F_N` is holomorphic near `s_N`.
- *Local inverse.* By Step 1 and the holomorphic inverse function theorem,
  there are a disc `V_0 = D(z_Q, delta)` and an open `W_0 ⊆ D(0, R_N)`
  containing `s_N` such that `z : W_0 -> V_0` is biholomorphic, with inverse
  `sigma`. We may take `delta` small so that `phi ≠ 0` and `1 + q s^2 ≠ 0` on
  `W_0`.
- *A candidate extension.* Put `Gamma~ = (F_N ∘ sigma)/(phi ∘ sigma)`,
  holomorphic on `V_0`.
- *Agreement on a segment.* The real function `z` has positive derivative at
  `s_N`. So for real `z in (z_Q - delta', z_Q)`, with `delta'` small, `sigma(z)`
  is the real preimage, which lies in `(0, s_N)`. By Step 4,
  `Gamma~(z) = F_N(sigma(z))/phi(sigma(z)) = Gamma_N(z)` there.
- *Agreement on a region.* `V_0 ∩ D(0, z_Q)` is convex, so the identity theorem
  gives `Gamma~ = Gamma_N` on it. So `Gamma_N` extends holomorphically to a
  neighbourhood of `z_Q`.

`Gamma_N` has nonnegative coefficients and radius `z_Q`, so this contradicts
Pringsheim's theorem. QED.

The hypothesis `rho_Q > rho_T` is used only through `s_N < 1/sqrt q`, that is,
`z'(s_N) > 0`.

## 3. Relative susceptibility on a tree

**Lemma 3.1.** For every subset `H ⊆ F_d` and every `p in [0,1]`,

```text
chi^H_p = sum_(h in H) P_p(o <-> h) = sum_(h in H) p^|h| = F_H(p)   in [0, infinity].
```

*Proof.* The first equality is linearity of expectation. `T` is a tree, so the
only simple path from `o` to `h` is the geodesic, which has `|h|` edges.
Therefore `o <-> h` iff all of them are open, which has probability `p^|h|`.
QED.

## 4. The relative threshold

The event

```text
A_H = { there is a cluster K with |K ∩ H| = infinity }
```

is increasing, so `p -> P_p(A_H)` is nondecreasing, by the standard monotone
coupling.

**Lemma 4.1 (below the radius).** Let `H <= F_d` be a subgroup and
`p in [0,1]`. If `chi^H_p < infinity`, then `P_p(A_H) = 0`. Hence
`P_p(A_H) = 0` for every `p < R_H`.

*Proof.*
- Since `E_p|K_o ∩ H| < infinity`, a.s. `|K_o ∩ H| < infinity`.
- For `h in H`, the map `g -> hg` is a graph automorphism of `T` fixing `H`
  setwise and sending `o` to `h`. It preserves `P_p`, so a.s.
  `|K_h ∩ H| < infinity`.
- `H` is countable, so a.s. this holds for all `h in H` simultaneously.
- An `H`-infinite cluster contains some `h in H`, and then it is `K_h`, with
  `|K_h ∩ H| = infinity`.

So `P_p(A_H) = 0`. For `p < R_H`, `chi^H_p = F_H(p) < infinity` by Lemma 3.1.
QED.

**Lemma 4.2 (cyclically reduced part).** Let `N ◁ F_d`. For `m >= 1` let

```text
c_m = #{ w in N : w cyclically reduced, |w| = m },   C_N(s) = sum_(m>=1) c_m s^m.
```

Here "cyclically reduced" means `w` is a nonempty reduced word with
`first(w) ≠ last(w)^(-1)`. Then

```text
F_N(s) - 1 = C_N(s) (1 - s^2)/(1 - q s^2)     (nonnegative series)      (4.1)
```

and, if `R_N < 1/sqrt q`, the radius of convergence of `C_N` equals `R_N`.

*Proof.*
- *Unique decomposition.* Every reduced word `h ≠ e` has a unique factorization
  `h = u w u^(-1)` without cancellation, where `w` is cyclically reduced and
  `|h| = 2|u| + |w|`. Repeatedly strip the first and last letters while
  `first = last^(-1)`. This never reaches the empty word: a reduced word of
  length `2` has `first ≠ last^(-1)`. The factorization is forced at each step.
- *Normality.* `h in N` iff `w in N`.
- *Counting the conjugators.* Fix a cyclically reduced `w` of length `m` and
  `k >= 1`. The words `u` of length `k` for which `u w u^(-1)` is reduced
  without cancellation are the reduced `u` with `last(u) ≠ first(w)^(-1)` and
  `last(u) ≠ last(w)`. These two excluded letters differ because `w` is
  cyclically reduced. So there are `q - 1` choices for `last(u)`, and `q^(k-1)`
  reduced words with a given last letter.
- *The count.* Hence `f_n = c_n + sum_(k>=1, 2k<n) (q-1) q^(k-1) c_(n-2k)` for
  `n >= 1`, and `f_0 = 1`.
- *Generating functions.* In generating functions,
  `F_N - 1 = C_N M` with `M(s) = 1 + sum_(k>=1) (q-1) q^(k-1) s^(2k)`, which
  equals `(1 - s^2)/(1 - q s^2)`.
- *The radius.* All series here have nonnegative coefficients, so (4.1) holds
  in `[0, infinity]` for `0 <= p < 1/sqrt q`. Since `c_m <= f_m`, the radius of
  `C_N` is at least `R_N`. If `R_N < p < 1/sqrt q`, then `F_N(p) = infinity`
  and `M(p) < infinity`, so `C_N(p) = infinity`. Hence the radius is at most
  `R_N`. QED.

**Proposition 4.3 (above the radius).** Let `N ◁ F_d` with
`R_N < 1/sqrt q`, and let `p in (R_N, 1]`. Then `P_p(A_N) = 1`.

*Proof.* By monotonicity we may assume `p < 1/sqrt q`.

*Step 1: a concatenable block set.* By Lemma 4.2,
`limsup_m (c_m p^m)^(1/m) = p/R_N > 1`. So there is `m >= 1` with
`c_m p^m > 2d`. For `x in S` let `E_x` be the set of cyclically reduced
`w in N` with `|w| = m` and `first(w) = x`. Since `sum_x |E_x| = c_m`, some
`x` has `|E_x| p^m > 1`. Fix it and write `E = E_x`.

For `w, w' in E`, `last(w) ≠ x^(-1) = first(w')^(-1)`. So every concatenation
`w_1 w_2 ... w_k` with `w_i in E` is a reduced word of length `km`, and it lies
in `N`. Distinct tuples give distinct reduced words, hence distinct group
elements.

*Step 2: a Galton–Watson process.* Let `L_k` be the set of such concatenations
of `k` blocks, with `L_0 = {o}`. Call `g in L_k` *reached* if every edge of the
geodesic from `o` to `g` is open, and let `Z_k` be the number of reached
elements of `L_k`. For `g in L_k` put

```text
xi_g = #{ w in E : every edge of the geodesic from g to gw is open }.
```

A reached `g w` has a reached `g`. So `Z_(k+1) = sum_(g in L_k reached) xi_g`.

- *Disjointness.* The geodesic from `g` to `gw` has edges
  `{g u_j, g u_(j+1)}`, where `u_j` is the prefix of `w` of length `j`, and
  `g u_j` is a reduced word of length `km + j`. If `g, g' in L_k` are distinct,
  their segments share no edge: a shared edge would give
  `g u_j = g' u'_j` as reduced words, so their first `km` letters would agree,
  and `g = g'`. These segments also share no edge with the geodesics to
  elements of `L_0, ..., L_k`, whose edges join words of length at most `km`.
- *Independence and law.* Let `F_k` be the sigma-field of the edges between
  words of length at most `km`. `F_k` determines which elements of `L_k` are
  reached. Given `F_k`, the variables `(xi_g)_(g in L_k)` are independent. Each
  has the law of `xi = #{w in E : the geodesic from o to w is open}`, because
  left multiplication by `g` preserves `P_p`.

So `(Z_k)` is a Galton–Watson process with offspring law `xi`, and
`E xi = |E| p^m > 1`. It survives with positive probability `theta > 0`. On
survival, `K_o` contains infinitely many elements of `N`, so
`P_p(A_N) >= theta > 0`.

*Step 3: zero-one law.* Left multiplication by `n in N` preserves `P_p` and
maps `N` to `N` and clusters to clusters. So `A_N` is invariant.
- Given `eps > 0`, choose an event `B` depending on a finite edge set `E_B`
  with `P_p(A_N Δ B) < eps`.
- Since `N` is infinite, there is `n in N` with `|n|` so large that `n E_B` and
  `E_B` are disjoint. Then `P_p(B ∩ nB) = P_p(B)^2`.
- By invariance, `P_p(A_N) = P_p(A_N ∩ n A_N)`, which is within `2 eps` of
  `P_p(B ∩ nB)`.
- `P_p(B)^2` is within `2 eps` of `P_p(A_N)^2`.

So `|P_p(A_N) - P_p(A_N)^2| <= 4 eps` for every `eps > 0`, and
`P_p(A_N) in {0,1}`. With Step 2, `P_p(A_N) = 1`. QED.

**Corollary 4.4.** If `N ◁ F_d` and `R_N < 1/sqrt q`, then `p_c(N;T) = R_N`.
Moreover `P_p(A_N) = 0` for `p < R_N` and `P_p(A_N) = 1` for `p > R_N`. So the
value does not depend on whether the relative threshold is defined by
`P_p(A_N) > 0` or by `P_p(A_N) = 1`. This follows from Lemma 4.1 and
Proposition 4.3.

## 4a. Remark on the threshold proof

Proposition 4.3 does not use Hutchcroft–Pan's relative sharpness
(`fpbs-hp-relative-sharpness`). On a tree, the exponential rate `1/R_N` of
cyclically reduced words of `N` directly supplies a supercritical branching
process inside the cluster of `o`.

## 5. Proof of Theorem A

Assume `N ◁ F_d` and `rho_Q > rho_T`.

**(A1).** Lemma 3.1 gives `chi^N_p = F_N(p)` for every `p in [0,1]`, and
Lemma 2.3 gives `R_N = s_N`.
- For `0 <= p < s_N`, the formula is Lemma 2.3, Step 4.
- At `p = s_N`, it is Step 5.
- For `p > s_N = R_N`, the nonnegative series `F_N(p)` diverges.

`G_Q((q+1) z(p)) = Gamma_N(z(p))` by definition of `Gamma_N`.

**(A2).** `s_N = R_N < 1/sqrt q` by Lemma 2.3 and Step 1 of its proof, so
Corollary 4.4 gives `p_c(N;T) = R_N = s_N`. By Cauchy–Hadamard,
`R_N = 1/alpha_N`.

**(A3).** At `p = s_N`, `(q+1) z(s_N) = (q+1) z_Q = 1/rho_Q`, so (A1) gives
`chi^N_(s_N) = phi(s_N) G_Q(1/rho_Q)`. Monotone convergence in `p` gives
`lim_(p ↑ s_N) chi^N_p = chi^N_(s_N)`. Since `phi(s_N) in (0, infinity)`, this
is finite iff `G_Q(1/rho_Q) < infinity`. `D(N)` is the statement
`chi^N_p -> infinity` as `p ↑ p_c(N;T) = s_N`, so it holds iff `mu` is
rho-recurrent.

**(A4).** `p_c(T) = 1/q`, and `1/q, s_N in [0, 1/sqrt q]`, where `z` is
strictly increasing. So `s_N > 1/q` iff `z_Q > z(1/q) = 1/(q+1)`, that is, iff
`rho_Q < 1`. Also `rho_Q <= 1` always, since `p_n <= 1`. QED.

**Remark 5.1.** (A2) and (A4) together say that `p_c(T) < p_c(N;T)` iff the
cogrowth `alpha_N` is less than `q`, iff `rho_Q < 1`. This is Grigorchuk's
cogrowth criterion, read as a percolation statement. (A2) is of the same kind
as Lyons' theorem `p_c = 1/br` for trees (R. Lyons, Ann. Probab. 18 (1990);
unverified, not fetched), applied to the subtree spanned by `N`. It does not
follow verbatim, because a cluster that is infinite in that subtree need not
meet `N` infinitely often, so a self-contained proof is given. The endpoint
value (A3) was not found stated in the sources checked.

*Referee note (2026-09-16).* The novelty wording was softened here, and the
approximation in Corollary C was corrected from `3.5242` to `3.5241`.

## 6. Examples

### 6.1. `N = [F_3,F_3]`, `Q = Z^3` (Corollary B)

Here `d = 3` and `q = 5`. `N` is the kernel of abelianization, `pi(a_i^(±1))`
is `±e_i`, and `mu` is simple random walk on `Z^3`.

- **`rho_Q = 1`.** `mu^(*n)` is supported on the box `[-n,n]^3`, which has
  `(2n+1)^3` points. By Cauchy–Schwarz and symmetry,
  `p_(2n) = sum_x mu^(*n)(x)^2 >= (2n+1)^(-3)`. So `rho_Q = 1`, which is larger
  than `rho_T = 2 sqrt 5/6 ≈ 0.745`.
- **`s_N`.** The quadratic is `5 s^2 - 6 s + 1 = (5s - 1)(s - 1)`, so
  `s_N = 1/5 = p_c(T)`. Also `phi(1/5) = (24/25)/(30/25) = 4/5`.
- **Transience.** `G_(Z^3)(1) < infinity` by Pólya's theorem. By Fourier
  inversion and monotone convergence as `w ↑ 1`,
  `G(1) = (2 pi)^(-3) ∫_[-pi,pi]^3 dtheta / (1 - (cos theta_1 + cos theta_2 + cos theta_3)/3)`.
  The denominator vanishes only at `theta = 0`, where it is about `|theta|^2/6`,
  and `|theta|^(-2)` is integrable in dimension 3.
- **Value.** Watson's integral, in the closed form of Glasser–Zucker 1977, is

  ```text
  G_(Z^3)(1) = (sqrt 6/(32 pi^3)) Gamma(1/24) Gamma(5/24) Gamma(7/24) Gamma(11/24)
             = 1.516386059...
  ```

  So `chi^N_(1/5) = (4/5) G_(Z^3)(1) = 1.213108847...`.

The script evaluates this closed form numerically. It confirms
`1 - 1/G = 0.3405373...`, the known return probability of simple random walk on
`Z^3`. As a sanity check of (2.2) it also computes `f_n(N)` for `n <= 22` by
brute force. The coefficients agree exactly, and the partial sum
`sum_(n<=22) f_n 5^(-n) = 1.1251...` increases towards `1.2131`.

### 6.2. `N = <<a_3>>`, `Q = F_2` (Corollary C)

Here `d = 3` and `q = 5`. `Q = <a_1, a_2>` is free, and `pi(a_3^(±1)) = e`.
So `mu = (1/3) delta_e + (2/3) nu`, where `nu` is simple random walk on the
4-regular tree `T_4 = Cay(F_2)`.

- **Green function of `nu`.** For the `(q'+1)`-regular tree with `q' = 3`, let
  `F(w)` be the generating function of the first hitting time of the parent of
  a vertex. A first step to the parent, or to one of `q'` children followed by
  two parent-hits, gives `q' w F^2 - (q'+1) F + w = 0`. The root with
  `F(0) = 0` is taken. A return to `e` is one step followed by a parent hit, so

  ```text
  G_nu(w) = 1/(1 - w F(w)) = 2q' / ( (q'-1) + sqrt((q'+1)^2 - 4 q' w^2) ).
  ```

  Its radius is `2/sqrt 3`, so `rho_nu = sqrt 3/2`, and `G_nu(2/sqrt 3) = 3`.
- **Green function of the lazy walk.** Expand
  `mu^(*n)(e) = sum_j C(n,j) 3^(-(n-j)) (2/3)^j nu^(*j)(e)` and sum over `n`:

  ```text
  G_Q(w) = (1 - w/3)^(-1) G_nu( 2w/(3 - w) ).
  ```

  The map `w -> 2w/(3-w)` is increasing on `[0,3)`. So the radius of `G_Q` is
  the solution of `2w/(3-w) = 2/sqrt 3`, namely `w = 3/(1 + sqrt 3)`, and
  `rho_Q = (1 + sqrt 3)/3 ≈ 0.910684`. This is larger than
  `rho_T = sqrt 5/3 ≈ 0.745`.
- **rho-transience.** At the radius,
  `G_Q(1/rho_Q) = ((1 + sqrt 3)/sqrt 3) · 3 = 3 + sqrt 3 < infinity`.
- **`s_N`.** The quadratic is `5 s^2 - 2(1 + sqrt 3) s + 1 = 0`, whose smaller
  root is

  ```text
  s_N = (2 + 2 sqrt 3 - sqrt(8 sqrt 3 - 4))/10 = 0.23246101817...
  ```

  Then `phi(s_N) = 0.74474008588...` and
  `chi^N_(s_N) = phi(s_N)(3 + sqrt 3) = 3.52414792481...`. This exceeds
  `p_c(T) = 1/5`, as (A4) predicts from `rho_Q < 1`.

The script checks (2.2) exactly for `n <= 14` against brute force. It also
checks that the series coefficients up to `n = 240` are nonnegative, and that
`sqrt(h_(n+1)/h_(n-1))` increases slowly towards `1/s_N = 4.3018`, taking the
values `4.2051, 4.2511, 4.2674, 4.2756` at `n = 60, 120, 180, 239`. The slow
approach is consistent with a square-root singularity of `G_nu`.

### 6.3. `N = [F_2,F_2]`, `Q = Z^2` (Corollary D)

Here `d = 2`, `q = 3`, and `rho_T = sqrt 3/2`.
- **`rho_Q = 1`.** The box argument gives `rho_Q = 1`.
- **`s_N`.** The quadratic is `3 s^2 - 4 s + 1 = (3s - 1)(s - 1)`, so
  `s_N = 1/3 = p_c(T)`.
- **Divergence.** For simple random walk on `Z^2`,
  `p_(2n) = (C(2n,n) 4^(-n))^2 ~ 1/(pi n)`, so `G_(Z^2)(1) = infinity` (Pólya).
  By (A3), `chi^N_(1/3) = infinity`.

So `D(N)` holds, and `p_c(N;T) = p_c(T)`.

### 6.4. A non-normal check: `H = <a_1>`

`f_n(H) = 2` for `n >= 1`, so `chi^H_p = (1+p)/(1-p)`, with `R_H = 1`.
- An `H`-infinite cluster contains the geodesic between any two of its points
  in `H`, hence an infinite ray of the line `H`. That has probability `0` for
  `p < 1`.
- So `p_c(H;T) = 1`, and `D(H)` holds.
- This is the "geodesic line in a tree" check of the frontier map, Section
  7(d). It exhibits both a gap and divergence, but along a non-normal subgroup.

## 7. Consequences for the frontier map and the residual class

### 7.1. `D(I)` is not a general principle

Section 7(d) of the frontier map proves correctly that `D(I)`, together with
`chi^I_(p_c(G)) < infinity`, gives `p_c(G) < p_c(I;G)`. It lists two checks
consistent with `D`: the `Z`-axis in `Z^2`, and a geodesic line in a tree. Both
are cyclic, non-normal subgroups.

By (A3), `D(N)` fails for *every* `N ◁ F_d` with `rho_Q > rho_T` whose quotient
walk is rho-transient. Corollaries B and C are explicit instances, proved in
Section 6 without imports beyond Pólya's theorem and Watson's closed form. The
closed form is used only for the numerical value.

So `D(I)` cannot be used as a black box, even for infinite normal subgroups of
free groups on their standard trees.

### 7.2. Critical relative finiteness does not force a gap

In Corollary B, `chi^N_(p_c(T)) < infinity`, yet `p_c(N;T) = p_c(T)`. So the
implication

```text
chi^I_(p_c(G)) < infinity   ==>   p_c(G) < p_c(I;G)
```

is false in general, for an infinite normal `I` on a tree. The premise of
`fpbs-relative-gap-along-any-subgroup-separates` has to be finiteness of
`chi^I_p` at some `p` strictly above `p_c(G)`. The value at `p_c(G)` is not
enough.

At `p = p_c(T) = 1/q` we have `(q+1) z(1/q) = 1` and `phi(1/q) = (q-1)/q`, so
(A1) reads

```text
chi^N_(p_c(T)) = ((q-1)/q) G_Q(1).                              (7.1)
```

This holds for every `N ◁ F_d` with `rho_Q > rho_T`. It is the mean-field
prediction of Section 4.2 of `relative-susceptibility-reduction.md`, the Green
function of the quotient walk at `1`, now proved with an explicit constant. So
on trees, critical relative finiteness along `N` holds iff the quotient walk is
transient.

In case C, (7.1) gives `chi^N_(1/5) = (4/5) · (3/2) · G_nu(1)`. With
`G_nu(1) = 6/(2 + sqrt 4) = 3/2`, this is `9/5`.

### 7.3. On trees, `D` and the gap are decoupled

For `N ◁ F_d` with `rho_Q > rho_T`, Theorem A gives:
- the gap `p_c(T) < p_c(N;T)` holds iff `rho_Q < 1`;
- `D(N)` holds iff `mu` is rho-recurrent.

| gap | `D(N)` | example |
| --- | --- | --- |
| yes | no | Corollary C: `<<a_3>>`, `Q = F_2` |
| no | no | Corollary B: `[F_3,F_3]`, `Q = Z^3` |
| no | yes | Corollary D: `[F_2,F_2]`, `Q = Z^2` |
| yes | yes | no normal example; the non-normal `<a_1>` of 6.4 has both |

A Guivarc'h-type theorem says that symmetric finitely supported walks on
nonamenable groups are rho-transient. It is an **unverified import**, not
checked here. If it holds, the last row is empty for normal subgroups, and
Theorem A then says: on trees, `D(N)` implies no gap.

Either way, the mechanism the crux relies on, "divergence at the relative
threshold", is not how the gap arises along normal subgroups of free groups.
There the gap comes with a *finite* relative susceptibility at the relative
threshold.

### 7.4. What this means for `fpbs-residual-price-one-non-ah-class-nonuniqueness`

**Nonamenable subgroups only.** The known members of the residual class are in
(R0): torsion groups with only finite amenable subgroups, such as `T x T'` for
Tarski monsters. The infinite subgroups `I` available for
`fpbs-relative-gap-along-any-subgroup-separates` there are nonamenable. The
natural ones are normal with nonamenable quotient, like `H x 1` in `H x K`.

**What the tree predicts.** The tree analogue of that situation is Corollary C:
the gap holds and `D` fails. So along such `I` the gap would need a direct
proof that `chi^I_p < infinity` slightly above `p_c(G)`, that is, a
continuation of the relative susceptibility past `p_c(G)`. On trees this
continuation is explicit: `chi^N_p = phi(p) G_Q((q+1) z(p))`.
- It is finite on `[1/q, s_N)`, because `(q+1) z(p) < 1/rho_Q` there.
- At `s_N` it is finite in the rho-transient case.

**Why the tree proof does not transfer.** Identity (2.2) uses two facts
specific to trees:
- `tau_p(o,h) = p^|h|` is multiplicative along the unique geodesic;
- reduced words give a non-backtracking path count with the exact recursion of
  Lemma 2.1.

On a Cayley graph with cycles, `tau_p` is not a multiplicative path weight.
There is no analogue of the substitution `s -> z(s)`, and Proposition 4.3's
branching process has no disjointness.

**What does transfer.** The union bound of Section 4.1 of
`relative-susceptibility-reduction.md` gives `p_c(N;G) >= 1/(d rho(Q))` for
every Cayley graph and normal `N`. It certifies a gap only perturbatively. On
the tree it gives `z_Q = 1/((q+1) rho_Q)`, which is strictly smaller than
`s_N = z_Q (1 + q s_N^2)`.

**Simple members.** A single Tarski monster has no infinite proper subgroup, so
the only choice is `I = Gamma`. There the relative susceptibility is the
ordinary susceptibility, and nothing is gained.

**Question 7.1** (not claimed). Let `G` be a Cayley graph of `Gamma`, and let
`N ◁ Gamma` be infinite with `Gamma/N` nonamenable. Is
`p_c(G) < p_c(N;G)`?
- (A4) answers yes for `Gamma = F_d` on its standard tree.
- A yes answer, with `fpbs-relative-gap-along-any-subgroup-separates`, would
  give `p_c < p_u` for every `H x K` with `K` nonamenable and `H` infinite.
  That includes the (R0) products.
- It would say nothing about simple members.

The tree case suggests attacking it by bounding `chi^N_p` directly, not through
`D(N)`.

## 8. Computations

The script is
`experiments/fpbs-tree-relative-cogrowth-2026-09-16/verify_cogrowth_identity.py`.
It is single-threaded, runs in under 2 seconds, and its output is
`output.txt` in the same folder, from a run on 2026-09-16 with exit code 0.

The script:
1. computes `f_n([F_3,F_3])` for `n <= 22` by dynamic programming over reduced
   words and exponent sums. It compares them, as exact integers, with the
   coefficients of `phi(s) sum_m g_m z(s)^m`, where
   `g_m = sum_(i+j+k = m/2) m!/(i!^2 j!^2 k!^2)` counts closed walks on `Z^3`.
   All 23 agree.
2. computes `f_n(<<a_3>>)` for `n <= 14` by dynamic programming over the image
   in `F_2`. It compares them exactly with the series built from
   `g_m = ((2I + A_(T_4))^m)(e,e)`. All 15 agree.
3. evaluates Watson's closed form, giving `G_(Z^3)(1) = 1.516386059` and
   `(4/5) G = 1.213108847`.
4. checks, for case C, that the series coefficients up to `n = 240` are
   nonnegative. It sums `sum_(n<=240) h_n 5^(-n) = 1.800000000`, confirming
   (7.1) in the form `9/5`, and evaluates `s_N`, `phi(s_N)` and
   `chi^N_(s_N) = 3.52414792481`.

Items 1 and 2 are consistency checks of Lemma 2.2. They are not part of any
proof. The proofs in Sections 2–6 do not depend on computation.

## 9. References

**Metadata verified by Crossref lookup on 2026-09-16.** The contents were not
re-read here.
- H. Kesten, *Symmetric random walks on groups*, Trans. Amer. Math. Soc. 92
  (1959) 336–354, DOI 10.1090/s0002-9947-1959-0109367-6. Kesten's criterion,
  used only in the Remarks.
- W. Woess, *Cogrowth of groups and simple random walks*, Arch. Math. 41
  (1983) 363–370, DOI 10.1007/bf01371408. The cogrowth formula.
- S. Northshield, *Cogrowth of arbitrary graphs*, in Random Walks and Geometry
  (de Gruyter, 2004) 501–514, DOI 10.1515/9783110198089.2.501. Cogrowth
  beyond Cayley graphs.
- R. Ortner and W. Woess, *Non-backtracking random walks and cogrowth of
  graphs*, Canad. J. Math. 59 (2007) 828–844, DOI 10.4153/cjm-2007-035-1.
- M. L. Glasser and I. J. Zucker, *Extended Watson integrals for the cubic
  lattices*, PNAS 74 (1977) 1800–1801, DOI 10.1073/pnas.74.5.1800. The closed
  form of `G_(Z^3)(1)`, used only numerically.

**Repo sources.**
- Hutchcroft–Pan, arXiv:2409.12283v1 (2024-09-18). The definition of
  `p_c(H;G)`, as recorded in
  `research/artifacts/fpbs/docs/relative-susceptibility-reduction.md`.
  Relative sharpness is `fpbs-hp-relative-sharpness`, which is not used in the
  proofs here.
- `research/artifacts/fpbs/docs/benjamini-schramm-frontier-map.md`, Section 7.

**Unverified, not fetched.** Cited for attribution or interpretation only.
- R. I. Grigorchuk, *Symmetrical random walks on discrete groups*, in
  Multicomponent Random Systems, Adv. Probab. Related Topics 6 (Dekker, 1980)
  285–325. The original cogrowth formula and criterion.
- G. N. Watson, *Three triple integrals*, Quart. J. Math. (1939). The value of
  `G_(Z^3)(1)`.
- G. Pólya, 1921. Recurrence and transience of simple random walk on `Z^d`.
- Y. Guivarc'h, 1980. The rho-transience of walks on nonamenable groups, used
  only in the conditional remark of 7.3.
- A. Pringsheim, *Pringsheim's theorem* on power series with nonnegative
  coefficients. A standard textbook fact, used in Lemma 2.3.

# STW LXI is a uniform exponential-length statement

Lane `ex-k1-properly-infinite`, 2026-09-12. Complete proofs. Not externally reviewed. This is a
reformulation: it does not decide LXI.

## 1. Definitions

For a unital C\*-algebra A and `u in U_0(A)`, the exponential length is
`cel_A(u) = inf { sum_j ||h_j|| : u = e^{i h_1} ... e^{i h_r}, h_j = h_j^* in A }`, and `cel_A(u) = infinity`
if u is not in `U_0(A)`. For unital properly infinite A and `L >= 0` put
`F_A(L) = sup { cel_A(u) : u in U(A), cel_{M_2(A)}(diag(u,1)) <= L }` (sup of the empty set is 0).

LXI (Blanchard--Rohde--Rordam): every unital properly infinite C\*-algebra is K1-injective.

## 2. Lemma A (bounded number of bounded factors)

**Lemma A.** If `cel_B(v) < L`, then `v = e^{i k_1} ... e^{i k_M}` with `M = floor(2L) + 3` and every
`||k_t|| <= max(pi, L)`.

*Proof.* Write `v = e^{i h_1} ... e^{i h_r}` with `sum ||h_j|| < L`. Greedily cut the word into consecutive
blocks: a block is a maximal run of consecutive factors whose norms sum to at most 1, or a single
factor of norm greater than 1. Two consecutive blocks together have norm sum greater than 1, so there
are at most `2L + 2` blocks. A single-factor block is `e^{i h_j}` with `||h_j|| <= L`. For a block w of
total norm at most 1, `||w - 1|| <= e - 1 < 2`, so -1 is not in the spectrum of w and the principal
logarithm gives `w = e^{i k}` with `||k|| <= pi`. Pad with `k_t = 0`. Square.

## 3. Theorem B

**Theorem B.** The following are equivalent.
1. LXI holds.
2. There is a function `F: [0,infinity) -> [0,infinity)` such that `F_A(L) <= F(L)` for every unital
   properly infinite A and every L.
3. `F_A(L) < infinity` for every unital properly infinite A and every L.

*Proof of 2 => 3.* Trivial.

*Proof of 3 => 1.* Let A be unital properly infinite and `[u] = 0` in `K_1(A)`. By BRR Lemma 2.4(ii),
applied in `M_2(A)` to `diag(u,1)` and `p = diag(1,0)` (both p and 1-p are properly infinite and full,
and p commutes with `diag(u,1)`), `diag(u,1)` lies in `U_0(M_2(A))`. This is how BRR prove
Proposition 5.2 (ii)=>(i). So `cel(diag(u,1)) = L < infinity`, and `cel_A(u) <= F_A(L+1) < infinity`,
so u is in `U_0(A)`.

*Proof of 1 => 2.* Suppose 2 fails. Then for some `L` there are unital properly infinite `A_n` and
`u_n in U(A_n)` with `cel(diag(u_n,1)) <= L` and `cel_{A_n}(u_n) > n` (possibly infinite). Let
`Q = l^infty(A_n) / c_0(A_n)` and `u = [(u_n)]`.

- Q is unital and properly infinite: choose isometries `s^{(n)}, t^{(n)}` in `A_n` with orthogonal
  ranges. Their classes in Q are isometries with orthogonal ranges.
- `[u] = 0` in `K_1(Q)`. By Lemma A with `L+1`, `diag(u_n,1) = prod_{t <= M} e^{i k_{t,n}}` with
  `||k_{t,n}|| <= max(pi, L+1)` and M independent of n. Then `k_t = [(k_{t,n})_n]` is self-adjoint in
  `M_2(Q) = l^infty(M_2(A_n)) / c_0(M_2(A_n))`, and `diag(u,1) = prod_t e^{i k_t}` in `M_2(Q)`. So
  `diag(u,1)` is in `U_0(M_2(Q))`.
- By 1, u is in `U_0(Q)`: `u = e^{i h_1} ... e^{i h_m}` in Q. Lift each `h_t` to a self-adjoint
  `(h_{t,n})_n` with `sup_n ||h_{t,n}|| <= ||h_t|| + 1`. (Lift arbitrarily, take real parts, and cut down by
  the continuous function `max(min(s, c), -c)` with `c = ||h_t|| + 1`; this changes the class by nothing,
  because the image already has norm at most `||h_t||`.) Then
  `||u_n - prod_t e^{i h_{t,n}}|| -> 0`.
- For large n put `w_n = u_n (prod_t e^{i h_{t,n}})^*`. Once `||w_n - 1|| < 1`, the principal logarithm
  gives `w_n = e^{i g_n}` with `||g_n|| <= pi/3`. So
  `cel(u_n) <= pi/3 + sum_t (||h_t|| + 1)`, a bound independent of n. This contradicts `cel(u_n) > n`. Square.

*Proof of 1 => 3 directly.* Apply the argument above to the constant sequence `A_n = A`.

## 4. Consequences

1. **A counterexample can be assembled from K1-injective algebras.** To refute LXI it suffices to find
   unital properly infinite `A_n`, each of which may well be K1-injective, and unitaries `u_n` with
   `cel(diag(u_n,1))` bounded and `cel(u_n) -> infinity`. The sequence algebra is then properly
   infinite and not K1-injective. BRR Theorem 5.5 turns this into a separable counterexample: the
   free product `O_infty * O_infty` would fail K1-injectivity.
2. **A single algebra suffices.** One unital properly infinite A with `F_A(L) = infinity` for some L
   refutes LXI, even if A itself is K1-injective.
3. **Positive answers must be quantitative.** Any proof of LXI yields a universal function F. For
   algebras with an asymptotically central sequence of projections `p` such that `p` and `1-p` are
   properly infinite and full, BRR Proposition 6.1 already gives K1-injectivity. By Theorem B, its
   proof must control length. The obstruction to a proof is exactly a family in which every
   null-homotopy of `u_n` is forced to be long while one stabilization shortens it.
4. **Where lower bounds could come from.** Traces do not exist on properly infinite algebras, so
   determinant-type lower bounds on `cel` (de la Harpe--Skandalis) are unavailable. Lower bounds must
   be topological or combinatorial and survive the unital embeddings `T_2 -> A_n`. This is the
   quantitative form of the detection problem recorded in the LXI Attempts: no unital homomorphism
   out of a properly infinite algebra lands in a finite algebra.

## 5. Novelty check (bounded)

Not found in BRR (J. Noncommut. Geom. 2 (2008), all of Sections 2, 4, 5, 6 read), Blanchard
arXiv:0804.4624v13 (all pages), arXiv:1507.02535v1 (all pages), or the table of contents and abstract
of R. Rohde's thesis (Odense 2009). Sequence-algebra arguments for exponential length are standard
(Phillips, Lin), so the observation is elementary. Its value is the reformulation of LXI as a
uniform quantitative statement.

# One transcendental coefficient: the determinant conjecture empties the exceptional set

Lane `ex-atiyah-torsion-free`, 2026-09-12. Supports the claim
`determinant-conjecture-gives-one-variable-atiyah-base-change`.

The note builds on `research/artifacts/atiyah-countable-exceptions-2026-09-12.md`
(Theorem 1: the exceptional set `E_G` is countable). It supersedes Section 5 of
`research/artifacts/atiyah-liouville-base-change-2026-09-12.md`, which said the
box principle could not empty `E_G`. It can, once polynomial *values* at the
parameter are used together with a resultant identity, instead of algebraic
approximants of the parameter.

## 0. Theorem 3

Let `G` be torsion-free. Suppose `G` satisfies Strong Atiyah over `Qbar` and
Lueck's determinant conjecture (for every matrix `X` over `Z[G]`, the
Fuglede--Kadison determinant of `r_X` off its kernel is `>= 1`). Then `E_G = ∅`.
Equivalently, for every transcendental `z in C`:

1. `x -> z` embeds `D(x)` in `U(G)` as the division closure of `Qbar(z)[G]`,
   where `D = D_(Qbar[G])`;
2. every matrix over `Qbar(z)[G]` has integral kernel dimension;
3. kernel dimensions of matrices over `Qbar(z)[G]` do not change when `z` is
   replaced by another transcendental number. This is one-variable Galois
   invariance.

The implications (`E_G = ∅`) => 1, 2, 3 are items 2-3 of Theorem 1.

Notation:
* `Delta(T) = exp (tau (x) Tr)(log |T|)` is the Fuglede--Kadison determinant of a
  bounded operator on `l^2(G)^N`, with the unnormalized matrix trace.
* `nu_T` is the distribution of `|T|`, of total mass `N`.
* For injective square `T`, `Delta(T)` is Lueck's `det_(N(G))(r_T)`.
* For `P in Z[x]` with leading coefficient `a` and roots `alpha_j`, the Mahler
  measure is `M(P) = |a| prod_j max(1, |alpha_j|)`, and `M(P) <= (deg P + 1)^(1/2) H(P)`.

Properties of `Delta` used (Lueck, *L^2-Invariants*, 2002, Theorem 3.14, for
weak isomorphisms; not re-read here):
- **(D1)** `Delta` of a block-diagonal operator is the product of the blocks' determinants;
- **(D2)** `Delta(A T B) = Delta(A) Delta(T) Delta(B)` for injective `T` and
  invertible scalar matrices `A, B`;
- **(D3)** `Delta(I_N (x) S) = |det S|^N` for a scalar matrix `S`.

## 1. Reduction to square integral pencils

Suppose `z_0` is transcendental and some `A(x)` over `Qbar[G][x]` has excess
`kappa = dim ker A(z_0) - (n - r(A)) > 0`. We produce a square pencil over
`Z[G]`, full over `D(x)`, with excess at least `kappa` at `z_0`.

* **(R1) Linearization (Higman's trick).** Over any ring `R`, the identity

  ```text
  [[1, -b], [0, 1]] [[a, b], [-c, 1]] [[1, 0], [c, 1]] = [[a + bc, 0], [0, 1]]
  ```

  with `a = A_0`, `b = x I`, `c = B(x)`, where `A(x) = A_0 + x B(x)`, shows that
  `A(x) (+) I` is equivalent over `R[x]` to `[[A_0, xI], [-B(x), I]]`. The degree
  in `x` of the remaining block drops. By induction `A(x) (+) I_k` is equivalent
  to a linear pencil `L(x) = L_0 + x L_1` over `Qbar[G]`.
  - The equivalences are products of elementary matrices over `Qbar[G][x]`, so
    they specialize to invertible matrices at every `z`.
  - Kernels at `z` agree, and generic ranks shift by `k`. So the excess is
    unchanged.
* **(R2) Square and full.** Let `L` be `m x n` with generic rank `r` over `D(x)`.
  - Choose `n - r` coordinates on which the generic kernel projects bijectively
    (pivots over the skew field `D(x)`), and let `W` be the corresponding
    coordinate matrix.
  - Choose `m - r` standard basis vectors completing the generic image, as the
    columns of `Y`.
  - Then `M = [[L, Y], [W, 0]]` is square and full over `D(x)`.
  - At `z_0`, `ker M(z_0)` contains `(ker L(z_0) cap ker W) (+) 0`. Dimensions of
    `U(G)`-submodules satisfy `dim(U cap V) >= dim U + dim V - dim(ambient)`, so
    this has dimension at least `(n - r + kappa) + r - n = kappa`.
  - `M` has generic kernel `0`, so its excess at `z_0` is at least `kappa`.
* **(R3) Integral coefficients.** Scale so the coefficients lie in `O_F` for a
  number field `F`, and restrict scalars along a Z-basis of `O_F`. The result
  `rho(M)(x)` is a square pencil over `Z[G]`.
  - `rho(M)(z_0)` is similar, by an invertible scalar matrix independent of `x`,
    to the direct sum over the embeddings `sigma: F -> C` of the conjugate pencils
    `M^sigma(z_0)`.
  - Each `M^sigma` is over `Qbar[G]`, and its excess is `>= 0` by the normal form
    over `D[x]` (Theorem 1, Section 2). So the excess of `rho(M)` at `z_0` is at
    least `kappa`.
  - Apply (R2) once more, to `rho(M)` over `Z[G]`, with 0-1 coordinate matrices.

**Output.** `M(x) = M_0 + x M_1`, with `M_0, M_1` in `M_N(Z[G])`, full over `D(x)`,
and `kappa_0 := dim ker M(z_0) >= kappa > 0`. By Theorem 2, item 1, of the
Liouville artifact, only finitely many algebraic numbers `beta_1..beta_q` have
`M(beta_i)` non-injective. Let `m_1..m_q` be their primitive minimal
polynomials.

## 2. The resultant identity

Let `p in Z[x]` be irreducible and primitive, of degree `d >= 1`, with leading
coefficient `a`, distinct roots `alpha_1..alpha_d`, and `p` not among the `m_i`.

* **Companion pencil.** Write `p = a x^d + c_(d-1) x^(d-1) + ... + c_0`. Put
  `E = diag(1, ..., 1, a)`, and let `F` be the integer matrix with `1` on the
  superdiagonal and last row `(-c_0, ..., -c_(d-1))`. Expanding along the last
  row gives `det(xE - F) = p(x)`.
* **Diagonalization.** `E^-1 F` has characteristic polynomial `p/a`, with distinct
  roots, so `E^-1 F = V Lambda V^-1` with `Lambda = diag(alpha_j)`.
* **The integral model.** Put `X := M_0 (x) E + M_1 (x) F in M_(Nd)(Z[G])`. Then

  ```text
  (I_N (x) V^-1 E^-1) X (I_N (x) V)  =  M_0 (x) I_d + M_1 (x) Lambda  =  (+)_j M(alpha_j).
  ```

* **The identity.** Every block is injective, so `X` is injective. By (D1)-(D3),
  and since `det(V^-1 E^-1) det V = 1/a`,

  ```text
  Delta(X)  =  |a|^N  prod_(j=1..d) Delta(M(alpha_j)).                         (RES)
  ```

For `G = 1` and `N = 1`, (RES) is the classical formula
`Res(p, M) = a^(deg M) prod_j M(alpha_j)`.

## 3. The upper bound at a kernel point

Put `c_M = max(||M_0||, ||M_1||, 1)`. For every `alpha in C`,

```text
Delta(M(alpha))  <=  C_0 * |alpha - z_0|^(kappa_0) * max(1, |alpha|)^(N - kappa_0),
C_0 = ||M_1||^(kappa_0) (2 c_M)^(N - kappa_0).                                  (UB)
```

*Proof.*
* **Small values.** `||M(alpha) - M(z_0)|| = |alpha - z_0| ||M_1||`, and
  `M(z_0)` has kernel dimension `kappa_0`. By min-max (Lemma 2 of the Liouville
  artifact), `nu_(M(alpha))` puts mass at least `kappa_0` on
  `[0, |alpha - z_0| ||M_1||]`.
* **Large values.** All of `nu_(M(alpha))` lies below
  `||M(alpha)|| <= c_M (1 + |alpha|) <= 2 c_M max(1, |alpha|)`.
* **Combine.** `log` is increasing, so
  `integral log s d nu <= kappa_0 log(|alpha - z_0| ||M_1||) + (N - kappa_0) log(2 c_M max(1,|alpha|))`.
  If `|alpha - z_0| ||M_1||` exceeds the norm bound, the right side still
  dominates, because it is at least `N log ||M(alpha)||`. ∎

## 4. The polynomial inequality

For `p` as in Section 2, apply the determinant conjecture to `X` and then (RES)
and (UB), using `prod_j |z_0 - alpha_j| = |p(z_0)|/|a|` and
`prod_j max(1, |alpha_j|) = M(p)/|a|`:

```text
1 <= Delta(X) = |a|^N prod_j Delta(M(alpha_j))
             <= |a|^N C_0^d (|p(z_0)|/|a|)^(kappa_0) (M(p)/|a|)^(N - kappa_0)
              = C_0^d |p(z_0)|^(kappa_0) M(p)^(N - kappa_0).
```

Hence, for every irreducible primitive `p` of degree `<= n` other than the `m_i`,

```text
|p(z_0)|  >=  C_0^(-n/kappa_0) * M(p)^(-beta),        beta := (N - kappa_0)/kappa_0.   (POLY)
```

The `m_i` satisfy `|m_i(z_0)| >= c_3 > 0`, because `z_0` is transcendental.

## 5. Small polynomials, and the conclusion

**Box principle.** Fix `n >= 1` and `H >= 1`.
* **Real case.** The `(H+1)^(n+1)` polynomials with coefficients in `[0, H]`
  take values at `z_0` in an interval of length at most
  `(n+1) H max(1, |z_0|)^n`. Two of them have values within
  `(n+1) max(1,|z_0|)^n H^(-n)` of each other. Their difference `P_H` is nonzero,
  with `deg <= n`, `H(P_H) <= H` and `|P_H(z_0)| <= c_1 H^(-w)`, where `w = n`.
* **Complex case.** Pigeonholing the values in squares gives the same with
  `w = (n-1)/2`.

**Factor.** Write `P_H = ± prod_i p_i^(e_i)` with irreducible primitive `p_i`,
so that `sum_i e_i <= n` and `prod_i M(p_i)^(e_i) = M(P_H) <= (n+1)^(1/2) H`. By
(POLY) and the bound for the `m_i`,

```text
c_1 H^(-w)  >=  |P_H(z_0)|  =  prod_i |p_i(z_0)|^(e_i)
            >=  prod_i ( c_4 M(p_i)^(-beta) )^(e_i)  >=  c_4^n (n+1)^(-beta/2) H^(-beta),
```

with `c_4 = min(C_0^(-n/kappa_0), c_3, 1)`, using `M(p_i) >= 1`. Letting
`H -> infinity` gives `w <= beta`, with `n` arbitrary. Choose
`n > beta` in the real case, or `n > 2 beta + 1` in the complex case. This is a
contradiction. So `kappa_0 = 0`, hence `kappa = 0`, and `z_0` is not exceptional.
∎

## 6. What it gives, and what remains

* **One transcendental coefficient.** A torsion-free group with Strong Atiyah
  over `Qbar` and the determinant conjecture satisfies Strong Atiyah over
  `Qbar(z)` for every complex `z`, with the division closure `D(x)` independent
  of `z`. One-variable Galois invariance of von Neumann ranks holds.
* **At the master host.** `algebraic-atiyah-and-determinant-one-group-tester` says
  `SA(E)` and `Det(E)` hold iff both hold for every torsion-free group. So under
  `SA(E)` and `Det(E)` every torsion-free group has these properties. That node's
  "Nothing over C" needs this amendment.
* **The approximation-free character.** The group is never approximated. The
  parameter is not approximated either. The inputs are only the skew field `D`
  and the integrality of the companion models `X`.
* **Correction to the Liouville artifact.** Its Section 5 said the box principle
  gives only a bounded excess. That estimate used algebraic approximants of `z_0`
  and restriction of scalars. The losses there were `d log H` per approximant,
  against a gain of `(d/2) log H`. The resultant identity (RES) loses only
  `N log M(p)`, while Minkowski's small values give `n log H`, so the gain grows
  with the degree. Theorem 2 of that artifact is still true, but it is now
  superseded.
* **What remains open.**
  - *Several algebraically independent coefficients.* The Kronecker product of
    two companion pencils gives the analogue of (RES), but there is no product
    formula relating `prod_(j,k) dist((alpha_j, beta_k), z)` to polynomial values
    at `z`. The loss becomes `N (d_2 log M(p_1) + d_1 log M(p_2))`, and the
    one-block gain does not beat it.
  - *Algebraic extensions of `Qbar(z)`.* One needs `D(x) (x) F` to be a skew field
    in `U(G)`. An identity like (RES) along the fibres of a coordinate function
    on a curve looks feasible but was not carried out.
  - So `strong-atiyah-base-change-algebraic-to-complex` is reduced, under the
    determinant conjecture, to transcendence degree at least 2 and to algebraic
    extensions.

## 7. Model tests

* **Strong Atiyah over `Qbar` is used.** For `G = Z/2` the family `x(1+s)/2` has
  kernel `1/2` at every `z != 0`. The skew field `D`, and with it the normal form
  and the finite jump set, fail.
* **The determinant conjecture is used.** Take a self-adjoint `t` with an atom `1/2`
  at `pi` and no algebraic atoms, and `D = Qbar(t)`. There `pi` is exceptional,
  and no integral model obeys (RES) with `Delta >= 1`. Compare
  `serre-class-atoms-obey-degree-bound`: under the determinant conjecture, integral
  self-adjoint matrices have no transcendental atoms.
* **A real object.** Sofic groups satisfy both hypotheses, and Jaikin-Zapirain's
  base change (GAFA 29 (2019), Theorem 1.1) gives the conclusion independently.

**Novelty (bounded check).** The ingredients are standard: Higman
linearization, Jacobson's normal form, the companion pencil, Minkowski's box
principle, and Fuglede--Kadison determinants. The combination was not found in
Jaikin-Zapirain--Lopez-Alvarez (arXiv:1810.12135v4), in Badziahin--Schleischitz
(arXiv:1912.09013v1, read for the exponent literature), or in this graph. No
wider search was possible: the session's web-search budget was exhausted.
Unreviewed.

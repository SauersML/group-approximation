# Two transcendental coefficients under the determinant conjecture, part 4

Lane `ex2-atiyah-base-change-td2`, 2026-09-13. Continues Parts 1-3. This part
passes from `Qbar(z_1, z_2)` to every coefficient field of transcendence degree
at most 2, as Theorem 4 did in degree one. **Unreviewed.**

## 7. Theorem 6

Let `G` be as in Theorem 5, and let `F ⊂ C` be a field with
`trdeg_(Qbar) F <= 2`. Then every matrix over `F[G]` has integral kernel
dimension, and this dimension is invariant under automorphisms of `C` fixing
`Qbar`.

*Proof.*
* **Reduction.** Degree `<= 1` is Theorem 4. Otherwise take `F` finitely
  generated, `F = Qbar(V)` for an irreducible affine surface `V` over `Qbar`,
  embedded through a point `P_0 in V(C)` whose coordinates generate a field of
  transcendence degree 2. Clearing denominators by a regular function nonzero
  at `P_0` changes no kernel. So it suffices to treat a matrix `M` over
  `Qbar[V][G]` evaluated at points `P in V(C)`. Put `k(P) = dim ker M(P)`.
  - `P_0` lies on no proper subvariety of `V` defined over `Qbar`.
* **Noether normalization.** Choose a finite surjective `pi: V -> A^2` over
  `Qbar`. By generic freeness and generic smoothness there is a nonzero
  `g in Qbar[x_1, x_2]` such that over `U = A^2 \ V(g)` the algebra
  `Qbar[V]_g` is free of rank `e` over `Qbar[x]_g` and `pi` is finite étale.
* **Step 1 (fibre sums).** Restriction of scalars along a basis gives `rho(M)`
  over `Qbar[G][x]_g`. Multiply by a power of `g` to make it polynomial; this
  changes no kernel over `U`. For `w in U(C)`, evaluating the basis at the `e`
  fibre points gives an invertible scalar matrix conjugating `rho(M)(w)` to
  `(+)_(pi(P) = w) M(P)`. So `dim ker rho(M)(w) = sum_(pi(P) = w) k(P)`.
  - Let `K` be the generic kernel dimension of `rho(M)`, and put
    `U° = U \ Y_rho(M)`, with `Y_rho(M)` from Lemma J.
  - Fibre sums equal `K` at every `w in U°(C)`:
    - `w` algebraic: this is Lemma J.
    - `trdeg w = 2`: this is Theorem 5.
    - `trdeg w = 1`: `w` is a generic point of an irreducible curve
      `W ⊂ A^2` over `Qbar`, and `W` is not contained in `Y_rho(M)`, since
      `w notin Y_rho(M)`. Pull `rho(M)` back to the normalization `W~` of `W`,
      a smooth affine curve over `Qbar`. The proof of Theorem 4 (Steps 1-2 of
      the transcendence-degree-one artifact) shows that the kernel dimension
      is constant on `W~` off finitely many algebraic points. The value at a
      point of `W` is the value at any preimage. At the algebraic points of
      `W` off `Y_rho(M)` it equals `K`. So it is `K` at `w`.
      *(Justification made explicit by ex-verify2-quantum-l2, 2026-09-13. The
      statement of Theorem 4 gives only integrality and invariance, and
      invariance moves `w` only among generic points of `W`. Constancy along a
      curve is what its proof gives, for smooth curves, hence the
      normalization.)*
* **Step 2 (continuity).** `k` is upper semicontinuous on `V(C)`, by Lemma 4 of
  the Liouville artifact. Let `P in V° = pi^-1(U°)`, with fibre
  `P = P_1, ..., P_e` over `w = pi(P)`.
  - Since `pi` is finite étale over `U`, for `P'` near `P` the fibre of `pi(P')`
    is `P' = P'_1, ..., P'_e` with `P'_i` near `P_i`.
  - By Step 1 and upper semicontinuity at `P_2, ..., P_e`,

    ```text
    k(P') = K - sum_(i >= 2) k(P'_i)  >=  K - sum_(i >= 2) (k(P_i) + eps)  =  k(P) - (e-1) eps.
    ```

  - So `k` is continuous on `V°(C)`.
* **Step 3 (constancy).**
  - At algebraic points of `V°`, `k` is an integer, by Strong Atiyah over
    `Qbar`. Such points are dense in `V°(C)`, so the continuous `k` is
    integer-valued on `V°(C)`, hence locally constant.
  - `V°` is an irreducible variety minus a proper Zariski-closed set, so
    `V°(C)` is connected, and `k` is constant on it.
  - `P_0` lies in `V°`, because it is on no proper `Qbar`-subvariety. So `k(P_0)`
    is that integer.
  - An automorphism `sigma` of `C` fixing `Qbar` maps `P_0` to another point of
    `V(C)` with the same property, which therefore also lies in `V°`. This gives
    the invariance. ∎

## 8. Consequences in transcendence degree 2

* **Eigenvalues over division closures of fields of degree one.** Let `F_1` have
  transcendence degree 1. Every eigenvalue of a square matrix over
  `D_(F_1[G])` is algebraic over `F_1`.
  - Suppose `z` is transcendental over `F_1` and `dim ker(z - C) > 0`.
  - Section 2 of the countable-exceptions artifact linearizes `C` with a
    Schur complement. This gives a one-variable family over `F_1[G][x]` that
    jumps at `z`.
  - Write `F_1(z) = Qbar(V)` with `P_0 = (P_1, z)`, where `P_1` generates `F_1`.
    The proof of Theorem 6 shows that `k` is constant on `V°(C)`. That set
    contains every `(P_1, z')` with `z'` transcendental over `F_1`.
  - Theorem 4 gives Strong Atiyah over `F_1`. So Theorem 1 of the
    countable-exceptions artifact applies over the base `F_1`, and the kernel
    dimension equals the generic rank over `D_(F_1[G])(x)` for all but countably
    many such `z'`.
  - Hence it equals the generic rank at `z` too, and there is no jump, which is
    a contradiction.
  - This repeats Corollary 5.1 one degree up. The use of Theorem 1 over the
    countable base `F_1` rather than `Qbar` has not been re-derived.
* **The open part of `determinant-conjecture-gives-full-atiyah-base-change`**
  is now exactly transcendence degree `>= 3`. By the same fibre argument,
  inducting on dimension, it reduces to purely transcendental fields
  `Qbar(z_1, ..., z_s)`. Parts 1-2 carry over to `A^s` unchanged:
  - Lemma J, by induction on `s` using `D(x_1..x_(s-1))[x_s]`;
  - (RES2), with `s` multiplication maps;
  - Lemma H and Corollary 6, with hyperplanes through `(1, z)`.

  What is missing is a violating form. That is an integral product `F` of linear
  forms at affine points of `A^s` with `a(F) + (B-1) b(F) + C deg F < 0`. The
  triangular chain of Part 3 does not provide one when `s = 3`.

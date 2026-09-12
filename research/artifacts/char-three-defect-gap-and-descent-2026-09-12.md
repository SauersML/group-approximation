# Characteristic-three defect gap and descent, in matricial and abstract scope

Lane `w5-c3-descent`, 2026-09-12. This ports the characteristic-two results of
`research/artifacts/two-root-defect-descent-gap-2026-09-12.md` (lane `w4-gate-descent`) to anti-central
models of the ternary Leavitt unit group, and scopes every step for abstract Sylvester rank functions.

It supports:
- `sylvester-rank-functions-compress-along-commuting-elements`;
- `ternary-anti-central-two-root-defect-has-a-uniform-gap`;
- `ternary-cylinder-defect-products-descend-in-sign-sectors`;
- `ternary-anti-central-disjoint-defects-have-a-strict-deficit`;
- an Attempts entry on `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`.

## 0. Summary

**Two scopes.**
* **(S) Abstract.** `N` is any Sylvester matrix rank function on `F_3[G]`. It need not be faithful, and the
  ring it lives on need not be regular. This is the scope of
  `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`, which the counterexample chain needs.
* **(M) Matricial.** `N(X) = rk(sigma(X))` for a homomorphism `sigma : G -> M^x` into a rank ultraproduct
  over fields of characteristic three. Every (M) function is an (S) function, so every (S) theorem is an
  (M) theorem.

**Results.**
* **Section 1 (S, any field).** Compressing a Sylvester rank function along a commuting element gives a
  Sylvester rank function. A nilpotent commuting with `P` shrinks `N(P)` by a fixed factor (Frobenius).
* **Section 2 (S, hence M): gap.** Over anti-central `N` (`N(eps_-) = 1`), `c_3 = min N(D)` is attained, and
  `0 < c_3 <= 2/3`. No fixed-point-free quotient, finite generation or displacement lemma is needed, because
  anti-centrality supplies the nontriviality.
* **Section 3 (S): descent.**
  * `f(k+1) <= (2/3) f(k)` for every `N`.
  * `f(k+1) >= c_3 h_k`, where `h_k = N(Q_B P_k)`.
  * `h_k >= N(R_+ P_k)/2` on the sign sector where the complement is anti-central.
  * `f(k+1) > 0` iff `h_k > 0`.
* **Section 4.** Which characteristic-two steps survive, in each scope.
* **Section 5.** Where it stops: the characteristic-three strict-deficit target, and its route to
  `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`.

## 1. Setting and the abstract toolkit

**Notation.**
* `R = L_(F_3)(1,2)`, `G = R^x`, and `z = -1`. The elements `eps_- = (1 - [z])/2 = 2(1 - [z])` and
  `eps_+ = 1 - eps_-` are central idempotents of `F_3[G]`.
* `G = EL_3(R)` through the code `(0, 10, 11)`. `N_ab = [x_ab(1)] - 1` lies in `F_3[G]`, and `D = N_23 N_12`.
* For a nonempty prefix `A`, `iota_A(g) = S[A] g T[A] + (1 - S[A]T[A])` is an injective endomorphism of `G`.
  `F_3[iota_A]` is its linear extension, and `D_A = F_3[iota_A](D)`.
* For a clopen `C` of Cantor space `X`:
  * `tau_C = 1 - 2 p_C` is its reflection, where `p_C` is the sum of `S[w]T[w]` over a prefix code of `C`;
  * `Q_C = 2(1 - [tau_C])` is an idempotent of `F_3[G]`, because `[tau_C]^2 = 1`;
  * `iota_A(z) = tau_A`, and `tau_(C_1 ⊔ C_2) = tau_(C_1) tau_(C_2)`, with `tau_X = z`.
* **Sylvester matrix rank functions.** `N` on a unital ring `A` assigns `N(X) >= 0` to every rectangular
  matrix over `A`, with:
  * `N(0) = 0` and `N(1) = 1`;
  * `N(XY) <= min(N(X), N(Y))`;
  * `N(X (+) Y) = N(X) + N(Y)`;
  * `N([[X, Z],[0, Y]]) >= N(X) + N(Y)`.
* **Anti-central.** `N` on `F_3[G]` is *anti-central* if `N(eps_-) = 1`. `A_S` denotes the set of anti-central
  functions and `A_M` the matricial ones. An anti-central rank model `sigma` (`sigma(z) = -1`) gives
  `N_sigma` in `A_M`.

**Lemma 1.1 (S).** Let `N` be a Sylvester matrix rank function on `A`.
1. `N(X + Y) <= N(X) + N(Y)`, and `N(uXv) = N(X)` for invertible `u` and `v`.
2. (Frobenius) `N(XY) + N(YZ) <= N(Y) + N(XYZ)`.
3. If `e` is an idempotent commuting with `P`, then `N(P) = N(eP) + N((1-e)P)`.
4. If `x` commutes with `P` and `x^m = 0`, then `N(xP) <= (1 - 1/m) N(P)`.
5. On `F_3[G]`, if `N(eps_+) = 0`, then `N(X) = N(X eps_-)` for every matrix `X`. Every anti-central `N`
   has `N(eps_+) = 0`, by item 3 with `P = 1`.

*Proof.*
1. `X + Y = [1 1] diag(X, Y) [1 1]^T`. Invariance follows from submultiplicativity applied both ways.
2. Subtract the first column times `Z` from the second, then `X` times the second row from the first. This
   takes `[[XY, 0],[Y, YZ]]` to `[[0, -XYZ],[Y, 0]]`, of rank `N(Y) + N(XYZ)`. After swapping rows and
   columns the first matrix is upper triangular with diagonal blocks `YZ` and `XY`.
3. `U = [[e, 1-e],[1-e, e]]` has `U^2 = 1`, and `U diag(eP, (1-e)P) = [[eP, (1-e)P],[0, 0]]`. Add the second
   column to the first, then subtract the first times `1-e` from the second. Since `eP = Pe`, this gives
   `[[P, 0],[0, 0]]`.
4. Put `a_j = N(x^j P)`. Frobenius applied to `(x, x^j P, x)` gives `2 a_(j+1) <= a_j + a_(j+2)`. So `a` is
   convex on `0..m` with `a_m = 0`, and `a_1 <= ((m-1) a_0 + a_m)/m`.
5. `X = X eps_- + X eps_+`, and `N(X eps_+) <= N(eps_+) = 0`. QED

**Lemma 1.2 (commuting compression, S, any ring).** Let `phi : A' -> A` be a unital ring homomorphism, `N` a
Sylvester matrix rank function on `A`, and `P` in `A` with `N(P) > 0` and `P phi(a) = phi(a) P` for every `a`.
Then `N^phi_P(X) = N(phi(X) P) / N(P)` is a Sylvester matrix rank function on `A'`.

*Proof.* Write `X'` for `phi(X)` entrywise, and let `P` act as a scalar matrix.
* `N^phi_P(1) = 1` and `N^phi_P(0) = 0`.
* `N(X'Y'P) <= N(Y'P)`, and `X'Y'P = X'PY'` gives `N(X'Y'P) <= N(X'P)`.
* `(X (+) Y)'P = X'P (+) Y'P`, and `[[X, Z],[0, Y]]'P = [[X'P, Z'P],[0, Y'P]]`. QED

No image, range idempotent or annihilator of `P` is used. This lemma replaces the corner models `q M q` of the
characteristic-two artifact.

**Lemma 1.3 (cited).**
* For any Sylvester matrix rank function `N` on `K[H]`, the set `K_N = {h : N(1 - [h]) = 0}` is a normal
  subgroup, and `N` is the augmentation rank when `K_N = H`
  (`simple-group-rank-functions-are-augmentation-or-detecting`).
* Every normal subgroup of `G` is `G` or lies in `<z>`. This is Lemma 1.1 of
  `research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md`, from
  `odd-leavitt-unit-groups-mod-scalars-are-fp-simple` and perfection.

**Lemma 1.4 (abstract corner locality, S).** If `N(D_A) = 0` for one prefix `A` (the empty prefix gives `D`),
then `N` is the augmentation rank. In particular `N(eps_-) = 0`.

*Proof.*
* `N o F_3[iota_A]` is a Sylvester rank function killing `D`.
* In `F_3[G]/ker N`, the identity `N_23 N_12 = 0` forces `N_12^2 = 0`
  (`reversed-root-pair-identity-forces-root-squares-to-vanish`, valid in any ring).
* So `N o F_3[iota_A]` is the augmentation rank, by
  `leavitt-rank-functions-killing-two-root-defect-are-augmentation` in characteristic `p`.
* Then `iota_A(G)` lies in `K_N`. That subgroup is normal and not inside `<z>`, so `K_N = G`, and the
  augmentation of `eps_-` is `0`. QED

**Fact 1.5 (V-conjugation).** Fact 1.2 of the characteristic-two artifact holds verbatim in `G`.
* `V` sits in `G` as prefix-replacement units, and `u p_C u^-1 = p_(uC)`.
* For two tuples of pairwise disjoint cylinders, each with proper union, some `u` in `V` has
  `u iota_(A_i)(g) u^-1 = iota_(B_i)(g)` for every `i`.
* `u` can be chosen to fix prescribed disjoint cylinders pointwise while swapping two nonempty disjoint
  clopens of their complement.
* By conjugation invariance (Lemma 1.1.1), every `N`-value below depends only on the shape of the
  configuration.

## 2. The gap

**Theorem 2.1 (S, hence M).** Suppose `A_S` is nonempty.
1. `c_3 = min {N(D) : N in A_S}` is attained, and `0 < c_3 <= 2/3`.
2. Every Sylvester matrix rank function on `F_3[G]` satisfies `N(D eps_-) >= c_3 N(eps_-)`.
3. Every `N` in `A_S` has `N(Q_A) = 1/2` and `N(D_A) >= N(D_A Q_A) >= c_3/2` for every nonempty proper
   prefix `A`.
4. The same holds for `A_M`, with `c_3^M = min {N(D) : N in A_M} >= c_3`.

*Proof.*
1. **Compactness.** Sylvester matrix rank functions on a ring form a compact space. `N(X)` lies in
   `[0, min(n, m)]` for an `n x m` matrix, and every axiom is a closed condition in the product topology.
   * `N(eps_-) = 1` is closed, and `N -> N(D)` is continuous, so the minimum is attained.
   * It is positive by Lemma 1.4.
   * `N_12^3 = [x_12(1)]^3 - 1 = 0` in characteristic three, so `N(D) <= N(N_12) <= 2/3` by Lemma 1.1.4.
2. If `N(eps_-) > 0`, then `N^id_(eps_-)` lies in `A_S` by Lemma 1.2, because `eps_-` is a central idempotent.
   Its value at `D` is `N(D eps_-)/N(eps_-)`.
3. **Half split.**
   * Take `u` in `V` with `u A = X \ A`.
   * `[tau_(X\A)] eps_- = [z][tau_A] eps_- = -[tau_A] eps_-`, so `Q_(X\A) eps_- = 2(1 + [tau_A]) eps_- = (1 - Q_A) eps_-`.
   * By Lemma 1.1.5, `N(Q_A) = N(u Q_A u^-1) = N(Q_(X\A)) = N(1 - Q_A)`. Both equal `1/2` by Lemma 1.1.3.

   **Compression.**
   * `Q_A` commutes with `F_3[iota_A(G)]`, because `tau_A = iota_A(z)` is central in `iota_A(G)`.
   * So `N' = N^(iota_A)_(Q_A)` is a Sylvester rank function, and `F_3[iota_A](eps_-) = Q_A` gives
     `N'(eps_-) = N(Q_A Q_A)/N(Q_A) = 1`.
   * Then `N'(D) = N(D_A Q_A)/N(Q_A) >= c_3`.
4. `A_M` is closed. A limit of matricial functions is matricial by the finite-stage diagonal ultraproduct of
   Lemma 2.3 of the characteristic-two artifact, run over characteristic-three fields (`G` is countable). QED

**Remark 2.2 (what characteristic three does not need).**
* **What characteristic two needed:** the fixed-point-free quotient (a range idempotent), four-generation, and
  a displacement lemma built from annihilators.
* **What replaces them here:** `N(eps_-) = 1`, which already excludes the trivial limit. A limit of
  anti-central functions is anti-central, and the augmentation rank is not.
* **Consequence:** the gap is abstract, and its minimum is attained in both scopes.
* **Calibration:** Lemma 1.4 is the only place where "R has no rank function" enters. Over a coefficient ring
  that has a rank function, the honest models of `EL_3` have `D = 0`.

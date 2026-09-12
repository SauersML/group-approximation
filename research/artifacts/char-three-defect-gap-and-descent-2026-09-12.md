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

## 3. Descent

**Setting.**
* `N` lies in `A_S`.
* `A_1, ..., A_k, B` are pairwise disjoint nonempty proper cylinders with proper union.
* `C = X \ (A_1 ∪ ... ∪ A_k)`. It contains `B`, and `C \ B` is nonempty.
* `P_k = D_(A_1) ... D_(A_k)`, with commuting factors because the subgroups `iota_(A_i)(G)` commute.
* `f(k) = N(P_k)` with `f(0) = 1`, and `h_k = N(Q_B P_k)`.
* `R_s`, for `s` in `{±}^k`, are the joint sign idempotents of `[tau_(A_1)], ..., [tau_(A_k)]`, all commuting
  with `P_k`. Put `pi(s) = prod_i s_i` and `R_± = sum over pi(s) = ±1 of R_s`.

By Fact 1.5, all these values depend only on `k`.

**Theorem 3.1 (S).**
1. `f(k+1) <= (2/3) f(k)`, hence `f(k) <= (2/3)^k`. This holds for every Sylvester rank function on `F_3[G]`.
2. `f(k+1) >= N(D_B Q_B P_k) >= c_3 h_k`.
3. `N(Q_B R_s P_k) = N(R_s P_k)/2` whenever `pi(s) = +1`. So `h_k >= N(R_+ P_k)/2`.
4. If `h_k = 0`, then `f(k+1) = 0`. So `f(k+1) > 0` iff `h_k > 0`.

*Proof.*
1. `f(k+1) = N(D_B P_k)`. `N^B_12 = F_3[iota_B](N_12)` commutes with `P_k` and has cube `0`, so Lemma 1.1.4
   gives `N(D_B P_k) <= N(N^B_12 P_k) <= (2/3) N(P_k)`.
2. **First inequality.** `D_B Q_B P_k = Q_B D_B P_k`, so it is submultiplicativity.
   **Second inequality.** It is trivial if `h_k = 0`, so suppose `h_k > 0`.
   * `E = Q_B P_k` commutes with `F_3[iota_B(G)]`: `Q_B` because `tau_B = iota_B(z)` is central in
     `iota_B(G)`, and `P_k` because the cylinders are disjoint.
   * So `N' = N^(iota_B)_E` is a Sylvester rank function (Lemma 1.2).
   * It is anti-central, because `F_3[iota_B](eps_-) = Q_B` and `N(Q_B E) = N(E)`.
   * By Theorem 2.1.1, `N'(D) = N(D_B Q_B P_k)/h_k >= c_3`.
3. **Sign on the sector.** Put `Y = R_s P_k eps_-`. Then
   `[tau_C] Y = [z] prod_i [tau_(A_i)] Y = -pi(s) Y = -Y`. So `[tau_(C\B)] Y = [tau_C][tau_B] Y = -[tau_B] Y`,
   and `Q_(C\B) Y = (1 - Q_B) Y`.
   **Swap.** Take `u` in `V` that fixes every `A_i` pointwise and swaps `B` with `C \ B`. It commutes with
   `P_k`, `R_s` and `eps_-`, and `u Q_B u^-1 = Q_(C\B)`. By Lemma 1.1.1 and 1.1.5:
   `N(Q_B R_s P_k) = N(Q_(C\B) R_s P_k) = N((1 - Q_B) Y) = N((1 - Q_B) R_s P_k)`.
   **Halves.** Lemma 1.1.3 splits `N(R_s P_k)` into these two equal halves. Summing over sectors, again by
   Lemma 1.1.3, gives `h_k >= N(R_+ P_k)/2`.
4. Suppose `h_k = 0` and `f(k) > 0`.
   * By Fact 1.5, `h_k = 0` for every configuration of this shape, in particular for `(A_1, ..., A_k, Bw)`
     with `w` any nonempty proper prefix.
   * `N'' = N^(iota_B)_(P_k)` is a Sylvester rank function.
   * `1 - [tau_w] = 2 Q_w` and `F_3[iota_B](Q_w) = Q_(Bw)`, so `N''(1 - [tau_w]) = N(Q_(Bw) P_k)/f(k) = 0`.
   * So `tau_w` lies in `K_(N'')`, which is normal and not contained in `<z>`. Hence `K_(N'') = G`, and `N''` is
     the augmentation rank (Lemma 1.3).
   * Then `f(k+1) = N(D_(Bw') P_k) = f(k) N''(D_(w')) = 0`, because the augmentation of every `N_ab` is `0`.
   QED

**Corollary 3.2.** Suppose some `beta > 0` gives `N(R_+ P_k) >= beta f(k)` for every `k` and every `N` in
`A_S`. Then `(beta c_3/2) f(k) <= f(k+1) <= (2/3) f(k)`.

**Remark 3.3 (what is lost relative to characteristic two).**
* **The pullback is only half anti-central.** The pullback `N o F_3[iota_B]` of an anti-central `N` is not
  anti-central, since `iota_B(z) = tau_B`. Only its `Q_B`-part is. The `(1 - Q_B)`-part is a model of
  `PG = G/<z>` through `iota_B`, and no gap is known for it. Characteristic two has no such split.
* **Odd sectors.** On sectors with `pi(s) = -1`, `[tau_C]` acts by `+1`, so the complement's unit group acts
  through `PG` and the half split fails. There `h_k` can be smaller than `f(k)/2`.
* **Globality does not port.** In characteristic two it (Lemma 3.0 there) makes the complement act without
  fixed vectors. A characteristic-three version would need `iota_B(G)` finitely generated, with `G` generated
  by its compressors, as in the matricial `rank-ultraproduct-compressors-conserve-fixed-right-ideals`. It
  would still leave the `pi(s) = -1` sectors.
* **Near-minimal multiplicativity does not port.** Proposition 4.1 of the characteristic-two artifact needs
  the unrestricted lower bound `f(k+1) >= c_* f(k)`, and also kernel corners, which are annihilator ideals.
  Neither is available.

## 4. Scope of each characteristic-two step

"Yes" means the step holds as stated in that scope; "via" names the replacement.

| characteristic-two step | abstract, char 2 | matricial, char 3 | abstract, char 3 |
|---|---|---|---|
| Fact 1.1(a),(b): annihilators, modular lattice | no (needs a regular ring) | yes | no, and not needed |
| Fact 1.1(c): square zero bounds corner rank by 1/2 | yes, via Frobenius (Lemma 1.1.4) | yes, bound 2/3 | yes, bound 2/3 |
| Fact 1.1(d): images of annihilator ideals | no | yes | no |
| Lemma 2.1: fixed-point-free quotient | no (range idempotent) | yes, but unnecessary | via compression along `eps_-` |
| Lemma 2.2: displacement through annihilators | no | yes, needs finite generation | via `N(eps_-) = 1` |
| Lemma 2.3: compactness | yes | yes | yes, minimum attained |
| Theorem 2.4: gap | see below | Theorem 2.1 | Theorem 2.1 |
| Lemma 3.0: globality | no | not established for `G_3` | no |
| Theorem 3.1: upper bound | yes, via Lemma 1.1.4 | yes, 2/3 | yes, 2/3 |
| Theorem 3.1: lower bound | no (range corner) | sector-limited only | sector-limited, via Lemma 1.2 |
| Proposition 4.1: near-minimal multiplicativity | no (kernel corners) | no | no |

**Theorem 2.4 in abstract characteristic two.** Its lower bound holds over functions with full augmentation
row rank, `N([1 - g_1, ..., 1 - g_4]) = 1`. The proof is compactness plus
`leavitt-rank-functions-killing-two-root-defect-are-augmentation`: the augmentation rank gives that row rank
`0`. But passing from an arbitrary nontrivial function to one of full row rank needs the fixed ideal, and that
step does not port.

## 5. Where it stops, and the route to the No branch

**Minimizers exist.** `c_3` is attained in both scopes. So closing the No branch along this line needs one
operation that takes a minimizer to an anti-central function of strictly smaller defect, or any
contradiction at a minimizer.

**The literal port does not close.** Transcribing `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`
to characteristic three gives nothing, because its payoff runs through near-minimal multiplicativity
(Remark 3.3). What does port is Theorem 3.1.2 at `k = 1`: `N(D_B Q_B D_A) >= c_3 N(Q_B D_A)`.
* **On main.** That transcription is `ternary-disjoint-cylinder-defects-strictly-submultiplicative` (lane
  `w5-c3-submult`). Its payoff paragraph assumes the near-minimal port, which Remark 3.3 shows is unavailable
  in both scopes.
* **Its firewall.** `anti-central-sofic-data-cannot-force-defect-submultiplicativity` gives regular profiles
  with `rk(N_12) = 2/3`, meeting the bound of Lemma 1.1.4, `rk(D_A) = 5/9`, and exactly multiplicative disjoint
  defects. Check item 2 below against it first.

**Target** (`ternary-anti-central-disjoint-defects-have-a-strict-deficit`, OPEN). There is `theta < 1` such
that for every `N` in `A_S`, and every pair of disjoint nonempty proper cylinders `A`, `B` with proper union:
1. `N(D_A D_B) > 0`;
2. the compressed anti-central function `N'(X) = N(F_3[iota_B](X) Q_B D_A)/N(Q_B D_A)` has
   `N'(D) <= theta N(D)`.

**Route** (`ternary-rank-kill-via-anti-central-defect-deficit`).
1. Suppose `A_S` is nonempty, and take a minimizer `N_0` with `N_0(D) = c_3`.
2. Item 1 and Theorem 3.1.4 make `N_0(Q_B D_A) > 0`.
3. Theorem 3.1.2 gives `N_0'(D) >= c_3 = N_0(D)`, while item 2 gives `N_0'(D) <= theta N_0(D) < N_0(D)`.
4. So `A_S` is empty.
5. Any `N` with `N(1 - [z]) > 0` has `N(eps_-) = N(1 - [z]) > 0`, and would compress into `A_S` by
   Theorem 2.1.2. So every Sylvester rank function on `F_3[G]` kills `1 - [z]`. That is
   `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`.

**What the target asks.**
* **Independent factors.** In an independent tensor configuration the compressed function is a copy of the
  factor at `B`, so `theta = 1`. The target asks that compressing along a disjoint defect strictly lowers the
  defect, which independent factors never do.
* **So a proof must use the Leavitt relations.** The characteristic-two firewalls on halving data and on
  finite-subgroup data are the first things to re-check in characteristic three.
* **Positivity.** Item 1 is open in both scopes. By Theorem 3.1.4 its failure means that the complement of `A`
  acts centrally on the range of `D_A`: a disjoint two-root identity for the model.
* **Calibration.** Over coefficient rings that have rank functions, honest models have all defects `0`, so the
  question is vacuous there.

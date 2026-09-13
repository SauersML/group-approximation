# The right-child exchange group: parabolic splitting, an infinite dihedral root closure, and where the Borel firewall stops

Lane `w7-gamma-b`, 2026-09-12. **Everything here is OPEN**: it is proved on paper and held until `w4-vf-gate` re-derives
it.

Inputs:
* `research/artifacts/multiletter-split-borel-and-coefficient-firewalls-2026-09-12.md`: Theorem 3.5, Fact 4.1,
  Lemma 4.3 and Lemma 6.1.
* `leavitt-right-child-frames-generate-infinite-order-units`: items 2 and 4.
* `sofic-subgroups-carry-independent-cylinder-defects`, "Theorem S".
* `locally-finite-hnn-data-allow-independent-cylinder-defects`.
* w7-sylv-global: Corollary 3.5 and Section 4.2 of `sylvester-exact-globality-and-kernel-compression-2026-09-12.md`.

## 0. Summary

Write `Gamma_b = <iota_A(D_8), iota_(A1)(D_8), b>` with `b = iota_A(w_23) iota_(A1)(w_12)`.

1. **Section 1.** `b` written out, in operator form and as a matrix in a frame.
2. **Section 2.** Of the six `b`-conjugates of positive roots, exactly one increases lexicographically:
   `u_2 = 1 + S[A11]T[A101] = iota_A(E_32(t_1))`.
3. **Section 3 (splitting).** `Gamma_b = M ⋊ Gamma'`, where `M` is an elementary abelian 2-group and
   `Gamma' ≅ <x, y, u, beta> <= R^x` at the root. So `Gamma_b` is amenable if and only if `Gamma'` is.
4. **Section 4 (dihedral closure).**
   * `u_1 = iota_A(x_23(1))` and `u_2 = b iota_(A1)(x_23(1)) b^-1` generate `D_inf`.
   * So no locally finite subgroup normalized by `b` contains both `x_23` roots.
   * This proves Lemma 6.1 for every order, pointwise and b-twisted ones included. The b-twisted-order route to a
     theta = 1 model is dead.
   * With `b' = x_0` on `[A1]`, which is `b` without the exchange, everything lies in `U_< ⋊ <b'>`. So the infinite
     order comes from the exchange.
5. **Section 5 (Theorem S).** The hypothesis `Gamma_b` must meet is exactly soficity of `Gamma_b`, or equivalently of
   `Gamma_b × iota_B(D_8)`. Amenability of `Gamma'` would suffice. Neither is decided here.
6. **Section 6.** A theta < 1 derivation from these relations would be a proof that `Gamma_b` is not sofic. That
   agrees with w7-sylv-global Section 4.2. No such derivation was found.

## 1. `b` explicitly

Conventions follow the multiletter artifact, Section 1.
* `S[v]T[w]` is the prefix replacement `wy -> vy`, and products compose rightmost first.
* `R = L_(F_2)(1,2)` is simple, so it acts faithfully on `F_2^(X)`, `X = {0,1}^N`, through `delta_(wy) -> delta_(vy)`.

**Operator form.**
```
iota_A(w_23)    = S[A0]T[A0] + S[A10]T[A11] + S[A11]T[A10] + 1 - e_A
iota_(A1)(w_12) = S[A10]T[A110] + S[A110]T[A10] + S[A111]T[A111] + 1 - e_(A1)
b               = S[A0]T[A0] + S[A100]T[A10] + S[A11]T[A110] + S[A101]T[A111] + 1 - e_A
```
On points:
* `A0z -> A0z`;
* `A10z -> A110z -> A100z`;
* `A110z -> A10z -> A11z`;
* `A111z -> A111z -> A101z`;
* the identity off `[A]`.

This matches item 2 of `leavitt-right-child-frames-generate-infinite-order-units`.

**Matrix form.** In the frame `(A10, A11)` of the corner `e_(A1) R e_(A1)`, where an entry `a` at `(p,q)` stands for
`S[p] a T[q]`:
```
b|[A1]    = [[s_0, s_1 t_1], [0, t_0]]
b^-1|[A1] = [[t_0, 0], [s_1 t_1, s_0]]
```
* **Entries.** For example, the `(A10,A11)` entry gives `S[A10] s_1 t_1 T[A11] = S[A101]T[A111]`, and the `(A11,A11)`
  entry gives `S[A11]T[A110]`.
* **Inverse check.** The product is `[[s_0t_0 + s_1t_1s_1t_1, s_1t_1s_0], [t_0s_1t_1, t_0s_0]] = I`, using
  `t_i s_j = delta_ij`.
* **Contraction.** `b e_(A10) b^-1 = e_(A100) < e_(A10)` and `b S[A10] = S[A10] s_0`. So `b` has infinite order and
  strictly contracts a frame projection, which is the situation of multiletter Lemma 4.3.
* **Fixed points on `[A1]`.** `b` fixes `A10 0^inf`, while `b^-1`, which sends `A11z -> A110z`, fixes `A11 0^inf`.

**`b` without the exchange.** Let `b' = S[A100]T[A10] + S[A101]T[A110] + S[A11]T[A111] + 1 - e_(A1)`, the generator
`x_0` of `F` on `[A1]`. Then `b = (A101 <-> A11) ∘ b'`, and `b'` lies in `F`.

## 2. `b`-conjugates of the positive roots

For `N = S[v]T[w]`, the conjugate `b N b^-1` is the operator `b(wy) -> b(vy)`. Split `y` by its first letter where `b`
is piecewise.

| positive root | `b N b^-1` | lex direction |
|---|---|---|
| `S[A0]T[A10]` | `S[A0]T[A100]` | decreasing |
| `S[A0]T[A11]` | `S[A00]T[A11] + S[A01]T[A101]` | decreasing |
| `S[A10]T[A11]` | `S[A1000]T[A11] + S[A1001]T[A101]` | decreasing |
| `S[A10]T[A110]` | `S[A100]T[A11]` | decreasing |
| `S[A10]T[A111]` | `S[A100]T[A101]` | decreasing |
| `S[A110]T[A111]` | `S[A11]T[A101]` | **increasing** |

* **The increasing one.** `S[A11]T[A101] = S[A11] t_1 T[A10]` is the entry `t_1` at `(A11,A10)`, that is
  `iota_A(E_32(t_1))`.
* **Under `b'`.** The last three rows become `S[A100]T[A101]`, `S[A100]T[A11]` and `S[A101]T[A11]`, and the first
  three stay decreasing (for example `S[A10]T[A11] -> S[A1000]T[A101] + S[A1001]T[A11]`). All six are decreasing.

## 3. Parabolic splitting

Decompose `1 = e_(A0) + e_(A1) + (1 - e_A)`. Let `P_A` be the set of units
`g = (m, h) := (1 - e_A) + e_(A0) + m + h`, with `m` in `e_(A0) R e_(A1)` and `h` in `(e_(A1) R e_(A1))^x`.

**The product.** `(m,h)(m',h') = (m' + m h', h h')`. The terms `h m'` and `m e_(A0)` vanish because the idempotents
are orthogonal.
* So `(m,h) -> h` is a homomorphism.
* Its kernel `{(m, 1)}` is abelian of exponent 2.
* Conjugation acts by `(0,h)^-1 (m,1) (0,h) = (m h, 1)`.

**The generators lie in `P_A`.**
* `iota_A(x_12(1)) = (S[A0]T[A10], 1)` and `iota_A(x_13(1)) = (S[A0]T[A11], 1)`.
* `iota_A(x_23(1))`, `iota_(A1)(D_8)` and `b` all have `m = 0`.

**Proposition 3.1.** Let `Gamma'_A = <iota_A(x_23(1)), iota_(A1)(D_8), b>`. Then `Gamma_b = M ⋊ Gamma'_A`, where
```
M = F_2-span { (S[A0]T[A10] h, 1), (S[A0]T[A11] h, 1) : h in Gamma'_A }.
```
Every element of `Gamma_b` is a unique pair `(m, h)` with `m` in `M` and `h` in `Gamma'_A`.

*Proof.*
1. Projection onto `h` maps `Gamma_b` onto `Gamma'_A`, and the inclusion `Gamma'_A <= Gamma_b` splits it.
2. The kernel is the normal closure of the two `m`-generators.
3. `M` is abelian, so conjugates by `Gamma'_A` suffice, and those are the right translates above. ∎

**Corollary 3.2.**
* `Gamma_b` is amenable if and only if `Gamma'_A` is.
* Soficity of `Gamma'_A` is necessary for soficity of `Gamma_b`. Sufficiency is not claimed, because abelian-by-sofic
  groups are not known to be sofic in general.

**Stripping the prefix.** The map `r -> T[A1] r S[A1]` identifies `(e_(A1) R e_(A1))^x` with `R^x`, and it sends
`Gamma'_A` onto `Gamma' = <x, y, u, beta>`:
```
x    = 1 + S[0]T[10]                     (a root of D_8 at the root frame)
y    = 1 + S[10]T[11]                    (a root of D_8 at the root frame)
u    = 1 + S[0]T[1]                      (image of iota_A(x_23(1)))
beta = S[00]T[0] + S[01]T[11] + S[1]T[10]   (image of b; in V \ F)
```
* **`u`.** In the root frame `(0,10,11)`, `u = 1 + E_12(s_0) + E_13(s_1)`. That is a coefficient root, not an element
  of `D_8`.
* **Frame `(0,1)` at the root.** There `u = [[1,1],[0,1]]`, `x = [[1,t_0],[0,1]]`, `y = diag(1, 1 + s_0 t_1)` and
  `beta = [[s_0, s_1t_1],[0,t_0]]`.
* **Coefficients.** All entries and inverse entries lie in the subalgebra `S_b` generated by `s_0, t_0, t_1`, since
  `s_1 t_1 = 1 - s_0 t_0`. So `Gamma' <= Phi_(0,1)(GL_2(S_b))`.
* **Two charts.** `S_b` contains the Jacobson algebra `<s_0, t_0>`, which is not RFD. So Fact 4.1, the one-chart RF
  firewall, does not apply.
* **Not `EL_3(J)` data.** `S_b` also contains `t_1`, with `t_1 s_0 = 0`. So these are not the `EL_3(J)` data of
  w7-el3j-presentation (`jacobson-el3-presentation-and-amalgam-kernel-2026-09-12.md`) or
  `binary-jacobson-el3-is-sofic`, and nothing here duplicates them.

## 4. The dihedral closure

**Proposition 4.1.** `u_1 = iota_A(x_23(1)) = 1 + S[A10]T[A11]` and `u_2 = b iota_(A1)(x_23(1)) b^-1 = 1 + S[A11]T[A101]`
are involutions whose product has infinite order. So `<u_1, u_2> ≅ D_inf <= Gamma_b`.

*Proof.*
1. **Involutions.** `N_1 = S[A10]T[A11]` and `N_2 = S[A11]T[A101]` square to zero, because `T[A11]S[A10] = 0` and
   `T[A101]S[A11] = 0`.
2. **Frame form.** In the frame `(A10, A11)`, `u_1 = [[1,1],[0,1]]` and `u_2 = [[1,0],[t_1,1]]`, so
   `G = u_1 u_2 = [[1+t_1, 1],[t_1, 1]]`.
3. **Grading.** `R` is `Z`-graded with `deg s_i = 1` and `deg t_i = -1`. The frame words have equal length, so the
   frame map preserves the degree of each entry. Write `G = G_0 + G_-1` with `G_-1 = [[t_1, 0],[t_1, 0]]`.
4. **Conclusion.** The degree `-n` part of `G^n` is `G_-1^n = [[t_1^n, 0],[t_1^n, 0]]`. It is nonzero because
   `t_1^n s_1^n = 1`. So `(u_1u_2)^n != 1` for every `n >= 1`. ∎

**Corollary 4.2 (every order).**
* **Statement.** Let `U <= R^x` be normalized by `b` and contain `iota_A(x_23(1))` and `iota_(A1)(x_23(1))`. Then `U`
  contains `D_inf`, so `U` is not locally finite.
* **Consequence for orders.** No order has all three of these properties:
  1. its monotone unipotents form a locally finite group;
  2. `b` normalizes that group;
  3. the two `x_23` roots, at `A` and at `A1`, are monotone.

  This covers setwise, pointwise tail-by-tail, piecewise and `b`-twisted orders. So `Gamma_b` does not lie in any
  `U ⋊ P` with `U` locally finite, `U` containing those two roots, and `b` in `P`.
* **Relation to Lemma 6.1.** This contains multiletter Lemma 6.1. That lemma uses all positive roots and a setwise
  order, and its contradiction step is stated for cylinders as intervals. Corollary 4.2 needs only the two `x_23` roots
  and no order at all.
* **Normal subgroups.** Every normal subgroup of `Gamma_b` containing both `x_23` roots is not locally finite.
* **What remains.** A locally finite normal subgroup with an amenable quotient would make `Gamma_b` amenable. That
  question is `Gamma'` (Corollary 3.2).

**Corollary 4.3 (the exchange is the escape).**
* **Without the exchange.** With `b'` from Section 1, `b' iota_(A1)(x_23(1)) b'^-1 = 1 + S[A101]T[A11]`, which is
  decreasing.
  * It commutes with `u_1`, because `T[A11]S[A101] = 0` and `T[A11]S[A10] = 0`, so together they generate a Klein
    four-group.
  * All conjugates in the Section 2 table are decreasing. So `<iota_A(D_8), iota_(A1)(D_8), b'> <= U_< ⋊ <b'>`,
    which is amenable (`lex-decreasing-units-with-order-preserving-letters-are-amenable`, OPEN).
* **The exchange.** Composing with `(A101 <-> A11)` turns the single row `S[A110]T[A111]` increasing, and that alone
  produces `D_inf`.
* **Firewall check (Task 3).** An identity that uses `<u_1, u_2>` uses the cross-frame exchange of `b`, not only the
  behaviour of `F`.

**Remark 4.4.** `D_inf` alone decides nothing.
* `<u_1, u_2>` is amenable.
* Its entries `1` and `t_1` come from one chart, so it lies in the one-chart class of multiletter Fact 4.1.
* A deficit must use `D_inf` together with `x`, `y` at both levels and `beta`, whose entries `s_0, t_0, t_1` use both
  charts.

## 5. Theorem S: the exact hypothesis and whether `Gamma_b` meets it

**What Theorem S requires.**
* `H <= R^x` is sofic.
* `iota_(A_i)(D_8) <= H` for pairwise disjoint nonempty proper cylinders `A_i`.
* For fixed-point-freeness, `H` contains an element of infinite order.

**The frames in `Gamma_b` are nested.** `A` contains `A1`, so the frames inside `Gamma_b` sit at nested cylinders.
Theorem S says nothing about `rk(D_A D_(A1))`.

**The disjoint pair.** Take `B` disjoint from `[A]`, with `[A] ∪ [B]` proper.
* Elements of `Gamma_b` are `1 - e_A` plus the corner at `A`, and elements of `iota_B(D_8)` are `1 - e_B` plus the
  corner at `B`.
* So they commute and meet trivially, and `H_B = <Gamma_b, iota_B(D_8)> ≅ Gamma_b × D_8`.
* `H_B` is sofic if and only if `Gamma_b` is, and `b` supplies the infinite-order element.

**Verdict.**
* `Gamma_b` meets the hypothesis if and only if `Gamma_b` is sofic.
* By Corollary 3.2, amenability of `Gamma' = <x, y, u, beta>` suffices. This is not decided here.
* If `Gamma_b` is sofic, then `H_B` has a fixed-point-free model with `rk(D_A D_B) = 9/64`, and relations holding in
  `H_B` force no theta < 1.

**The other Task 2 options.**
* **Induced model.** An induced model from a finite-index subgroup adds nothing: amenability and soficity are invariant
  under finite index.
* **HNN over `K`.** Let `K` be the finite group of positive roots at `A` and `A1` (right-child item 4), and let
  `Lambda(K)` be the HNN extension with one letter `t` for `b`. It does not model `Gamma_b`:
  * `x = iota_A(x_12(1))` gives `[b x b^-1, x] = 1` in `Gamma_b`, because `T[A100]S[A0] = 0` and `T[A10]S[A0] = 0`.
  * In `Lambda(K)` the word `t x t^-1 x t x^-1 t^-1 x^-1` is Britton-reduced, because neither conjugate of `x` lies in
    `K`:
    - `b x b^-1 = 1 + S[A0]T[A100]`;
    - `b^-1 x b = 1 + S[A00]T[A10] + S[A01]T[A111]`.
  * **Why neither conjugate is in `K`.** On `delta_(A1001^inf)`:
    - `S[A0]T[A100]` gives `delta_(A01^inf)`, while every element of the span of `K`'s monomials gives a multiple of
      `delta_(A001^inf)`;
    - similarly `S[A00]T[A10]` acts on `delta_(A101^inf)` differently from `S[A0]T[A10]`.
* **Larger `L`.** A larger locally finite `L` may absorb such relations, since the pinch needs `b^-1 x b` in `L`. By
  Corollary 4.2, `L` cannot contain both `u_1` and `u_2`. Since `Z/2 * Z/2 ≅ D_inf` already, this is no contradiction.
  Whether some `L` realizes every relation of `Gamma_b` is open.

## 6. The minimizer (Task 4) and the form of a certificate (Task 3)

* **At a minimizer.**
  * By w7-sylv-global Corollary 3.5 and Section 4.2, a minimizer `psi_*` has the independent-profile numbers.
  * On `H_B`, those are the numbers Theorem S realizes when `H_B` is sofic. So at a minimizer, relations of `H_B`
    produce no contradiction unless `Gamma_b` is not sofic.
* **Agreement with w7-sylv-global.** Section 4.2 says a relation-only proof needs a nonsofic subgroup containing both
  frames. `H_B` is such a candidate exactly when `Gamma_b` is nonsofic.
* **What a derivation would prove.** Suppose a theta < 1 derivation uses only relations of `H_B`, rank calculus,
  nontriviality and fixed-point-freeness. By the contrapositive of Theorem S, it proves that `Gamma_b` is not sofic,
  and so that `Gamma'` is not amenable. The first model premise it breaks is soficity of `Gamma_b`.
  * Per the RULES NOTE (`w3-strategist-gate`), such a derivation would be the certificate for the gate itself.
* **Conditions any such derivation must meet.**
  1. It must use the exchange (Corollary 4.3). Otherwise it holds in `U_< ⋊ F` and would prove
     `thompson-f-is-not-amenable`.
  2. It must use more than `<u_1, u_2>` or one-chart subgroups (Remark 4.4).
  3. It must multiply conjugating units, or use a non-locally-finite subgroup, beyond the HNN firewall. `D_inf` meets
     the second condition, but by itself it carries no deficit.
* **Result.** No theta < 1 identity was found.

## 7. Where it stopped

**Proved on paper (OPEN until w4-vf-gate).**
* The formulas of Sections 1–2.
* Proposition 3.1 and Corollary 3.2.
* Proposition 4.1 and Corollaries 4.2–4.3.
* The hypothesis verdict of Section 5 and the certificate form of Section 6.

**Refuted as routes.**
* A `b`-twisted, pointwise or piecewise Borel order (Corollary 4.2).
* An induced model from a finite-index subgroup.
* The HNN firewall over `K` alone.

**Open.**
* Amenability, free subgroups, LEF and soficity of `Gamma' = <x, y, u, beta>`.
* A normal form for `Gamma'`. Relative to `Gamma'`, `Gamma_b = {(m,h)}` has the unique form of Proposition 3.1.
* A theta < 1 identity.

**The one next lead.** Decide whether `Gamma'` is amenable.
* **Free subgroup.** Try ping-pong of `beta`, which contracts `[0] -> [00]` with attractor `0^inf` and repeller
  `10^inf`, against `u_1u_2` on `F_2^(X)`.
* **Amenability.** Try an invariant mean on the tail class of the attractor.
* **What each outcome gives.** If `Gamma'` is amenable, `Gamma_b` has theta = 1 by Theorem S. If `Gamma'` contains a
  free subgroup, `Gamma_b` stays a live candidate for the certificate.

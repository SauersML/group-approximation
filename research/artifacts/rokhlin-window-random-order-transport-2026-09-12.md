# Rokhlin window transport under a random order: identity, domination normal form, codeword Følner count

Lane `w7-inf-uniform`, 2026-09-12.

**Target.** A lower bound on the window value `Phi` of `bernoulli-rokhlin-deficit-has-a-finitary-witness` that is uniform in the read degree `m`. This is the Rokhlin counterpart of `injective-ca-random-order-transport-is-dominated`. On a self-copy host any uniform `c > 0` upgrades to `log q` (`self-copy-host-rokhlin-deficits-need-unbounded-windows`).

All work was done by hand; nothing was computed.

**Outcome.** No uniform bound was found. The following hold on every countable group:

1. an exact random-order transport identity for `I(x(1); y_F)` (Theorem 1);
2. maximality is equivalent to domination of that transport, and `C`-domination gives `Phi >= log q / C` (Corollary 2);
3. domination holds on reading sunflowers (Proposition 3) and for affine codes on every incidence pattern (Proposition 4); a noncancellative star has `Phi -> 0` (Example 5);
4. `Phi >= log q / lambda(F)` with `lambda(F) = inf_S |SF|/|S|`, so `Phi >= log q` whenever `<F F^-1>` is amenable (Proposition 6);
5. through Seward's upper bound, maximality is equivalent to a lower bound on the random-past entropy of every generating partition, and copy codes have random-past entropy exactly `k log q` (Section 6).

**Where it stops.** Every proved case of domination, CA or Rokhlin, ends with a count over a finite index set that is closed under the codewords, with ratio `1`. That step, and nothing else, is specific to finite models (Section 7).

## 1. Setting

`G` is countable, `|A| = q >= 2`, `k >= 1`, and `x = (x(g))_(g in G)` is iid uniform on `A^k`.

A configuration `(k, E, F, psi)` has finite sets `E, F` and a map `psi` from `(A^k)^E` to a finite set. For every `g in G` put `y_g = psi((x(g e))_(e in E))` and `y_S = (y_s)_(s in S)`. Then

    Phi = (1/k) [ H(y_1) + H(x(1) | y_F) ],     H(x(1) | y_F) = k log q - I(x(1); y_F),

and `rho_q(G) = inf Phi` (Theorem 3 of `research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md`).

* `F_1 = F ∩ E^-1` is the set of codewords that read site `1`, and `m = |F_1|`.
* The codeword `e^-1` reads site `1` at position `e`, so distinct readers read site `1` at distinct positions. This is right cancellation.
* `U = (U_g)` is iid uniform on `[0,1]`, independent of `x`, and `past(g) = {h : U_h < U_g}`.
* Conditioning on a random index set includes `U`: `I(X; Y | y_(S(U)), U) = E_u I(X; Y | y_(S(u)))`.
* The translation `(T_g x)(h) = x(g h)`, `(T_g U)(h) = U(g h)` preserves the law of `(x, U)`. It satisfies `y_h(T_g x) = y_(g h)(x)` and `past_(T_g U)(h) = g^-1 past_U(g h)`.

## 2. The transport identity

**Theorem 1.** For every configuration,

    I( x(1) ; y_F ) = sum_(f in F) I( x(f^-1) ; y_1 | y_(f^-1 F ∩ past(1)), U ).

*Proof.* `U` is independent of `x`, so `I(x(1); y_F) = I(x(1); y_F | U)`. For fixed labels `u`, all distinct, list `F` in increasing order and apply the chain rule:

    I(x(1); y_F | U = u) = sum_(f in F) I( x(1) ; y_f | y_(F ∩ past(f)), U = u ).

Integrate over `u`. The `f`-term is a functional of the law of `(x, U)`. Evaluate it at `T_(f^-1)(x, U)`, which has the same law:

* `x(1)` becomes `x(f^-1)`;
* `y_f` becomes `y_1`;
* the codewords `y_h`, `h in F`, `U_h < U_f`, become `y_(f^-1 h)` with `U_(f^-1 h) < U_1`, that is `y_(f^-1 F ∩ past(1))`;
* conditioning on `T_(f^-1) U` is the same as conditioning on `U`. QED

The input side is decoding of site `1`. The output side is what the single output `y_1` sends to the input sites `f^-1`, each term conditioned on the translated past codewords. The proof uses no finite model and no amenability.

Unlike the CA identity (`injective-ca-random-order-transport-identity`), the left side is not a constant: it is `k log q - H(x(1) | y_F)`.

*Check on `Z`.* Take `E = {0, 1}`, `psi` the copy map, and `F = {-1, 0}`. The left side is `1` bit. Each of the two right-side terms is `1` exactly when the other reader is later in the order, so each contributes `1/2`.

## 3. Domination normal form

**Corollary 2.** Fix `G` and `q`.

1. `rho_q(G) = log q` if and only if every configuration over `G` satisfies

       sum_(f in F) I( x(f^-1) ; y_1 | y_(f^-1 F ∩ past(1)), U ) <= H(y_1).        (D)

2. If every configuration satisfies the sum `<= C H(y_1)` for one `C >= 1`, then `rho_q(G) >= log q / C`.

*Proof.* (1) `Phi >= log q` is `I(x(1); y_F) <= H(y_1)`. Apply Theorem 1 and Theorem 3 of the route artifact.

(2) Put `H = H(y_1)` and `I = I(x(1); y_F) <= min{k log q, C H}`, so `k Phi = H + k log q - I`.
* If `C H >= k log q`, then `k Phi >= H >= k log q / C`.
* Otherwise `k Phi >= k log q - (C - 1) H > k log q - (C - 1) k log q / C = k log q / C`. QED

**Self-copy hosts.** On a host with `h_sup in {0, infinity}`, such as the binary Leavitt unit group or Thompson's `V`, part (2) with any `C` gives `h_sup > 0`, so INF holds on that host.

**A witness overshoots by `C`.** Let `Phi <= log q / C` and `r = H(x(1) | y_F)`. Then `H + r <= k log q / C`, so `I = k log q - r >= k log q (1 - 1/C) + H >= C H`, using `k log q >= C H`. So the transport sum exceeds `H(y_1)` by the factor `C`.

**Per-term bounds.** Each term of (D) is at most `H(y_1)`, so the sum is at most `|F| H(y_1)`.

Terms of non-reading codewords need not vanish. On `Z/5` take `E = {0,1,2}` and `psi` the parity of three bits:
* the circulant `1 + s + s^2` is invertible modulo `s^5 - 1` over `F_2`, with inverse `s + s^2 + s^4`;
* so `x(0) = y_1 + y_2 + y_4` is the unique representation of `x(0)`, and it uses the non-readers `1` and `2`;
* in the order `4 < 1 < 2`, the chain-rule term of the non-reader `2` is the whole bit.

The read-degree bound `Phi >= log q / m` (`bernoulli-witness-information-is-bounded-by-code-reads`) is the chain rule along the order that lists the non-readers of site `1` first. There their terms vanish, because they do not depend on `x(1)`. That order is defined relative to one site, is not translation-invariant, and does not transport.

## 4. Where domination holds on every pattern, and a star that breaks it

`Phi` depends only on the incidence pattern `(f, e) -> f e` on `F x E` together with the site `1`. Propositions 3 and 4 use no group structure beyond right cancellation.

**Proposition 3 (reading sunflowers).** Suppose every codeword of `F` reads site `1`, and the windows `f E`, `f in F`, pairwise meet only in `{1}`. Then `I(x(1); y_F) <= H(y_1)` and `Phi >= log q`.

*Proof.*
* Given `x(1)`, the `y_f` read disjoint sets of other coordinates. So they are conditionally independent, and `I(x(1); y_F) <= sum_f I(x(1); y_f)`.
* By translation `I(x(1); y_f) = I(x(f^-1); y_1)`, and the `f^-1` are distinct elements of `E`.
* For independent inputs `I(x(e); y_1 | earlier inputs) >= I(x(e); y_1)`. So `sum_(e in E) I(x(e); y_1) <= I(x|_E; y_1) = H(y_1)`. QED

So a witness needs codewords outside `F_1` or overlapping windows. Removing codewords never helps a lower bound, because `H(x(1) | y_F) <= H(x(1) | y_(F_1))`.

**Proposition 4 (affine codes, every pattern).** Let `A = F_q` be a field and `psi` affine over it. Then `I(x(1); y_F) <= H(y_1)` on every incidence pattern.

*Proof.* A translation of `psi` changes no entropy, so assume `psi` is linear. Let `L` be the linear map `x|_(FE ∪ {1}) -> y_F`.
* Given `y_F`, the input is uniform on a coset of `ker L`. So `I(x(1); y_F) = (dim V) log q`, where `V` is the space of functionals `phi` on `A^k` for which `phi ∘ pr_1` vanishes on `ker L`.
* Each such `phi ∘ pr_1` factors as `Lambda ∘ L` with `Lambda` linear.
* Evaluate on a constant input `c`. Every codeword outputs `Psi c`, where `Psi = psi ∘ diag : A^k -> A^r`. So `phi = lambda ∘ Psi` for a linear `lambda`.
* So `dim V <= rank Psi <= rank psi`, and `H(y_1) = (rank psi) log q`. QED

This extends Remark 3.2 of the route artifact from `k = 1` to every `k` and every pattern. It is the finitary form of the constants argument in `homomorphic-codes-cannot-compress-bernoulli-shifts`.

**Example 5 (a noncancellative star).** Take `q = 2` and `k = 2^t`, a center site `s`, and `M` petals. Petal `i` reads `s` at position `e_0` and a fresh site `a_i` at position `e_1`. Put

    psi(u, v) = ( j(v), u_(j(v)) ),

where `j(v) in [k]` is given by the first `t` bits of `v`.
* `H(psi) = t + 1` bits.
* `H(x(s) | y_F) = k (1 - 1/k)^M` bits, the expected number of unrevealed coordinates.
* With `M = ⌈2 k ln k⌉` the residual is at most `1/k`, so

      Phi <= ( log_2 k + 1 + 1/k ) / k  bits  -> 0 .

Every petal reads the center at the same position. So the pattern violates right cancellation and occurs in no group. Proposition 3 is the same sunflower with distinct positions, and there `Phi >= log q`. So a uniform bound must use cancellation.

On abstract patterns the read-degree bound is attained up to a polylogarithmic factor: here `m = M` and `Phi ~ log_2 k / k`.

## 5. The codeword Følner count

**Proposition 6.** For every configuration, with `lambda(F) = inf |S F| / |S|` over nonempty finite `S ⊂ G`,

    k log q <= lambda(F) H(y_1) + H(x(1) | y_F),     so   Phi >= log q / lambda(F).

Moreover `lambda(F) = 1` exactly when `<F F^-1>` is amenable, and then `Phi >= log q`.

*Proof.* Fix `S` and put `r = H(x(1) | y_F)`. By subadditivity and translation,

    |S| k log q = H(x|_S) <= H(y_(SF)) + sum_(s in S) H(x(s) | y_(sF)) <= |SF| H(y_1) + |S| r.

Divide by `|S|` and take the infimum. Since `lambda >= 1`, `lambda H + r <= lambda (H + r)`, which gives the bound on `Phi`.

For the last part fix `f_0 in F` and put `K = F f_0^-1`.
* If `|SF| <= (1 + eps)|S|`, then `|S f f_0^-1 \ S| <= eps |S|` for each `f in F`.
* Right multiplication by `<K>` preserves the left cosets of `<K>`. So some `S ∩ g<K>` is `|K| eps`-invariant, and `g^-1 (S ∩ g<K>)` is a right Følner set in `<K>`.
* Conversely, a right Følner set `S` of `<K>` has `|SF| = |SK| <= (1 + |K| eps)|S|`.
* Finally `<K> = <F F^-1>`, since `f f'^-1 = (f f_0^-1)(f' f_0^-1)^-1`. QED

With the read-degree bound, `Phi >= log q / min{m, lambda(F)}`. Proposition 6 is the Rokhlin form of the CA count `|F| log |A| <= |FN| H(y(e))`.

## 6. Random-past entropy

### 6.1 Normal form through Seward's upper bound

For a finite-entropy partition `alpha` of `(A^k)^G`, put `h^ro(alpha) = E_U H(alpha | alpha^(past(1)))`. Here `alpha^S` is the sigma-algebra generated by the translates `g.alpha`, `g in S`.

Alpeev (arXiv:1705.08559v1, p. 2) states:

> **Theorem 1.1** (Seward, [S16]). Let α be a generating partition for a p.m.p. action of the countable group G. Then the Rokhlin entropy of this action is bounded from above by the quantity E_ξ H(α|α^{L_ξ}).

Here `(ξ_g)` is iid uniform on the unit interval and `L_ξ = {g : ξ_g < ξ_e}`. Replacing `L_ξ` by `L_ξ^-1` does not change its law, so the translation convention does not matter.

**Proposition 7.** `h^Rok((A^k)^G) = inf h^ro(alpha)` over generating partitions `alpha` of `(A^k)^G`. So `rho_q(G) = log q` if and only if every generating partition of every `(A^k)^G` has `h^ro(alpha) >= k log q`.

*Proof.* Bernoulli shifts over infinite groups are ergodic, so `h^Rok = inf H(alpha)` over generating `alpha`. For generating `alpha`, Seward gives `h^Rok <= h^ro(alpha) <= H(alpha)`. QED

So attacking maximality through random-past entropy loses nothing, and the sufficient direction is trivial.

Alpeev (p. 2) notes that Rokhlin entropy bounds sofic entropy from above: "In fact, this provides essentially the only way to get a lower bound for the Rokhlin entropy." His random-ordering lower bound (Theorem 1.3, p. 4) concerns the sofic entropy `h(μ)` of a unique Gibbs measure. It is proved in his Section 4 "using the random ordering argument from [BCKL13]". That section was not read here.

### 6.2 Copy codes

**Example 8.** Let `E` be finite and nonempty, and `alpha = x|_E`. Then `H(alpha) = |E| k log q`, while `h^ro(alpha) = k log q` on every group.

*Proof.* `alpha^(past(1))` is generated by `x|_(past(1) E)`, so `h^ro = E |E \ past(1) E| · k log q`.
* A site `h` lies in `g E \ past(g) E` exactly when `g` is the `U`-least element of the finite set `h E^-1`. So each site is new at exactly one codeword.
* The mass transport `m(g, h) = 1{g is U-least in h E^-1}` is diagonally invariant.
* So `E |E \ past(1) E| = E sum_h m(1, h) = E sum_g m(g, 1) = 1`. QED

The expanded partition `gamma = join_(s in S) s.beta` of Proposition 4 of the route artifact is a copy code. Over a nonamenable group its window entropy is at least `(1 + c) log q`, but its random-past entropy is exactly `log q`. The random past removes exactly the redundancy that window entropy counts.

### 6.3 Where the averaging stops

Let `y` come from a configuration with residual `r`. Fix a finite `S`, put `T = SF`, and fix a finite `W`. Put `delta_W = H(y_1 | y_(W ∩ past(1)), U)`; as `W` increases it decreases to `h^ro(y_1)`, by martingale convergence. Let `T° = {g in T : g W ⊆ T}`.

The decoding step of Proposition 6, the chain rule along the order, and translation give

    |S| (k log q - r) <= H(y_T) = sum_(g in T) H(y_g | y_(T ∩ past(g)), U) <= |T°| delta_W + |T \ T°| H(y_1).   (6.3)

Both model-free decompositions of `H(y_T)` bound it from below:
* by `|S|(k log q - r)`, which is decoding;
* by `|T| h^ro`, since conditioning on the whole past can only lower entropy. This one points in the direction of Seward's upper bound.

An upper bound on `H(y_T)` in terms of `h^ro` needs `|T \ T°| = o(|S|)` and `|T| = (1 + o(1))|S|`, that is, Følner sets.
* Over amenable `G`, (6.3) gives `h^ro(y_1) >= k log q - r`.
* Over a nonamenable group the boundary term is a fixed fraction of `|S| H(y_1)`. Since `delta_W <= H(y_1)`, (6.3) then gives nothing beyond Proposition 6.

There is no infinite form of the chain rule:
* The order that iid labels induce on a countably infinite set is almost surely dense and has no endpoints. So no enumeration of `G` along it exists, and every use of the chain rule passes through a finite `T`.
* Mass transport moves only invariant per-site quantities, and `H(y_g | y_(T ∩ past(g)), U)` depends on `T`.
* The one exact invariant decomposition is Theorem 1, over the finite set `F`, and it is equivalent to the goal.

## 7. Direction (c): the finite-model step

The amenable case of `injective-ca-random-order-transport-is-dominated` (Section 3.3 of `research/artifacts/random-order-decoder-transport-2026-09-12.md`) has four steps:

1. decoding, `H(x|_F) <= H(y|_(FN))`, which is injectivity;
2. subadditivity, `H(y|_(FN)) <= |FN| H(y(e))`;
3. translation invariance of the joint law;
4. a finite `F` with `|FN| / |F| -> 1`.

Steps 1 to 3 hold on every group, and Theorem 1 and the CA identity use only them and the chain rule.

Step 4 is the only step specific to finite models:
* Inside `G` it is Følner's criterion for right translates. It fails for a nonamenable decoder group: Remark 1.1 of `research/artifacts/three-point-decoder-transport-obstruction-2026-09-12.md` gives the ratio `1/2` for a free semigroup.
* In a sofic model the index set is the finite vertex set `V` of an almost action. The codewords map `V` into itself, so the ratio is `1` up to the defect.

The Rokhlin count of Proposition 6 has the same four steps, with `S`, `SF` and `lambda(F)`. The other known cases fit the same pattern:
* the difference-subgroup filter counts in a finite subgroup, or imports maximality of the subgroup (`bernoulli-deficit-windows-need-a-non-maximal-difference-subgroup`);
* the sofic-radical localization counts on permutation models (`sofic-radical-localizes-bernoulli-deficit-witnesses`).

So every proved case of domination, CA or Rokhlin, is step 4 with ratio `1`.

## 8. Direction (b): the shape of a counterexample family

A configuration over a group with `Phi <= log q / C` needs all of the following:

1. read degree `m >= C` (`bernoulli-witness-information-is-bounded-by-code-reads`);
2. `lambda(F) >= C`, so `<F F^-1>` is nonamenable with right expansion ratio at least `C` (Proposition 6);
3. `<E E^-1>` infinite, nonsofic and non-maximal (`bernoulli-deficit-windows-need-a-non-maximal-difference-subgroup`);
4. `psi` not affine over any finite-field structure on `A` (Proposition 4);
5. a transport sum of at least `C H(y_1)` (Corollary 2), so `F` is not a reading sunflower (Proposition 3);
6. on a self-copy host, unbounded windows (`self-copy-host-rokhlin-deficits-need-unbounded-windows`).

No non-maximal group is known, so no such family can be exhibited, and this lane has none. The only family with `Phi -> 0` known here is Example 5, which violates right cancellation.

Cancellative abstract patterns were not tested. The end-fixing tree of Section 2.1 of the CA artifact is the natural place to look for a pattern-level deficit off groups.

## 9. Audit against Section 4 of the localization artifact

* The transport terms, `lambda(F)` and `h^ro` are functionals of one configuration or one partition, not invariants of the action. So the weak-equivalence barrier (`weak-invariants-give-no-bernoulli-rokhlin-lower-bound`) does not apply to them. Their infimum over generating partitions is `h^Rok` itself (Proposition 7).
* No ergodic decomposition and no co-induction is used.
* Nothing here is circular, and nothing here proves a new case of the claim. Theorem 1, Corollary 2 and Proposition 7 are reformulations; Propositions 3, 4 and 6 are filters.

## 10. Literature

**Read here:**
* Alpeev, arXiv:1705.08559v1, pp. 1-6: the abstract, Section 1, and the start of Section 2.
* Alpeev--Meyerovitch--Ryu, arXiv:1812.10833v2, pp. 1-3: the abstract, Section 1, and the start of Section 2. It treats amenable groups, and cites random orders in entropy theory for nonamenable groups only by reference.

Seward's theorem is quoted from Alpeev, not from [S16].

**Not read by this lane:** Gaboriau on ℓ²-Betti numbers, Seward on ergodic decomposition, and Koopman data. The landed audit covers them.

## 11. Status

* **Proved** here, pending review by `w4-vf-positive-b`:
  * Theorem 1 and Corollary 2;
  * Propositions 3, 4 and 6;
  * Proposition 7, given the quoted theorem;
  * Examples 5 and 8, and the `Z/5` calibration.
* **Open:** domination (D) on every group, and a bound on `Phi` uniform in `m` and `lambda(F)`.
* **Where it stops:** every known proof of domination is a ratio-`1` count on a finite index set closed under the codewords (Section 7). A proof without finite models needs a new inequality that:
  * uses the conditionings in (D) jointly;
  * uses right cancellation (Example 5);
  * survives a nonamenable `<F F^-1>`.

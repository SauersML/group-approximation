# Metric ultraproduct surjunctivity is Gottschalk's conjecture up to bounded-width profinite closure

Lane `w4-metric-ultra`, 2026-09-12. This artifact supports:
- the open claim `strict-reverse-words-lie-in-bounded-width-profinite-closures`, and the two routes that join it to
  `metric-ultraproducts-of-finite-groups-are-surjunctive`;
- `weak-sofic-reflection-kernel-is-bounded-width-closure`;
- `surjunctivity-of-a-local-class-is-reflection-kernel-membership`.

It continues `weak-sofic-hamming-transport-is-soficity-2026-09-12.md` ([WH]), and uses the tables, clauses and
Theorem 1 of `gottschalk-rectangle-clauses-and-recognition-2026-09-12.md` ([RC]).

## 0. Conventions

**Lengths and ultraproducts.**
- A *length* on a group `K` is a function `l: K -> [0, infinity)` with `l(1) = 0`, `l(g^-1) = l(g)`,
  `l(gh) <= l(g) + l(h)` and `l(k g k^-1) = l(g)`.
- `Q = prod_omega H_i / N_omega` is a metric ultraproduct of finite groups with lengths, as in [WH] Section 4.

**Strict data.** A strict datum `D = (S, M, A, mu, nu, T_f, T_r)` is as in [RC] Section 1.
- `F = F(D)` is the free group on the symbols `x_a`, for `a` in `S ⊔ M` other than the two labels `1`. Put
  `x_1 = 1` for both labels.
- The *forward relators* are
  `R_f(D) = { x_s x_m x_m'^-1 x_s'^-1 : (s,m) T_f (s',m') }`.
- The *reverse words* are
  `W_r(D) = { x_m x_s x_s'^-1 x_m'^-1 : (m,s) and (m',s') not T_r-related }`.
- Both sets are finite, and `W_r(D)` is nonempty. If `T_r` were the full relation, `Enc(T_r)` would only test
  constant patterns. Dec at constants makes `a -> nu(mu(a,...,a),...)` the identity of the finite set `A`, so
  `a -> mu(a,...,a)` is bijective and Enc holds at constants. So a strict datum never has full `T_r`.

**Labellings.** A labelling in `K` is a homomorphism `lambda: F -> K`. It *realizes* `D` when every forward relator
is trivial at `lambda` and every reverse word is nontrivial at `lambda`. This is exactly `T_f ⊆ T_f(lambda)` and
`T_r(lambda) ⊆ T_r`. By [RC] Theorem 1, `K` is not surjunctive iff some strict datum is realized in `K`.

**Bounded products of conjugates.** For `X ⊆ K` let `Cons_n^K(X)` be the set of products of at most `n` factors
`k y^(±1) k^-1`, with `y` in `X` and `k` in `K`; `Cons_0^K(X) = {1}`.
- It is symmetric and conjugation invariant, and `Cons_a · Cons_b ⊆ Cons_(a+b)`.
- For a surjective homomorphism `psi: K -> L`, `psi(Cons_n^K(X)) = Cons_n^L(psi X)`.

**Profinite closure.** `cl(C)` is the closure of `C ⊆ F` in the profinite topology. The basic neighbourhoods of `w`
are the cosets `wK` with `K` normal of finite index. So `w` is in `cl(C)` iff `psi(w)` is in `psi(C)` for every
homomorphism `psi` from `F` onto a finite group.

## 1. The bounded-width closure form

**Theorem 1.1.** The following are equivalent.
- **(a)** Every metric ultraproduct of finite groups with lengths is surjunctive
  (`metric-ultraproducts-of-finite-groups-are-surjunctive`).
- **(b)** For every strict `D` there are `n >= 0` and `w` in `W_r(D)` with `w` in `cl(Cons_n^F(R_f(D)))`.
- **(c)** For every strict `D` there is `n >= 0` with the following property. For every finite group `H` and every
  labelling `lambda` in `H`, some `w` in `W_r(D)` satisfies `w(lambda)` in `Cons_n^H(R_f(lambda))`.

*Proof.* **(b) ⇒ (c).** Take `n` and `w` from (b), a finite `H`, and a labelling `lambda`. With `psi = lambda`
onto `lambda(F)`,
`w(lambda) = psi(w)` lies in `psi(Cons_n^F(R_f)) = Cons_n^(lambda(F))(R_f(lambda)) ⊆ Cons_n^H(R_f(lambda))`.

**(c) ⇒ (b).** Suppose (b) fails for `D`, and fix `n`.
1. For each `w` in `W_r(D)` choose a surjection `psi_w: F -> H_w` onto a finite group with
   `psi_w(w)` not in `Cons_n^(H_w)(psi_w R_f)`.
2. Put `H = prod_w H_w` and `lambda = (psi_w)_w`.
3. Suppose `w(lambda)` lies in `Cons_n^H(R_f(lambda))` for some `w`. The projection `pi_w: H -> H_w` is onto, so
   `psi_w(w) = pi_w(w(lambda))` lies in `Cons_n^(H_w)(psi_w R_f)`, a contradiction.

So (c) fails at `n`, for every `n`.

**(c) ⇒ (a).** Suppose `Q = prod_omega H_i / N_omega` is not surjunctive. By [RC] Theorem 1 it realizes a strict
`D` through some labelling `lambda`.
1. **Lift.** Choose labellings `lambda_i` in `H_i` whose classes give `lambda` on the generators. Since the class
   map is a homomorphism, `r(lambda)` is the class of `(r(lambda_i))_i` for every word `r`.
2. **Relators are infinitesimal.** Put `eps_i = max over r in R_f of l_i(r(lambda_i))`. Every forward relator is
   trivial at `lambda`, so `lim_omega eps_i = 0`.
3. **Reverse words are not.** Every reverse word is nontrivial at `lambda`, so
   `c = min over w in W_r of lim_omega l_i(w(lambda_i))` is positive.
4. **Contradiction.** Take `n` from (c). For each `i` some `w_i` in `W_r` has `w_i(lambda_i)` in
   `Cons_n^(H_i)(R_f(lambda_i))`, so `l_i(w_i(lambda_i)) <= n eps_i`. As `W_r` is finite, one `w` equals `w_i` for
   `omega`-almost every `i`. Then `lim_omega l_i(w(lambda_i)) <= n lim_omega eps_i = 0 < c`.

**(a) ⇒ (c).** Suppose (c) fails for `D`.
1. **Models.** For every `n` pick a finite `H_n` and a labelling `lambda_n` with `w(lambda_n)` outside
   `Cons_n^(H_n)(R_f(lambda_n))` for every `w` in `W_r`.
2. **Lengths.** Let `len_n(h)` be the least `k` with `h` in `Cons_k^(H_n)(R_f(lambda_n))` (`infinity` outside the
   normal closure), and put `l_n = min(1, len_n / n)`. By the properties of `Cons`, `l_n` is a length. Forward
   relators have `l_n <= 1/n`, and reverse words have `len_n > n`, so `l_n = 1`.
3. **Ultraproduct.** Take a nonprincipal ultrafilter `omega` on the natural numbers, `Q = prod_omega H_n / N_omega`,
   and `lambda = [lambda_n]`. Every forward relator is infinitesimal and every reverse word keeps length `1`, so
   `lambda` realizes `D`. By [RC] Theorem 1, `Q` is not surjunctive. QED

**Remark 1.2 (only capped word lengths matter).** The direction (a) ⇒ (c) uses only the lengths
`min(1, len_X / n)` with `X` finite. These are the lengths Glebsky manufactures
(`glebsky-manufactured-invariant-length`). So (a) is equivalent to its restriction to these lengths, and the claim
contains no metric content beyond bounded conjugacy width.

## 2. Three kernels, and the weakly sofic reflection

For a strict `D` let `N = <<R_f(D)>>` be the normal closure in `F`, and put

```text
N_hat = union over n of cl( Cons_n^F(R_f(D)) ),        N_bar = cl(N).
```

**Lemma 2.1.** `N ⊆ N_hat ⊆ N_bar`, and `N_hat` is a normal subgroup of `F`.

*Proof.*
- **Inclusions.** `N` is the union of the `Cons_n^F(R_f)`. Each `Cons_n^F(R_f)` lies in `N`, so its closure lies
  in `N_bar`.
- **Subgroup.** `F` is a topological group in the profinite topology, so `cl(A) cl(B) ⊆ cl(AB)`, and inversion and
  conjugation are homeomorphisms. The sets `Cons_n^F(R_f)` are symmetric and conjugation invariant, and
  `Cons_a · Cons_b ⊆ Cons_(a+b)`. So `N_hat` is closed under products, inverses and conjugation. QED

**Corollary 2.2 (the ladder).**
- **Gottschalk's conjecture** holds iff `W_r(D) ∩ N` is nonempty for every strict `D`. This is [RC] Corollary 1.4:
  equations in `P(D) = F/N`.
- **The metric ultraproduct claim** holds iff `W_r(D) ∩ N_hat` is nonempty for every strict `D` (Theorem 1.1).
- **Unconditionally,** `W_r(D) ∩ N_bar` is nonempty for every strict `D`. Otherwise each reverse word survives in
  some finite quotient of `P(D)`. The product of those quotients realizes `D` in a finite group, which is
  surjunctive.

So the claim is Gottschalk's conjecture with one relaxation: a reverse word need only lie in a profinite closure of
bounded conjugacy width of the forward relators, not in their normal closure. The two statements can differ only
at data with `W_r(D) ∩ N` empty and `W_r(D) ∩ N_hat` nonempty.

**Proposition 2.3 (`N_hat` is the weakly sofic reflection kernel).** `F/N_hat` is weakly sofic. Every normal
`M ⊇ R_f(D)` of `F` with `F/M` weakly sofic contains `N_hat`. So `F/N_hat` is the largest weakly sofic quotient of
`P(D)`.

*Proof.* We use Glebsky–Rivera Theorem 4.3 (`glebsky-rivera-w-sofic-criterion`): for `F` finitely generated free
and `M` normal, `F/M` is weakly sofic iff `cl([g_1]^F ··· [g_k]^F) ⊆ M` for all `g_1, ..., g_k` in `M`.
- **Weak soficity.** Let `g_j` be in `cl(Cons_(n_j)^F(R_f))`. Conjugation invariance gives
  `[g_j]^F ⊆ cl(Cons_(n_j)^F(R_f))`. Then
  `[g_1]^F ··· [g_k]^F ⊆ cl(Cons_(n_1 + ... + n_k)^F(R_f))`, a closed subset of `N_hat`, so the closure of the
  product lies in `N_hat`.
- **Minimality.** `Cons_n^F(R_f)` is the finite union, over `k <= n` and `r_1, ..., r_k` in `R_f^(±1)`, of the
  products `[r_1]^F ··· [r_k]^F`, together with `{1}`. Each `r_j` lies in `M`, so the criterion puts the closure of
  each product in `M`. A finite union of closures is the closure of the union, so `cl(Cons_n^F(R_f)) ⊆ M` for every
  `n`. QED

**Corollary 2.4 (universal test groups).** The claim holds iff no strict `D` is realized by the canonical labelling
of the finitely generated weakly sofic group `P_ws(D) = F/N_hat(D)`. These groups play the role for the claim that
`P(D)` plays for Gottschalk's conjecture.

**Proposition 2.5 (local classes).** Let `C` be a class of groups closed under subgroups, finite direct products,
and local embeddability. Here `G` is in `C` whenever every finite subset of `G` has an injective map into a member
of `C` that is multiplicative on the subset.
- For a strict `D` let `N_C(D)` be the intersection of all normal `M ⊇ R_f(D)` with `F/M` in `C`.
- Then `F/N_C(D)` is in `C`, and every group in `C` is surjunctive iff `W_r(D) ∩ N_C(D)` is nonempty for every
  strict `D`.

*Proof.*
- **The reflection is in `C`.** A finite `Phi` in `F/N_C` is separated by finitely many of the quotients `F/M`. The
  map into their finite product is injective on `Phi` and multiplicative, so `F/N_C` is locally embeddable into
  `C`.
- **If.** Let `G` in `C` realize `D` through `lambda`. Then `M = ker lambda` contains `R_f`, and `F/M ≅ lambda(F)` is
  in `C`. So `M ⊇ N_C`, and every reverse word in `N_C` is trivial at `lambda`, contradicting realization.
- **Only if.** `F/N_C` is in `C`, hence surjunctive, so its canonical labelling does not realize `D`. It kills every
  forward relator, so it kills some reverse word. QED

**Instances.** The class of all groups gives `N`, by [RC]. The classes LEF, sofic, `F`-linear sofic for a fixed
field `F`, and weakly sofic all satisfy the hypotheses. By `sofic-implies-linear-sofic-over-every-field` and
`linear-sofic-implies-weakly-sofic-over-every-field` their kernels are nested:

```text
N  ⊆  N_hat = N_ws  ⊆  N_lin(F)  ⊆  N_sof  ⊆  N_lef  ⊆  N_bar .
```

The last inclusion holds because `F/N_bar` is residually finite, hence LEF.
- Gromov–Weiss is `W_r ∩ N_sof` nonempty for all `D`.
- `linear-sofic-groups-are-surjunctive` over `F_p` is `W_r ∩ N_lin(F_p)` nonempty.
- The claim is `W_r ∩ N_ws` nonempty.
- Gottschalk's conjecture is `W_r ∩ N` nonempty.

Every positive theorem on record reaches at most `N_sof`. Every open positive statement in this region is one step
of this ladder.

## 3. Consequences, test hosts, and the rank calibration

### 3.1 The linear sofic rung

By `linear-sofic-implies-weakly-sofic-over-every-field`, `N_ws ⊆ N_lin(F)`, so the claim implies
`linear-sofic-groups-are-surjunctive` (route `linear-sofic-surjunctivity-from-weak-sofic-case`). A proof of the claim
therefore proves that groups linear sofic over a prime field are surjunctive over every alphabet. The only recorded
route to that, `linear-sofic-surjunctivity-via-formalizability-and-ascent`, needs stable formalizability and
alphabet ascent, and both are open.

### 3.2 Does the rank calibration generalize?

The linear calibration `linear-sofic-group-algebra-is-stably-finite` runs through a ring.
- **Rank bound.** In a rank ultraproduct, `ba = 1 + e` with `rk e <= r` gives `dim ker a <= r`. So some invertible
  `a'` has `rk(a - a') <= r`, and `b a' = 1 + e'` with `rk e' <= 2r`.
- **Conclusion.** Then `ab - 1 = a' e' a'^-1 + (a - a')(1 + e') a'^-1` has rank at most `3r`.
- **What it uses.** A Sylvester rank on an ambient matrix algebra that is small on the defects `d - 1` and bounded
  below on `g - 1` for separated `g`.

A finite group with a length carries no rank of this kind. The transfer works exactly when representation ranks
dominate the lengths in both directions.

**Proposition 3.1.** Let `(H_i, l_i)` define `Q`. Suppose there are representations `rho_i: H_i -> GL_(d_i)(F)` and
constants `C, c, c' > 0` with:
- `rk(rho_i(h) - 1) <= C d_i l_i(h)` for all `h`;
- `rk(rho_i(h) - 1) >= c' d_i` whenever `l_i(h) >= c`.

Then every countable subgroup of `Q` whose nontrivial elements have limit length at least `c` is `F`-linear sofic,
and its group algebra over `F` is stably finite.

*Proof.* Compose each weakly sofic approximation `phi_i` with `rho_i`.
- **Defects.** `rk(rho_i(phi_i(a)phi_i(b)) - rho_i(phi_i(ab))) = rk(rho_i(phi_i(a)phi_i(b)phi_i(ab)^-1) - 1)`, which
  is at most `C d_i eps_i`.
- **Separation.** `rk(rho_i(phi_i(g)) - 1) >= c' d_i`.

Stable finiteness follows from `linear-sofic-group-algebra-is-stably-finite`. QED

So along invariant lengths, the direct-finiteness proof reaches exactly what representations make linear sofic, the
rung `N_lin`. Beyond that rung the method has nothing to act on.

The linear shadow of the claim is `weakly-sofic-group-algebras-are-stably-finite`: `F_q[G]` is stably finite for
every finite field `F_q` and every weakly sofic `G`.
- It follows from the claim through `stable-finiteness-failure-refutes-surjunctivity` (route
  `weak-sofic-stable-finiteness-from-surjunctivity`).
- No argument on record proves it without linear soficity.

### 3.3 Test hosts

- **The Kun–Thom Clifford cover `E_S`.**
  - `kun-thom-clifford-cover-weakly-sofic` makes it weakly sofic. The permanence argument recorded there uses only
    local finiteness of the kernel and residual finiteness of the quotient.
  - So `kun-thom-clifford-cover-nonsurjunctive` refutes the claim.
  - `clifford-cover-anti-half-skew-ring-not-directly-finite` refutes the linear shadow, because
    `F_3[E_S] = F_3[W] x A_S` (`clifford-cover-group-algebra-splits-into-wreath-and-skew-ring`) and a one-sided
    inverse in one factor, padded by `1` in the other, is one in the product.
- **Leavitt unit groups.** If the claim and `leavitt-unit-group-nonsurjunctive` both hold, then `R^x` is not weakly
  sofic, which would be a first non-weakly-sofic group. Read the other way: a strict automaton on `R^x`, together
  with weak soficity of `R^x` (for instance `binary-leavitt-unit-group-is-f2-linear-sofic`), refutes the claim.
- **The Deligne triple cover `E_3`** (from w4-deligne-twisted). Its central `z` lies in the finite residual, hence
  in `cl(N)`. At `z`, `E_3` is weakly sofic exactly when `z` avoids every `cl(Cons_n(R))`: for each `n` some finite
  quotient of the free group has `z` outside the products of `n` relator conjugates. No finite model has to separate
  `z` itself.

### 3.4 Where it stops

- **Positive direction.** A proof must bound the conjugacy width of one reverse word over the forward relators,
  uniformly over all finite quotients of `F(D)`.
  - Finite surjunctivity gives membership in each normal closure, with no bound.
  - Hamming transports give membership in `N_sof` only.
  - No width bound on record applies to normal closures of relators in arbitrary finite quotients.
- **Negative direction.** A counterexample is a Gottschalk counterexample whose weakly sofic reflection still
  realizes it. The recorded weakly sofic nonsofic hosts are the Kun–Thom wreath, which is surjunctive, and `E_S`,
  which is open.

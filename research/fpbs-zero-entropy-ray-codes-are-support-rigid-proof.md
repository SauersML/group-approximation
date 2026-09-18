---
rg: 2
id: fpbs-zero-entropy-ray-codes-are-support-rigid-proof
kind: route
title: The four cases of the rotation rigidity proof only ever conclude that a forward or backward itinerary of one point equals plus or minus an itinerary of the other, so two-sided injectivity of the coding makes the bad relation countable-to-one; zero entropy gives two-sided injectivity through a Krieger binary generator, since the future and the past of a generator each carry everything
target: fpbs-zero-entropy-ray-codes-are-support-rigid
requires:
  - fpbs-rotation-boundary-class-refutes-shadow-summability
---

Full written proof. Notation is as in the claim. Numbered results of
`fpbs-rotation-boundary-class-refutes-shadow-summability-proof` are cited as "[R, Lemma 4.1]" and so on.

## Imported inputs

- **(Kg) Krieger's generator theorem.** An ergodic, aperiodic, invertible probability-preserving transformation of a
  Lebesgue space with `h(T) < log k` has a generating partition into `k` sets (W. Krieger, *On entropy and generators
  of measure-preserving transformations*, Trans. AMS 149 (1970)).
- **(Pf) Pinsker formula and Kolmogorov--Sinai.** For a finite partition `P`,
  `h(T,P) = H(P | ⋁_{n >= 1} T^{-n} P) = H(P | ⋁_{n >= 1} T^{n} P)`, and `h(T,P) = h(T)` when `P` generates
  (e.g. Walters, *An introduction to ergodic theory*, Thm 4.14 and Thm 4.17--4.18).
- **(LS) Lusin--Souslin.** An injective Borel map between standard Borel spaces maps Borel sets to Borel sets.
- **(DJK), (AW), (Kr).** Dougherty--Jackson--Kechris, Trans. AMS 341 (1994), Thm 9.1: aperiodic, nonsmooth hyperfinite
  Borel equivalence relations are classified up to Borel isomorphism by the number of their invariant ergodic
  probability measures. Araki--Woods: for every `lambda ∈ [0,1]` there is a product measure `m_lambda` on `2^N`, quasi-
  invariant and ergodic for `E_0`, of Krieger type `III_lambda`. Krieger: ergodicity and the ratio set are unchanged
  under restriction to a complete section of positive measure.
- **(Rec) Recurrence theorem** for nonsingular actions of countable groups (Aaronson, *An introduction to infinite
  ergodic theory*, §1.6).

## 1. Basic properties of the ray code

Let `(X_0,T,s)` be two-sided injective, `Omega = X_0 x Z/2`, and `sigma`, `zeta_n`, `zeta^+`, `iota_±` as in the claim.
Then `zeta_n(sigma omega) = zeta_{n+1}(omega)`, so the shifted ray satisfies `S zeta^+(omega) = zeta^+(sigma omega)`,
where `S` deletes the first letter.

**Lemma 1.1.**
1. Every `zeta^+(omega)` is a reduced ray: consecutive letters alternate between an `a^{±1}` and a `b^{±1}`.
2. `zeta^+` is injective on `Omega`.
3. No ray `zeta^+(omega)` is eventually periodic.
4. **Tail rigidity.** If `S^p zeta^+(omega) = S^q zeta^+(omega')` with `p, q >= 0`, then `sigma^p omega = sigma^q omega'`.
5. The left-infinite word `... zeta_{-1} zeta_0 (omega)` is not eventually periodic to the left.

*Proof.*
1. `t_n` alternates between `a` and `b`.
2. For `omega = (x,j)`, the type of `zeta_1(omega) = t_{1+j}^{±1}` determines `j`. The exponents of `zeta^+(omega)` are
   `iota_+(x)`, which determines `x` by forward injectivity.
3. Suppose the letters satisfy `zeta_{n+p} = zeta_n` for `n > N`, with `p >= 1`. Then
   `zeta^+(sigma^N omega) = zeta^+(sigma^{N+p} omega)`, so `sigma^N omega = sigma^{N+p} omega` by (2). Hence
   `T^p (T^N x) = T^N x`, which contradicts aperiodicity.
4. `S^p zeta^+(omega) = zeta^+(sigma^p omega)`. Apply (2).
5. Suppose `zeta_{-n-p} = zeta_{-n}` for `n >= N`, with `p >= 1`. The exponents give
   `iota_-(T^{-N} x) = iota_-(T^{-N-p} x)`, so `T^{-N} x = T^{-N-p} x` by backward injectivity. This again contradicts
   aperiodicity. ∎

For `k ∈ Z` let `gamma_k(omega)` be `(zeta_1 ... zeta_k(omega))^{-1}` for `k >= 0` and `zeta_{k+1} ... zeta_0(omega)`
for `k < 0`. These are reduced words of length `|k|`, and `gamma_k(omega) zeta^+(omega) = zeta^+(sigma^k omega)`.

**Lemma 1.2 (orbits through rays).** For `omega ∈ Omega` and `gamma ∈ F`, we have `gamma zeta^+(omega) ∈ B` if and only
if `gamma = gamma_k(omega)` for some `k`, and that `k` is unique.

*Proof.* This is the proof of [R, Lemma 4.1] word for word. It uses only Lemma 1.1(3), (4) and the length and type
count for uniqueness. ∎

**Right-end readings.** As in [R, §5], let `R_k(omega)(r)` be the letter of `gamma_k(omega)` at distance `r` from its
right end, for `0 <= r < |k|`. Then `R_k(omega)(r) = zeta_{r+1}(omega)^{-1}` if `k > 0`, and
`R_k(omega)(r) = zeta_{-r}(omega)` if `k < 0`.

## 2. Theorem 1

**Proposition 2.1 (the four cases).** Let `omega = (x,j)` and `omega' = (x',j')` in `Omega`, and let `u, v ∈ F`. Suppose infinitely many `(k,k') ∈ Z^2`
satisfy `gamma_k(omega) = u gamma_{k'}(omega') v`. Then there are `e, q >= 0` such that one of the following holds:
1. `iota_+(T^e x) = iota_+(T^q x')`;
2. `iota_-(T^{-e} x) = iota_-(T^{-q} x')`;
3. `-iota_+(T^e x) = iota_-(T^{-q} x')`;
4. `iota_-(T^{-e} x) = -iota_+(T^q x')`.

*Proof.* The length count, the bounded-cancellation step and the passage to a subsequence in the proof of
[R, Proposition 5.2] use only that `gamma_k` is reduced of length `|k|`. They give fixed signs of `k`, `k'` and fixed
`e, q >= 0` with

`R_k(omega)(e + t) = R_{k'}(omega')(q + t)` for all `t >= 0`. (2.1)

Compare only the exponents in (2.1). The exponent of `zeta_n(x,j)` is `s(T^n x)`.
1. `k, k' > 0`: `zeta_{e+t+1}(omega)^{-1} = zeta_{q+t+1}(omega')^{-1}`, so `s(T^{e+1+t} x) = s(T^{q+1+t} x')` for all
   `t >= 0`. That is case 1.
2. `k, k' < 0`: `zeta_{-e-t}(omega) = zeta_{-q-t}(omega')`, so `s(T^{-e-t} x) = s(T^{-q-t} x')`. That is case 2.
3. `k > 0 > k'`: `zeta_{e+t+1}(omega)^{-1} = zeta_{-q-t}(omega')`, so `-s(T^{e+1+t} x) = s(T^{-q-t} x')`. That is
   case 3.
4. `k < 0 < k'`: `zeta_{-e-t}(omega) = zeta_{q+t+1}(omega')^{-1}`, so `s(T^{-e-t} x) = -s(T^{q+1+t} x')`. That is
   case 4. ∎

In the rotation the four conclusions are exactly the four cases of [R, Proposition 5.2], each read through Lemma 5.1
there. Here that lemma is replaced by the hypothesis of two-sided injectivity.

**The bad relation.** Let `Bad` be the set of `((x,j),(x',j')) ∈ Omega^2` for which there are `m, n ∈ Z` with one of

`iota_+(T^n x) = iota_+(T^m x')`, `iota_-(T^n x) = iota_-(T^m x')`, `iota_+(T^n x) = -iota_-(T^m x')`,
`iota_-(T^n x) = -iota_+(T^m x')`.

**Lemma 2.2.**
1. `Bad` is Borel and invariant under `sigma x id` and `id x sigma`.
2. For each `omega`, the sections `{omega' : (omega, omega') ∈ Bad}` and `{omega' : (omega', omega) ∈ Bad}` are countable.
3. If `(omega, omega') ∉ Bad`, then for all `u, v ∈ F` only finitely many `(k,k')` satisfy
   `gamma_k(omega) = u gamma_{k'}(omega') v`.

*Proof.*
1. Each condition is the preimage of the diagonal (or the antidiagonal) of `{±1}^N x {±1}^N` under a Borel map, and
   there are countably many conditions. Replacing `x` by `T x` shifts `n` by one, and `m, n` range over `Z`.
2. Fix `omega = (x,j)`, `m, n` and one of the four conditions. The condition prescribes `iota_+(T^m x')` or
   `iota_-(T^m x')` as a fixed sequence. By injectivity of `iota_+` or `iota_-`, at most one `T^m x'` qualifies, so
   at most one `x'`. With two values of `j'`, the section is countable. The other section is symmetric.
3. Proposition 2.1: its conclusions are instances of the four conditions, with `(n, m) = (e, q)`, `(-e, -q)`,
   `(e, -q)` and `(-e, q)`. ∎

**Lemma 2.3 (the null set).** Put `N = ⋃_{h, h' ∈ F} (h x h')(zeta^+ x zeta^+)(Bad)`. Then `N` is Borel. For all
nonatomic finite Borel measures `lambda_1, lambda_2` on `dF`, `(lambda_1 x lambda_2)(N) = 0`.

*Proof.* `zeta^+ x zeta^+` is injective and Borel (Lemma 1.1(2)), so (LS) makes `N` Borel. Fix `h, h'` and put
`N_{h,h'} = (h x h')(zeta^+ x zeta^+)(Bad)`. Its section over `eta` is empty unless `eta = h zeta^+(omega)`. That
`omega` is unique, and then the section is `h' zeta^+(Bad_omega)`, which is countable by Lemma 2.2(2). By Fubini,
`(lambda_1 x lambda_2)(N_{h,h'}) = ∫ lambda_2(countable set) d lambda_1 = 0`. Take the countable union. ∎

No quasi-invariance, ergodicity or relation to any invariant measure is used. Lemma 2.3 is where the method is
support-only.

*Proof of Theorem 1.* Let `(eta, eta') ∉ N` with `eta = h zeta^+(omega)` and `eta' = h' zeta^+(omega')`. Then
`(omega, omega') ∉ Bad`, by the definition of `N`. Fix `w, w' ∈ H`. By Lemma 1.2:
- `g eta ∈ wB` if and only if `g = w gamma_k(omega) h^{-1}` for some `k`;
- `g eta' ∈ w'B` if and only if `g = w' gamma_{k'}(omega') h'^{-1}` for some `k'`.

Both hold if and only if `gamma_k(omega) = (w^{-1} w') gamma_{k'}(omega') (h'^{-1} h)`. Lemma 2.2(3) leaves finitely many
`(k,k')`, hence finitely many `g`. Sum over the finitely many `(w, w')`. ∎

## 3. Theorem 2

This is the proof of [R, Theorem 3(2)] with Lemma 2.3 in place of [R, Lemma 5.3].
- *A cover.* Choose finite-measure sets `E_n` increasing to `Z` and finite sets `H_n` increasing to `F`. Since
  `xi_*(mu_Z|_{E_n})` is carried by `F B`, the sets `E'_n = E_n ∩ xi^{-1}(H_n B)` increase to a conull set.
- *Pairs avoid `N`.* `(xi x xi)_*(mu_Z|_{E'_n} x mu_Z|_{E'_n}) = lambda_n x lambda_n` with `lambda_n = xi_*(mu_Z|_{E'_n})`
  nonatomic and finite. By Lemma 2.3, a.e. pair in `E'_n x E'_n` maps off `N`.
- *Finite returns.* If `g(z,z') ∈ E'_n x E'_n`, then `g xi(z), g xi(z') ∈ H_n B`. By Theorem 1, a.e. pair of
  `E'_n x E'_n` has finitely many such `g`.
- *Dissipativity.* By (Rec), a.e. point of the conservative part `C` that lies in `E'_n x E'_n` returns to it infinitely
  often. So `C ∩ (E'_n x E'_n)` is null for every `n`, and `C` is null.
- *Not PDR.* PDR asks for a conservative piece of the diagonal, as in Theorem A of
  `fpbs-dini-boundary-class-diagonal-dissipative`, and the diagonal has none. ∎

## 4. Theorem 3: zero entropy gives two-sided injectivity

Let `(X,T,m)` be ergodic, aperiodic, probability-preserving, with `h(T) = 0`.

*A binary generator.* By (Kg) with `k = 2`, there is a generating partition `P = {A, X \ A}`. Put `s = 1_A - 1_{X \ A}`.
The atom of `T^{-n} P` containing `x` records `s(T^n x)`. So

`sigma(iota_+) = ⋁_{n >= 1} T^{-n} P =: A_+` and `sigma(iota_-) = ⋁_{n >= 0} T^{n} P =: A_-`.

*The future carries everything.* By (Pf), `H(P | A_+) = h(T,P) <= h(T) = 0`, so `P ⊂ A_+` mod `m`. Put
`A'_+ = ⋁_{n >= 0} T^{-n} P = P ∨ A_+`. Then `A'_+ = A_+` mod `m`, and `T^{-1} A'_+ = A_+`. Since `T` preserves `m`,
this gives `T^{-1} A_+ = A_+` mod `m`. So `A_+` contains `T^{-n} P` for every `n ∈ Z`, mod `m`. Because `P`
generates, `A_+` is the full Borel `sigma`-algebra mod `m`.

*The past carries everything.* By (Pf), `H(P | ⋁_{n >= 1} T^n P) = 0`. The same argument, with `T^{-1}` in place of `T`,
shows that `⋁_{n >= 1} T^n P`, and hence `A_-`, is full mod `m`.

*From mod 0 to injectivity.* Let `f : X -> {±1}^N` be Borel with `sigma(f)` full mod `m`. Choose Borel sets `A_i`,
`i ∈ N`, that separate points. For each `i` choose a Borel `C_i` with `m(A_i Δ f^{-1} C_i) = 0`, and put
`N_f = ⋃_i (A_i Δ f^{-1} C_i)`, a null set. For `x, y ∉ N_f`, `f(x) = f(y)` gives `x ∈ A_i ⟺ y ∈ A_i` for every `i`,
so `x = y`.

Apply this to `iota_+` and `iota_-`. Let `X_0` be `X` minus the `T`-saturation of `N_{iota_+} ∪ N_{iota_-}` and minus
the periodic points. This set is Borel, `T`-invariant and conull, because `T` preserves `m` and `m`-a.e. point is
aperiodic. On `X_0` both itineraries are injective. ∎

*Remark.* The proof uses `h = 0` only through `H(P | A_+) = H(P | A_-) = 0`. So any finite-valued coding whose future
and past each determine the present works. The binary case is what the ray code needs.

## 5. Theorem 4: every Krieger type on the rays of a zero-entropy system

Let `X_0` and `s` be as in Theorem 3, and put `Omega_1 = X_0 x Z/2` with `sigma`.
- *A uniquely ergodic complete piece.* Let `P'` be an ergodic component of `m x (uniform)` under `sigma`. Every
  component projects to a `T`-invariant measure, and these projections average to the ergodic `m`, so a.e. component
  projects to `m`. Fix one, `P'`. Fix a countable algebra `(C_i)` generating the Borel sets of `Omega_1`. Let `G` be
  the set of `omega` whose Birkhoff averages of every `1_{C_i}` converge to `P'(C_i)`. Then `G` is Borel,
  `sigma`-invariant and `P'`-conull. If `nu` is an ergodic `sigma`-invariant probability on `G`, the Birkhoff theorem
  for `nu` gives `nu(C_i) = P'(C_i)` for all `i`, so `nu = P'`. So `P'` is the unique invariant probability on `G`.
- *DJK.* `R_sigma|G` is aperiodic, since `T` has no periodic points on `X_0`. It is hyperfinite, since it is generated
  by one automorphism. It is nonsmooth, since it carries the nonatomic ergodic invariant `P'`. `E_0` on `2^N` has the
  same three properties and one invariant ergodic probability. By (DJK) there is a Borel isomorphism
  `Psi : G -> 2^N` carrying `R_sigma|G` onto `E_0`.
- *The measure.* Put `rho_lambda = Psi^{-1}_* m_lambda` with `m_lambda` from (AW). Then `rho_lambda` is nonatomic, and it
  is `R_sigma`-quasi-invariant and ergodic of type `III_lambda`.
- *The class on `dF`.* Put `nu = sum_g c_g g_* zeta^+_* rho_lambda`, with `c_g > 0` and total mass 1. Each `g'_* nu` is
  equivalent to `nu`, so `nu` is `F`-quasi-invariant.
  - `nu` is carried by `F zeta^+(G)`, and `zeta^+(G)` is a complete section.
  - By Lemma 1.2, the orbit relation of `F` restricted to `zeta^+(G)` is `(zeta^+ x zeta^+)(R_sigma|G)`.
  - `nu|_{zeta^+(G)}` is equivalent to `zeta^+_* rho_lambda`. The summand `c_e` gives one inequality. For the other,
    the set `{omega : gamma_k(omega) = g}` is carried into `zeta^+(G)` by `zeta^+ ∘ sigma^k`, and `rho_lambda` is
    `sigma`-quasi-invariant, so each summand restricted to `zeta^+(G)` is `<< zeta^+_* rho_lambda`.
  - Hence, by (Kr), `nu` is ergodic of type `III_lambda`.
- *Killing.* `nu` is nonatomic and carried by `F B`. The Maharam extension `(dF x R, nu x e^t dt)` projects to `dF`,
  and the restriction of its measure to any set of finite measure pushes forward to a measure `<< nu`. The same holds
  for every imp action over `nu`. Theorem 2 applies to each. ∎

## 6. Where the method stops: positive entropy

*Bernoulli.* Let `X_0 = {±1}^Z` with the shift and `s(x) = x_0`. Then `B` is the set of all type-alternating reduced
rays. Take `z, z' ∈ B`, both beginning with an `a`-letter. Every type-alternating reduced word `w` of even length that
ends in a `b`-letter gives reduced, type-alternating rays `w z` and `w z'`, which lie in `B`. So every pair has
infinitely many joint returns to `B x B`. The conclusion of Theorem 1 fails for **every** pair, not just on a null set.
The failure is at Lemma 1.1(2) and (4): here the future does not determine the past.

*General positive entropy.* Let `(X,T,m)` be ergodic with `h(T) > 0`, and let `P` be a finite generating partition.
By (Pf), `H(P | A_+) = h(T) > 0`, so `A_+` is not full mod `m`. If `iota_+` were injective on a conull Borel set
`X_1`, then (LS) would make every Borel subset of `X_1` the `iota_+`-preimage of a Borel set, so `A_+` would be full
mod `m`. So forward injectivity fails on every conull set. A non-generating `P` codes a factor, and the same holds
for that factor whenever the factor has positive entropy.

This says only that the support method needs zero entropy. Whether a positive-entropy ray class carries a
conservative diagonal, or is killed through its Radon--Nikodym fibre, is the open statement named in the claim.

## 7. Hyperbolic groups

Theorem C of `fpbs-rotation-support-rigidity-kills-type-iii-classes` (with its pigeonhole Lemma 3.1) uses the rotation
code only through three properties:
- reducedness;
- tail rigidity;
- the fact that forward and backward rays are not eventually periodic.

These are Lemma 1.1(1), (3), (4) and (5) here. It also uses Theorem 1 in place of [R, Proposition 5.2]. So it holds
verbatim for the ray code of any two-sided injective system. In particular it holds for every zero-entropy ergodic
system, embedded in a quasiconvex free subgroup with (M').

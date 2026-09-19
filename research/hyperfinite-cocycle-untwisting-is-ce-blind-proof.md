---
rg: 2
id: hyperfinite-cocycle-untwisting-is-ce-blind-proof
kind: route
title: Amplify the Bernoulli action of a sofic Kazhdan group, identify the corner crossed product, and lift the cocycle crossed product into the normalizer
target: hyperfinite-cocycle-untwisting-is-ce-blind
requires:
  - popa-vanishing-cohomology-amplification-and-ce-imports
  - leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity
  - elementary-groups-over-fg-rings-have-property-t
---

Notation is as in the target. Popa's statements are cited by his numbering, and each is quoted in
`popa-vanishing-cohomology-amplification-and-ce-imports-citation`.

## 0. A recognition lemma for cocycle crossed products

**Lemma 0.** Let `M` be a finite von Neumann algebra with faithful normal trace `tau`, `N <= M` a `II_1` subfactor
(with `tau|_N = tau_N`), and `(alpha, v)` a normalized cocycle action of `Gamma` on `N`. Suppose there are unitaries
`W_g in M` such that:
1. `W_g x W_g^* = alpha_g(x)` for `x in N`;
2. `W_g W_h = v_(g,h) W_(gh)` and `W_e = 1`;
3. `tau(y W_g) = 0` for `y in N`, `g != e`;
4. the span of `N W_g`, `g in Gamma`, is weakly dense in `M`.

Then `sum_h U_h x_h -> sum_h W_h x_h` extends to a trace-preserving isomorphism `N x|_(alpha,v) Gamma ≅ M` that is
the identity on `N`.

*Proof.* Popa's crossed product is the weak closure of the finitely supported sums `sum U_h x_h`, with
multiplication determined by `x U_h = U_h alpha_h^(-1)(x)`, `U_g U_h = v_(g,h) U_(gh)` and
`U_g^* = U_(g^(-1)) v_(g,g^(-1))^*`. By 1 and 2 the elements `W_h` satisfy the same relations, so the map is a
`*`-homomorphism from the algebraic crossed product onto the algebra spanned by the `N W_g`. By 3,
`tau(sum W_h x_h) = tau_N(x_e)`, which is Popa's trace. A trace-preserving `*`-homomorphism between the dense
`*`-algebras of two tracial GNS constructions is isometric in `||.||_2`. So it extends to a normal trace-preserving
injective `*`-homomorphism of the von Neumann closures. By 4 its image is `M`. ∎

## 1. (K2) Amplification commutes with crossed products

Let `M = N x|_sigma Gamma` with canonical unitaries `U_g`, `p in N` a projection of trace `t`, and `w_g` as in
Popa's Definition 3.1: `w_g w_g^* = p`, `w_g^* w_g = sigma_g(p)`, `w_e = p`. Put `W_g = w_g U_g in pMp`. Give `pMp`
the normalized trace `tau/t`.
- **Unitary.** `W_g W_g^* = w_g U_g U_g^* w_g^* = p`, and `W_g^* W_g = U_g^* sigma_g(p) U_g = p`.
- **Implements `sigma^p`.** For `x in pNp`, `W_g x W_g^* = w_g sigma_g(x) w_g^* = sigma^p_g(x)`.
- **Cocycle.** `w_h = w_h sigma_h(p)` gives `sigma_g(w_h) = sigma_g(w_h) sigma_(gh)(p) = sigma_g(w_h) w_(gh)^* w_(gh)`.
  Hence `W_g W_h = w_g sigma_g(w_h) U_(gh) = (w_g sigma_g(w_h) w_(gh)^*) w_(gh) U_(gh) = v^p_(g,h) W_(gh)`.
  Also `W_e = p`, the unit of `pMp`.
- **Trace.** For `y in pNp` and `g != e`, `tau(y W_g) = tau((y w_g) U_g) = 0`.
- **Generation.** `pMp` is the weak closure of the span of `p x U_g p`, `x in N`. And
  `p x U_g p = p x sigma_g(p) U_g = p x w_g^* w_g U_g = (p x w_g^*) W_g`, with `p x w_g^* in pNp`.

Lemma 0, applied to `pNp <= pMp`, gives `pMp ≅ pNp x|_(sigma^p, v^p) Gamma`.

**CE is invariant under amplification.**
- *Corners.* Let `M <= R^omega` and let `p in M` be a projection with `tau(p) = t > 0`. Lift `p` to projections
  `p_n in R` with `tau(p_n) -> t`. Then `pR^omega p` is the tracial ultraproduct of the `p_n R p_n` with their
  normalized traces. Each `p_n R p_n ≅ R`, so `pR^omega p ≅ R^omega`, and `pMp` is CE.
- *Converse.* If `pMp <= R^omega`, choose `k >= 1/t`. Then `M` is isomorphic to a corner of `M_k(pMp)`, and
  `M_k(pMp) <= M_k(R^omega) ≅ M_k(R)^omega ≅ R^omega`. So `M` is CE by the corner case.

## 2. (K3) The cocycle form of Popa's Theorem 6.3

Let `(alpha, v)` be a free cocycle action of `Gamma` on `R`, `M = R x|_(alpha,v) Gamma`, with canonical unitaries
`U_g`. By Popa's freeness criterion, `R' ∩ M = C1`, so `M` is a `II_1` factor.

**(⇒)** Let `theta : M -> R^omega` be a trace-preserving embedding.
- By the fact used in Popa's proof of Theorem 6.3 (two copies of `R` in `R^omega` are unitarily conjugate), there
  is `W in U(R^omega)` with `W theta(R) W^* = R`.
- Then `phi = Ad(W) theta|_R` is an automorphism of `R`. By Popa's Proposition 6.1 2°, `phi = Ad(U_phi)|_R` for
  some `U_phi in N_(R^omega)(R)`.
- Put `theta' = Ad(U_phi^* W) theta`. This is a trace-preserving embedding of `M` with `theta'|_R = id_R`.
- Put `V_g = theta'(U_g)`. For `x in R`, `V_g x V_g^* = theta'(U_g x U_g^*) = theta'(alpha_g(x)) = alpha_g(x)`. So
  `V_g in N_(R^omega)(R)` and `Ad(V_g)|_R = alpha_g`.
- Finally `V_g V_h = theta'(v_(g,h) U_(gh)) = v_(g,h) V_(gh)`.

**(⇐)** Let `V_g` be as in the statement. Normalization gives `V_e V_e = V_e`, so `V_e = 1`.
- **Trace.** Fix `h != e`, and let `E_R : R^omega -> R` be the trace-preserving conditional expectation. Put
  `y = E_R(V_h)`. For `x in R`, `V_h x = alpha_h(x) V_h`. Applying `E_R`, which is `R`-bimodular, gives
  `y x = alpha_h(x) y`.
  - Then `y^* y x = y^* alpha_h(x) y = (alpha_h(x^*) y)^* y = (y x^*)^* y = x y^* y`. So `y^* y in R' ∩ R = C1`.
  - Likewise `y y^* alpha_h(x) = y x y^* = alpha_h(x) y y^*`, so `y y^* in C1`.
  - If `y != 0`, then `y = lambda u` with `lambda > 0` and `u in U(R)`, and `u x u^* = alpha_h(x)`. So `alpha_h` is
    inner, contradicting freeness. Hence `y = 0`, and `tau(x V_h) = tau(x E_R(V_h)) = 0` for all `x in R`.
- **Embedding.** Lemma 0 applies to `M' = (R ∪ {V_g})''` inside `R^omega`, with `W_g = V_g`: conditions 1 and 2
  are the hypotheses, 3 was just shown, and 4 holds by definition of `M'`. So `M ≅ M' <= R^omega`.

**Remark.** For a free action the trace condition of `finitary-extension-ce-iff-action-lifts-to-normalizer` (2) is
automatic. The argument above is the same one, carried out with a cocycle.

## 3. (K1) CE-blind cocycles on sofic groups with an infinite relative (T) subgroup

Let `Gamma` be sofic and contain an infinite subgroup with the relative property (T). Let `sigma` be the
noncommutative Bernoulli action of `Gamma` on `R_0^(⊗Gamma) ≅ R`, with `R_0 = L(S_inf) ≅ R`. Here `S_inf` is the
group of finitary permutations of `N`, which is amenable and ICC, so `L(S_inf) ≅ R` by Connes' theorem as quoted in
Popa's Remark 6.5.1°.
- **The untwisted crossed product is CE.** Popa's Remark 6.5.1° (from [HaS16]) says that `S_inf wr Gamma` is sofic
  and that `R x|_sigma Gamma = L(S_inf wr Gamma)` is CAE. Write `M` for this factor. The action `sigma` is free
  (Theorem 3.2 speaks of "the free cocycle action obtained by amplifying σ", and Definition 3.1 amplifies free
  actions), so `M` is a `II_1` factor.
- **Amplification.** Fix `0 < t < 1` and a projection `p in R` of trace `t`. Popa's Definition 3.1 gives a free
  cocycle action `(sigma^p, v^p)` of `Gamma` on `pRp ≅ R`, representing `(sigma^t, v^t)` up to cocycle conjugacy.
- **Not weak-vanishing.** By Popa's Theorem 3.2(a), `v^t` is not weak-vanishing. Definition 3.1 defines
  `(sigma^t, v^t)` only up to cocycle conjugacy, as the class of `(sigma^p, v^p)` for any `p` of trace `t`, so the
  theorem is a statement about `v^p`. In particular `v^p` does not vanish.
- **Its crossed product is CE.** By (K2), `pRp x|_(sigma^p, v^p) Gamma ≅ pMp`. By the corner part of (K2), `pMp` is
  CE because `M` is.
- **At `t = 1`.** `sigma` is a genuine action, so its cocycle is `1`, and `M` is CE.

So the same group carries a free cocycle action on `R` that is untwistable in `U(R)` and one that is not even weakly
untwistable. Both crossed products are CE, and the second is an amplification of the first. By (K3), both cocycles
untwist in `U(R_omega)`: for `pMp`, the lifts `V_g` exist even though no unitaries of `pRp` untwist `v^p`.

## 4. Application to the Toeplitz corner

Let `E = EL_20(J)` act on `V`, with `L = GL_fin(V)`. Step 2 of `leavitt-corner-trace-gate-jacobson-proof`, the route
of the required claim `leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity`, proves:
- (S1) `L <= E`;
- (S2) `L` is simple and perfect;
- (S3) `C_E(L) = 1`;
- `E/L ≅ EL_20(F_2[x,x^(-1)]) = Q`.

**(A1) The corner cocycle action is free, on `R`.**
- *Infinite `L`-classes.* Let `g in E`, `g != 1`, have a finite `L`-conjugacy class. Then `C_L(g)` has finite index
  in `L`, and so contains a finite-index normal subgroup of `L`. `L` is infinite and simple (S2), so that normal
  subgroup is `L`. Hence `g in C_E(L) = 1` (S3), a contradiction.
- *Consequences.*
  - With `g in L`, this says `L` is ICC. `L` is locally finite, hence amenable, so `L(L) ≅ R` by Connes' theorem.
  - In general, an element `sum_g c_g u_g in L(E)` commuting with `L(L)` has `c` constant on `L`-conjugacy classes
    and square-summable. So it is supported on finite classes, i.e. on `{1}`. Hence `L(L)' ∩ L(E) = C1`.
- *The crossed product.* Choose a section `s : Q -> E` with `s(e) = 1`. Put `W_q = u_(s(q))`,
  `alpha_q = Ad(W_q)|_(L(L))` and `omega_(q,r) = u_(s(q)s(r)s(qr)^(-1))`, a unitary of `L(L)`. Then:
  - the normalized cocycle identities (1.1.1) and (1.1.2) hold, being identities in `E`;
  - `W_q W_r = omega_(q,r) W_(qr)`;
  - `tau(y W_q) = 0` for `y in L(L)`, `q != e`, since `y W_q` is supported on the coset `L s(q) != L`;
  - the span of `L(L) W_q` contains every `u_g`, `g in E`.
  
  By Lemma 0, `L(E) ≅ R x|_(alpha,omega) Q`.
- *Freeness.* By Popa's freeness criterion and `L(L)' ∩ L(E) = C1`, `(alpha, omega)` is free.

**(A2) `Q` meets the hypotheses of (K1).**
- *Property (T).* `Q` has property (T) by `elementary-groups-over-fg-rings-have-property-t` (`F_2[x,x^(-1)]` is
  finitely generated, `20 >= 3`), and `Q` is infinite. So `Q` is its own infinite relative (T) subgroup, and
  `Q ∉ VC_w(R)` by Popa's Corollary 3.3.
- *Residually finite.* For `N >= 1`, reduction modulo `x^N - 1` maps `Q` into the finite group
  `GL_20(F_2[x]/(x^N - 1))`. A nonzero Laurent polynomial whose exponents lie in an interval of length `< N` is
  nonzero modulo `x^N - 1`. So a given `g != 1` survives for `N` large.
- *Sofic.* The left regular actions of these finite quotients on themselves are homomorphisms into symmetric groups.
  Each `g != 1` eventually acts without fixed points. So `Q` is sofic.

(K1) therefore applies with `Gamma = Q`.

## 5. (A3) The kill

The decision point recorded in `agent-leavitt-not-bcs-negative-root-corner` is to decide whether `omega` is a
(weak) coboundary in `U(R)`, or whether the induced cocycle vanishes in `R' ∩ R^omega`. Take the three readings in
turn.

1. **`U(R)` coefficients, negative outcome.**
   - *Claim.* The implication "(beta, v) free cocycle action of `Q` on `R`, `v` not weak-vanishing ⇒
     `R x|_(beta,v) Q` not CE" is false.
   - *Proof.* Take `(beta, v) = (sigma^p, v^p)` from Section 3 with `Gamma = Q`, which is legitimate by (A2).
   - *Consequence.* A proof that `omega` does not weakly vanish yields non-hyperlinearity of `E` only together
     with a further property `P` of `(alpha, omega)`, where `P` fails for every amplified Bernoulli cocycle of `Q`.
     All of the logical work is then in `P`.
2. **`U(R)` coefficients, positive outcome.**
   - Suppose `omega` weakly vanishes: by Popa's (1.4.2) there are `w_q in U(R)`, `w_e = 1`, with
     `w_q alpha_q(w_r) omega_(q,r) w_(qr)^* = mu_(q,r) in T`.
   - Put `W'_q = w_q W_q`. Then `W'_q W'_r = w_q alpha_q(w_r) W_q W_r = w_q alpha_q(w_r) omega_(q,r) W_(qr) =
     mu_(q,r) W'_(qr)`. Also `beta_q = Ad(W'_q)|_R = Ad(w_q) alpha_q` is outer for `q != e`, and `beta` is a genuine
     action because scalars act trivially.
   - Lemma 0 gives `L(E) ≅ R x|_(beta,mu) Q`, a crossed product with scalar cocycle `mu`.
   - By (K3), CE of this crossed product is again equivalent to a normalizer lift `V_q` with
     `V_q V_r = mu_(q,r) V_(qr)`. That is the same kind of problem with a scalar cocycle.
   - This outcome points toward hyperlinearity, the opposite of the goal, and does not settle it.
3. **`U(R_omega)` coefficients.**
   - Given any lifts `U_q in N_(R^omega)(R)` of `alpha_q`, the unitaries `c_(q,r) = omega_(q,r)^* U_q U_r U_(qr)^*`
     commute with `R`, because `Ad(U_q U_r U_(qr)^*)|_R = alpha_q alpha_r alpha_(qr)^(-1) = Ad(omega_(q,r))`.
   - "Vanishing in `R' ∩ R^omega`" means `U_q` can be corrected by `U(R_omega)` to make `c = 1`. That is exactly
     the lift in (K3).
   - So by (K3), this reading is equivalent to `L(E)` being CE, i.e. by Definition 6.2 to `E` being hyperlinear. It
     is the hole restated.

**Invariant and death step.**
- The invariant is amplification. CE of the crossed product is unchanged by `(alpha, v) -> (alpha^t, v^t)` (K2).
  Vanishing in `U(R)` changes (Section 3: from vanishing at `t = 1` to not weakly vanishing at `t < 1`).
- Every member of the class dies at the change of coefficients from `U(R)` to `U(R_omega)`, i.e. at (K3). Only
  the `U(R_omega)` question is equivalent to CE, and that question is the hole.

**Prior art.** Popa's Remark 6.5.3° already observes that the amplified Bernoulli cocycles, the only known cocycle
actions on `R` that do not untwist, would untwist on `R ∨ R_omega` whenever `sigma(Gamma)` does. (K1) makes this
unconditional for sofic `Gamma` via [HaS16] and (K2). The new content is its application to the Toeplitz corner
cocycle of `EL_20(J)`. The Kazhdan group `Q` is exactly the group on which Popa's non-vanishing theorem applies, so
a Popa-style non-vanishing proof for `omega` would be available in principle, and by item 1 it would be inert.

## 6. The sufficient condition (not proved)

Let `beta` be the genuine action of `Q` on `R_bi = L(GL_fin(W))` from `untwisted-bilateral-symbol-enrichment-is-lef`,
so `R_bi x|_beta Q = L(H_bi)`, which is CE because `H_bi` is LEF, hence sofic. Suppose that `(alpha, omega)` is
cocycle conjugate to `(beta^p, v^p)` for a projection `p in R_bi`, through a group automorphism `gamma` of `Q`. Then:
- Popa's Proposition 1.2 (converse part) gives `L(E) ≅ pR_bi p x|_(beta^p, v^p) Q`;
- (K2) identifies this with `p L(H_bi) p`, which is CE.

So `E` would be hyperlinear. This is recorded as a spark, not as a node. It is not proved, and it is not a
consequence of the group-level compression `V -> V_+`: `L(L)` sits in `R_bi` as a subalgebra, not as a corner.

No step of this route decides the hole itself. ∎

---
rg: 2
id: kazhdan-relations-have-no-poly-haagerup-host-proof
kind: route
title: Induce a C0 positive-definite function along the host cocycle, fix a vector by (T) of L(R), cohomologize into a finite group through the normal series, and contradict smoothness of the skew product
target: kazhdan-relations-have-no-poly-haagerup-host
requires:
  - non-ce-property-t-equivalence-relation-exists
---

**Notation.**
* `R` is on `(X, mu)`. `S` is on `(A, zeta_A)`, with `zeta_A` a probability measure, and `r : A -> X` is as in item 1
  of the claim.
* For `theta ∈ [R]`, the *lift* `theta~ ∈ [S]` sends `a` to the unique point of `[a]_S` over `theta(r(a))`.
  * `theta ↦ theta~` is a homomorphism, and `r ∘ theta~ = theta ∘ r`.
  * `theta~` preserves `zeta_A`, because its graph lies in `S`.
  * `Fix(theta~) = r^(-1)(Fix(theta))`, by class-injectivity of `r`.
* `E_X : L^infinity(A) -> L^infinity(X)` is the conditional expectation onto `r^(-1)`(Borel sets), so
  `∫_{r^(-1)D} g · (f∘r) d zeta_A = ∫_D E_X(g) f d mu`.
* `L(S)` acts on `L^2(S, nu)`, where `nu` is the left counting measure, by kernels:
  `(T eta)(a, a'') = Σ_{a'} T(a, a') eta(a', a'')`.
  * `u_{theta~}` has kernel `1{a = theta~ a'}`.
  * `f ↦ f∘r` and `u_theta ↦ u_{theta~}` extend to a trace-preserving embedding `L(R) ⊆ L(S)`. By the fixed-point
    identity, `tau_S((f∘r) u_{theta~}) = ∫_{Fix theta} f d mu`. This is the lifting used in item 1 of
    `nonce-relation-hosts-force-root-or-q1-failure`.
  * `E` denotes the trace-preserving conditional expectation `L(S) -> L(R)`.

## Step 0. The imported property (T) statement

From S. Popa, *On a class of type II_1 factors with Betti numbers invariants*, Ann. of Math. 163 (2006) 809–899.
Quoted from arXiv:math/0209130, pp. 35–36, read 2026-09-19:
* *"(4.0.2'). For any ε > 0, there exist a finite subset F′ ⊂ N and δ′ > 0 such that if H is a Hilbert N-bimodule
  and ξ ∈ H is a unit vector satisfying ‖yξ − ξy‖ ≤ δ′, ∀y ∈ F′, then there exists ξ0 ∈ H such that xξ0 = ξ0x,
  ∀x ∈ N and ‖ξ − ξ0‖ ≤ ε."* The paper attributes to Connes–Jones the equivalence of this with their definition of
  property (T) for a II_1 factor `N`.
* *"4.1. Proposition. ... The following conditions are equivalent: 1°. There exists a normal faithful tracial state
  τ on N such that: ∀ε > 0, ∃F′ ⊂ N finite and δ′ > 0 such that if H is a Hilbert N-bimodule with a vector ξ ∈ H
  satisfying the conditions ‖⟨·ξ,ξ⟩ − τ‖ ≤ δ′, ‖⟨ξ·,ξ⟩ − τ‖ ≤ δ′ and ‖yξ − ξy‖ ≤ δ′, ∀y ∈ F′ then ∃ξ0 ∈ H such
  that ‖ξ0 − ξ‖ ≤ ε and bξ0 = ξ0b, ∀b ∈ B. 2°. There exists a normal faithful tracial state τ on N such that:
  ∀ε > 0, ∃F ⊂ N finite and δ > 0 such that if φ : N → N is a normal, completely positive map with τ∘φ ≤ τ,
  φ(1) ≤ 1 and ‖φ(x) − x‖_2 ≤ δ, ∀x ∈ F, then ‖φ(b) − b‖_2 ≤ ε, ∀b ∈ B, ‖b‖ ≤ 1."*

Take `B = N = L(R)`. A vector as in 1° is a unit vector, since `<1ξ, ξ>` is within `δ′` of `τ(1) = 1`, and 1°
only adds hypotheses to (4.0.2′), up to rescaling. So (4.0.2′) gives 1°, and hence 2°.

**(T′).** *If `Phi_n` are normal unital trace-preserving cp maps on `L(R)` with `‖Phi_n(x) − x‖_2 -> 0` for every
`x`, then some `n` has `‖Phi_n(u) − u‖_2 ≤ 1/10` for every `u` in the unit ball.*

*Proof.* Apply 2° with `ε = 1/10`, which gives `F` and `δ`. Since `F` is finite, some `n` has
`‖Phi_n(x) − x‖_2 ≤ δ` for all `x ∈ F`. □

**Haagerup property used.** A countable group `Q` is Haagerup when it has normalized positive-definite functions
`phi_n` that are `C_0` (vanish at infinity) and satisfy `phi_n -> 1` pointwise.

## Step 1. Schur multipliers from a cocycle

Let `b : S -> Q` be a Borel cocycle, meaning `b(a, a'') = b(a, a') b(a', a'')`, with `b(a', a)` read as "from `a` to
`a'`". Let `phi(g) = <rho(g) xi, xi>` be a normalized positive-definite function on `Q`, with `rho` its GNS
representation on `K` and `xi` a cyclic unit vector.

Define `V : L^2(S) -> L^2(S) ⊗ K` by `(V eta)(a, a'') = eta(a, a'') rho(b(a'', a)) xi`. Pointwise
`‖rho(.) xi‖ = 1`, so `V` is an isometry. Put `m(T) = V* (T ⊗ 1) V` for `T ∈ B(L^2(S))`. By the cocycle identity,
`<rho(b(a'', a')) xi, rho(b(a'', a)) xi> = phi(b(a, a'))`, and so
`(m(T) eta)(a, a'') = Σ_{a'} phi(b(a, a')) T(a, a') eta(a', a'')`.

It follows that:
* `m` is normal and completely positive. It is unital because `b(a, a) = 1`.
* `m` multiplies kernels by the function `phi ∘ b`. It sends each `(f ∘ r) u_{theta~}` into `L(S)`, so by normality
  it maps `L(S)` into `L(S)`.
* The diagonal of the kernel is unchanged, so `tau_S ∘ m = tau_S`.

Put `Phi = E ∘ m`, restricted to `L(R)`. It is normal, unital, completely positive and trace-preserving on `L(R)`.
By Kadison–Schwarz it is a `‖.‖_2`-contraction.

For `x = (f ∘ r) u_{theta~}`, the kernel of `m(x) − x` is `f(r(a)) (phi(b(a, a')) − 1) 1{a = theta~ a'}`. Hence
`‖Phi(x) − x‖_2^2 ≤ ‖m(x) − x‖_2^2 = ∫ |f(r(a))|^2 |phi(b(a, theta~^(-1) a)) − 1|^2 d zeta_A(a)`.

Now take `phi = phi_n` with `phi_n -> 1` pointwise. By dominated convergence, `Phi_n(x) -> x` in `‖.‖_2` for these
`x`. Their span is `‖.‖_2`-dense and the maps are uniform contractions, so `Phi_n(x) -> x` for every `x ∈ L(R)`.
By (T′), there is `n` with `‖Phi_n(u_theta) − u_theta‖_2 ≤ 1/10` for every `theta ∈ [R]`.

The kernel of `m(u_{theta~})` is `phi(b(a, a')) 1{a = theta~ a'}`. So
`tau(Phi(u_theta) u_theta*) = tau_S(m(u_{theta~}) u_{theta~}*) = ∫ phi(b(a, theta~^(-1) a)) d zeta_A(a)`.
Its real part is at least `1 − ‖Phi(u_theta) − u_theta‖_2 ≥ 9/10`. Fix this `phi = phi_n`, which is `C_0`, and
write `rho`, `K`, `xi` for its GNS data.

**(1.1)** For every `theta ∈ [R]`, `Re ∫ phi(b(a, theta~^(-1) a)) d zeta_A(a) ≥ 9/10`.

## Step 2. An invariant vector field

Let `[R]` act on `L^2(A, zeta_A; K)` by `(theta . F)(a) = rho(b(a, theta~^(-1) a)) F(theta~^(-1) a)`.
* Each `theta~` preserves `zeta_A`, so each operator is unitary.
* `theta ↦ theta~` is a homomorphism, and the cocycle identity then makes this a representation.

Let `F_xi` be the constant field `xi`, a unit vector. Then `<theta . F_xi, F_xi> = ∫ phi(b(a, theta~^(-1) a)) d zeta_A`,
so (1.1) gives `‖theta . F_xi − F_xi‖^2 ≤ 2 − 18/10 = 1/5` for every `theta`.

The orbit `[R] . F_xi` is a bounded set, and `[R]` permutes it. So its unique circumcenter `F_0` is `[R]`-fixed.
`F_0` lies in the closed convex hull of the orbit, hence `‖F_0 − F_xi‖ ≤ 5^(-1/2)` and `‖F_0‖ ≥ 1 − 5^(-1/2) > 0`.

Fix a Borel representative of `F_0`; `K` is separable, since `Q` is countable. By Feldman–Moore, some countable
group `Gamma_0 ≤ [R]` generates `R`. For `(a', a) ∈ S`, pick `theta ∈ Gamma_0` with `theta(r(a)) = r(a')`. Then
`theta~ a` is the point of `[a]_S` over `r(a')`, which is `a'` by class-bijectivity. So the lifts of `Gamma_0`
generate `S`.

Discard the `S`-saturation of the countably many null sets on which `theta . F_0 = F_0` fails pointwise for
`theta ∈ Gamma_0`. This saturation is null, because `S` preserves `zeta_A`. On what remains:

**(2.1)** `F_0(a') = rho(b(a', a)) F_0(a)` for all `(a', a) ∈ S`.

## Step 3. A finite-set section, and item 2

**`rho` is a `C_0` representation.** Its coefficients on the dense span of `rho(Q) xi` are finite sums of
translates of `phi`, which is `C_0`. Every coefficient is a uniform limit of these, so every coefficient is `C_0`.

**The section.** Let `A_0 = {a : F_0(a) ≠ 0}`.
* `A_0` is `S`-invariant by (2.1), and `zeta_A(A_0) > 0` because `F_0 ≠ 0`.
* For `a ∈ A_0` put `p_a(g) = |<F_0(a), rho(g) xi>|`.
  * `p_a` is `C_0` on `Q`.
  * `p_a ≢ 0`, because `xi` is cyclic.
  * So its maximum is attained on a nonempty finite set `Phi(a) ⊆ Q`.
* `a ↦ Phi(a)` is Borel into the countable set `Fin(Q)` of finite subsets.
* By (2.1), `p_{a'}(g) = |<F_0(a), rho(b(a, a') g) xi>| = p_a(b(a, a') g)`.

**(3.1)** `Phi(a') = b(a', a) Phi(a)` for `(a', a) ∈ S|A_0`.

**Cohomology into a finite group.**
* `Q` acts on `Fin(Q)` by left translation, and `Fin(Q)` has countably many orbits `O`.
* By (3.1), each `{a : Phi(a) ∈ O}` is `S`-invariant, and one of them has positive measure. Replace `A_0` by it.
* Fix `P ∈ O`, and let `h(a)` be the first element, in a fixed enumeration of `Q`, with `Phi(a) = h(a) P`. Then `h` is
  Borel.
* By (3.1), `h(a') P = b(a', a) h(a) P`. So `h(a')^(-1) b(a', a) h(a)` lies in `K = {g : g P = P}`.
* `K` is finite: for `p_0 ∈ P`, the map `g ↦ g p_0` injects `K` into `P`.

This proves item 2 of the claim. □

**Restriction lemma.** Let `A_0 ⊆ A` be `S`-invariant with `zeta_A(A_0) > 0`. Then `S|A_0`, with `r|A_0` and the
normalized measure, is again a pmp class-bijective extension of `R`.
* The classes of `S|A_0` are full `S`-classes, so `r` stays class-bijective on them.
* For `theta ∈ [R]`, `theta~` preserves `A_0` and `zeta_A`, so `theta_* r_*(zeta_A|A_0) = r_*(zeta_A|A_0)`.
* This measure is `R`-invariant and absolutely continuous with respect to `mu`. By ergodicity of `R` it is
  `zeta_A(A_0) mu`. □

## Step 4. Down the normal series

**Lemma 4.1.** If `H ≤ G` has finite index and `H` is Haagerup, then `G` is Haagerup.

*Proof.* Let `phi_n` be witnesses for `H`, and let `phi_n'` be `phi_n` extended by `0` off `H`. The function
`phi_n'` is positive-definite on `G`: in `Σ c_k c̄_l phi_n'(x_l^(-1) x_k)`, only pairs in the same left coset
`xH` contribute, and those contributions form a positive sum for `phi_n`.

Write `phi_n' = <pi(.) eta, eta>`, and let `g_1, ..., g_m` represent `G/H`. Put
`psi_n(g) = (1/m) Σ_{i,j} phi_n'(g_i^(-1) g g_j)`. Then `psi_n(g) = <pi(g) eta~, eta~>/m` with
`eta~ = Σ_j pi(g_j) eta`, so `psi_n` is positive-definite.

We check the three properties:
* `psi_n(1) = 1`, because `g_i^(-1) g_j ∈ H` only for `i = j`.
* `psi_n` is `C_0`, because each `g ↦ g_i^(-1) g g_j` is proper and `phi_n'` is `C_0` on `G`.
* For fixed `g` and each `i`, exactly one `j` has `g_i^(-1) g g_j ∈ H`. Hence `psi_n(g) -> m/m = 1`. □

**Induction.** Let `c : S -> Lambda` be a cocycle, and let `1 = N_0 ≤ ... ≤ N_k = Lambda` be a normal series with
Haagerup quotients.

*Claim.* For `j = 0, ..., k` there are:
* an `S`-invariant `A_j` with `zeta_A(A_j) > 0`;
* a subgroup `Lambda_j ≤ Lambda` containing `N_(k−j)` with `[Lambda_j : N_(k−j)] < infinity`;
* a Borel `h_j : A_j -> Lambda` with `c_j(a', a) = h_j(a')^(-1) c(a', a) h_j(a) ∈ Lambda_j` on `S|A_j`.

*Proof.* For `j = 0`, take `A_0 = A`, `Lambda_0 = Lambda` and `h_0 = 1`.

Given stage `j < k`, let `q : Lambda_j -> Q_j = Lambda_j / N_(k−j−1)`. This quotient is defined because
`N_(k−j−1)` is normal in `Lambda`.
* `Q_j` contains `N_(k−j) / N_(k−j−1)`, which is Haagerup, with finite index. So `Q_j` is Haagerup by Lemma 4.1.
* By the restriction lemma, `S|A_j` is a pmp class-bijective extension of `R`. Apply item 2 (Steps 1–3) to
  `q ∘ c_j` on it. This gives `A_(j+1) ⊆ A_j`, a finite `K ≤ Q_j`, and `h`.
* Lift `h` to a Borel `h^ : A_(j+1) -> Lambda_j` using a section of `q` over the countable `Q_j`.
* Put `h_(j+1) = h_j h^` and `Lambda_(j+1) = q^(-1)(K)`. Then
  `[Lambda_(j+1) : N_(k−j−1)] = |K| < infinity`, and `c_(j+1)` takes values in `Lambda_(j+1)`. □

At `j = k`, the group `Lambda_k` is finite, since it contains `N_0 = 1` with finite index. So `c` restricted to
`S|A_k` is cohomologous, via `h_k`, to a cocycle `c_k` into the finite group `F = Lambda_k`.

## Step 5. Item 1: no dissipative cocycle

Suppose `c : S -> Lambda` is dissipative. Take `A_k`, `h_k` and `c_k` from Step 4.

**Transfer to the finite group.**
* The skew relation of `c` restricted to the invariant Borel set `A_k × Lambda` is still smooth.
* `Psi(a, lambda) = (a, h_k(a)^(-1) lambda)` is a Borel bijection of `A_k × Lambda`. It maps
  `(a', c(a', a) lambda)` to `(a', c_k(a', a) h_k(a)^(-1) lambda)`. So it carries the skew relation of `c` to that of
  `c_k`, and the skew relation of `c_k` is smooth.
* `c_k` takes values in `F`, so `Y = A_k × F` is invariant. The skew relation `E` of `c_k` on `Y` is smooth and
  preserves the finite measure `zeta_A × counting`, of total mass `zeta_A(A_k) |F| > 0`.

**`E` has infinite classes.** The class of `(a, g)` is `{(a', c_k(a', a) g) : a' ∈ [a]_S}`, which is in bijection
with `[a]_S`. That set is in bijection with `[r(a)]_R`, and this class is infinite a.e., since `L(R)` is a II_1
factor.

**Mass transport.**
* Let `T` be a Borel transversal of `E` on a conull invariant `Y' ⊆ Y`.
* By Lusin–Novikov, the Borel set `{(t, y) ∈ T × Y' : y E t}` has countable sections. So it is the union of
  disjoint graphs of Borel partial maps `f_n : T -> Y'`, with `n ∈ N`.
* Each `f_n` is injective, since `y` determines `t`. The images `f_n(T)` are pairwise disjoint.
* Each `f_n` has graph in `E`, so it preserves the invariant measure.
* Infinite classes make every `f_n` total on `T`. So `m(Y) ≥ Σ_n m(f_n(T)) = Σ_n m(T)`.

Since `m(Y) < infinity`, this forces `m(T) = 0`. Then `m(Y') = Σ_n m(f_n(T)) = 0`, a contradiction. So item 1
holds. □

## Step 6. Items 3 and 4, and the facts about the class

**Item 3.** Let `(Lambda ↷ (Z, zeta), A, S, r)` be a free host. Here `zeta` may be infinite.
* Discard a null `S`-saturated set on which the action is not free. Put `c(a', a) = ` the unique `lambda` with
  `lambda a = a'`. This is a Borel cocycle `S -> Lambda`.
* `S` preserves `zeta_A`, because `Lambda` preserves `zeta` and `S ⊆ R_Lambda(Z)`. So `S`, with `r`, is a pmp
  class-bijective extension of `R`.
* `Pi(a, lambda) = lambda^(-1) a` is constant on skew classes, since
  `(c(a', a) lambda)^(-1) a' = lambda^(-1) a`. Its fibers `{(lambda z, lambda)}` are countable.

A countable Borel relation contained in the fiber relation of a Borel map with countable fibers is smooth.
* By Lusin–Novikov, enumerate each fiber as `g_n(Pi(y))` with `g_n` Borel on the image set.
* Send `y` to `g_n(Pi(y))` for the least `n` with `g_n(Pi(y)) ~ y`. This is a Borel selector for the skew classes.

So `c` is dissipative, which contradicts item 1.

For a splitting `c : R -> Lambda` into a pmp action on `X` with `c(x, x') · x = x'`, item 2 of
`nonce-relation-hosts-force-root-or-q1-failure` gives a finite free host with actor `Lambda`. Alternatively, apply
the same `Pi` argument directly to `S = R` with the cocycle `(x', x) ↦ c(x, x')`. □

**Item 4.** `non-ce-property-t-equivalence-relation-exists` gives `R_T` ergodic pmp, with `L(R_T)` a property (T)
II_1 factor. So the theorem applies.

If a host with actor `Lambda` has `S ⊆ R_(Lambda')(Z)` for a subgroup `Lambda' ≤ Lambda`, then restricting the action
gives a host with actor `Lambda'`. So `Lambda'` is not normally poly-Haagerup either. □

**Facts about the class.**
* *Closed under subgroups.* For `H ≤ Lambda`, the groups `N_i ∩ H` are normal in `H`, and each quotient
  `(N_i ∩ H) / (N_(i−1) ∩ H)` embeds in `N_i / N_(i−1)`. The Haagerup property passes to subgroups.
* *No infinite (T) member.* Suppose `G` is (T) and normally poly-Haagerup. Then `G / N_(k−1)` is (T) and Haagerup,
  hence finite. So `N_(k−1)` has finite index and is (T). Inducting down the series, `G` is finite.
* *Membership of the listed examples.* Each example is Haagerup-by-Haagerup, using the chain `1 ≤ N ≤ Lambda`:
  * `Z^n ⋊ SL_2(Z)`, since `SL_2(Z)` is virtually free;
  * amenable-by-virtually-free groups;
  * free-by-cyclic groups.

  For `P_n`, the Fadell–Neuwirth kernels `ker(P_n -> P_(n−i))` are normal and have successive free quotients.

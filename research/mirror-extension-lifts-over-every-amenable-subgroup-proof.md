---
rg: 2
id: mirror-extension-lifts-over-every-amenable-subgroup-proof
kind: route
title: Untwist the full-group 2-cocycle of a set-theoretic lift by a fundamental-domain partition (finite case) or by the Popa-Shlyakhtenko-Vaes / Feldman-Sutherland-Zimmer cocycle vanishing for free cocycle actions on a Cartan pair (amenable case)
target: mirror-extension-lifts-over-every-amenable-subgroup
requires:
  - bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift
  - mirror-extension-splits-over-free-finite-by-free-subgroups
---

The notation is that of the target. [BL] means `bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift`, and
[SP] means `mirror-extension-splits-over-free-finite-by-free-subgroups-proof`, whose imports (I1)--(I4) are reused.

Throughout, `T` is an ergodic p.m.p. countable Borel equivalence relation on a standard atomless probability space
`(X, mu)`, and `[T] <= N <= N[T]`. The group `Lambda` is countable, `rho: Lambda -> N/[T]` is a homomorphism, and
`sigma: Lambda -> N` is a set-theoretic lift with `sigma(e) = 1`. Put
`c(g,h) = sigma(g) sigma(h) sigma(gh)^-1`, which lies in `[T]`.

For the mirror case take `T = T_-` and `N = N_-`. Here `T_-` is ergodic by (I3), and `[T_-] <= N_- <= N[T_-]` by
(I2) and [BL] Theorem 1.

**Fact 0.** Each `f ∈ N[T]` preserves `T`. So if `x T y` then `f x T f y`.

## 1. Finite `Lambda`: an elementary proof

Let `m = |Lambda|`.

**Step 1 (partition).** Choose a Borel partition `X = ⊔_{g ∈ Lambda} D_g` with `mu(D_g) = 1/m`. This exists because
`mu` is atomless. Put `D = D_e`.

**Step 2 (matching).** Fix `g`. Since `sigma(g)` preserves `mu`, `mu(sigma(g) D) = 1/m = mu(D_g)`.
* By (I4) (Kechris--Miller, Lemma 7.10) choose `theta_g ∈ [[T]]` with domain `sigma(g) D` and range `D_g`. Take
  `theta_e = id_D`.
* Put `phi_g = theta_g ∘ sigma(g)|_D : D -> D_g`. It is a measure-preserving Borel bijection, and
  `phi_g(d) T sigma(g) d` for a.e. `d`.

**Step 3 (the action).** For `h ∈ Lambda` define `alpha(h)` by `alpha(h)(phi_g d) = phi_{hg} d`, for `d ∈ D`.
* On `D_g`, `alpha(h)` equals `phi_{hg} phi_g^-1 : D_g -> D_{hg}`. The pieces are measure-preserving, and
  `g -> hg` permutes the index set, so `alpha(h)` is a p.m.p. automorphism of `X`.
* `alpha(h) alpha(k) (phi_g d) = alpha(h)(phi_{kg} d) = phi_{hkg} d = alpha(hk)(phi_g d)`, so `alpha` is a
  homomorphism.
* For `h != e`, `alpha(h)` maps `D_g` onto the disjoint set `D_{hg}`, so the action is free.

**Step 4 (right coset).** Let `x = phi_g d`. Then:
* `alpha(h) x = phi_{hg} d T sigma(hg) d`, by Step 2.
* `sigma(h) x T sigma(h) sigma(g) d`, by Fact 0 applied to `x T sigma(g) d`.
* `sigma(h) sigma(g) d = c(h,g) sigma(hg) d T sigma(hg) d`, since `c(h,g) ∈ [T]`.

So `alpha(h) x T sigma(h) x` for a.e. `x`. By Fact 0 for `sigma(h)^-1`, `sigma(h)^-1 alpha(h) x T x` a.e. This gives
`sigma(h)^-1 alpha(h) ∈ [T]`, hence `alpha(h) ∈ sigma(h)[T] ⊂ N`, and `alpha` lifts `rho`.

No hyperfiniteness, outerness or injectivity of `rho` was used. This settles (FL). QED(finite).

## 2. Imported theorem

**(I5)** (Popa--Shlyakhtenko--Vaes, *Cohomology and L^2-Betti numbers for subfactors and quasi-regular inclusions*,
arXiv:1811.06929v2, Theorem 5.2.) Verbatim:

> "Let G be a discrete measured groupoid with Y = G(0) and (Ay ⊂ By)y∈Y a measurable field of Cartan subalgebras in
> II1 factors with separable predual. Assume that G is amenable. When (α,u) is a free cocycle action of G on
> (Ay ⊂ By)y∈Y, the cocycle u is a co-boundary: there exists a measurable field of unitaries G ∋ g ↦ wg ∈ N_{Bt(g)}(At(g))
> such that u(g,h) = αg(w∗h)w∗g wgh for all (g,h) ∈ G(2)."

The definitions it uses are PSV Definition 2.2 and the Cartan setup of Section 5:
* A cocycle action satisfies `α_g ∘ α_h = Ad(u(g,h)) ∘ α_gh` and `α_g(u(h,k)) u(g,hk) = u(g,h) u(gh,k)`, with the
  normalizations `α_e = id` and `u(e,h) = u(g,e) = 1`.
* In the Cartan setting, `α_g(A) = A` and `u(g,h) ∈ N_B(A)`.
* The action is free if `α_g` is free for isotropy elements `g != e`. PSV: "An automorphism α of a von Neumann
  algebra B is said to be free (or properly outer) if the only element v ∈ B satisfying vx = α(x)v for all x ∈ B is
  the zero element v = 0."

PSV note that for groups this is classical: "These results were so far only known for amenable groups (see
[FSZ88, Theorem 3.4], [BG84, Theorem 3.4] and [GS86])." The group case is Feldman--Sutherland--Zimmer, *Subrelations
of ergodic equivalence relations*, ETDS 9 (1989), 239--269. Its abstract reads: "in the case where Q is amenable, one
can work with a genuine action." Only the group case, `G = Lambda` with a one-point unit space, is used below.

**(I6)** (Feldman--Moore.) `A = L^∞(X) ⊂ B = L(T)` is a Cartan subalgebra.
* `B` is a II_1 factor with separable predual, because `T` is ergodic with a.e. infinite classes (`mu` atomless).
* Elements of `L(T)` are identified with `L^2`-functions `v(x,y)` on `T`. The product is
  `(vw)(x,z) = Σ_y v(x,y) w(y,z)`, and `a ∈ A` acts by `(av)(x,y) = a(x) v(x,y)` and `(va)(x,y) = v(x,y) a(y)`.
* `u_phi(x,y) = 1_{y = phi^-1 x}` for `phi ∈ [T]`, so that `u_phi u_psi = u_{phi psi}` and
  `u_phi a u_phi^* = a ∘ phi^-1`.

## 3. Amenable `Lambda`

**Step 0 (reduce to injective `rho`).** Let `K = ker rho`. Then `Lambda/K` is countable and amenable. A lift of the
induced injective map `Lambda/K -> N/[T]`, composed with `Lambda -> Lambda/K`, lifts `rho`. So assume `rho` is
injective. Then `sigma(g) ∉ [T]` for `g != e`.

**Step 1 (the cocycle action).** Each `f ∈ N[T]` defines an automorphism `alpha_f` of `B` by
`alpha_f(a) = a ∘ f^-1` on `A` and `alpha_f(u_phi) = u_{f phi f^-1}`.
* `alpha_f` preserves the trace and `A`, and `alpha_f alpha_f' = alpha_{f f'}`.
* For `phi ∈ [T]`, `alpha_phi = Ad(u_phi)`.

Put `alpha_g = alpha_{sigma(g)}` and `u(g,h) = u_{c(g,h)} ∈ N_B(A)`. Then:
* `alpha_g alpha_h = alpha_{c(g,h) sigma(gh)} = Ad(u(g,h)) alpha_gh`.
* `alpha_g(u(h,k)) u(g,hk) = u_{sigma(g) c(h,k) sigma(g)^-1 c(g,hk)}`. Here
  `sigma(g) c(h,k) sigma(g)^-1 c(g,hk) = sigma(g) sigma(h) sigma(k) sigma(ghk)^-1 = c(g,h) c(gh,k)`, which is the
  cocycle identity.
* The normalizations hold because `sigma(e) = 1`.

**Step 2 (freeness).** Fix `g != e`, put `theta = sigma(g) ∉ [T]`, and suppose `v x = alpha_theta(x) v` for all
`x ∈ B`.
* Taking `x = a ∈ A` gives `v(x,y) a(y) = a(theta^-1 x) v(x,y)`. Over a countable separating family of `a`, it
  follows that `v(x,y) != 0` implies `y = theta^-1 x`.
* So `v` is supported on `{(x, theta^-1 x) : x ∈ E}`, where `E = {x : theta^-1 x T x}`.
* `E` is `T`-invariant by Fact 0: if `x' T x ∈ E`, then `theta^-1 x' T theta^-1 x T x T x'`. By ergodicity `E` is
  null or conull.
* If `E` were conull, then `theta^-1 ∈ [T]`, contradicting `theta ∉ [T]`. So `E` is null and `v = 0`.

Hence `alpha_g` is free. `Lambda` is its own isotropy group, so `(alpha,u)` is a free cocycle action of the amenable
(one-unit) groupoid `Lambda` on the Cartan pair `A ⊂ B`.

**Step 3 (vanishing).** By (I5) there are `w_g ∈ N_B(A)` with `u(g,h) = alpha_g(w_h^*) w_g^* w_gh`. Put
`beta_g = Ad(w_g) alpha_g`. Then
`beta_g beta_h = Ad(w_g alpha_g(w_h) u(g,h)) alpha_gh`, and
`w_g alpha_g(w_h) u(g,h) = w_g alpha_g(w_h) alpha_g(w_h^*) w_g^* w_gh = w_gh`.
So `beta` is a genuine action of `Lambda` preserving `A`.

**Step 4 (normalizers are full-group elements).** Let `w ∈ N_B(A)`.
* `Ad(w)|_A` is a trace-preserving automorphism of `L^∞(X)`, so `Ad(w)(a) = a ∘ psi^-1` for a p.m.p. `psi`.
* As in Step 2, `w(x,y) != 0` implies `y = psi^-1 x`.
* Then `1 = (w w^*)(x,x) = |w(x, psi^-1 x)|^2 1_{psi^-1 x T x}` a.e. So `psi^-1 x T x` a.e., and `psi ∈ [T]`.

**Step 5 (point maps).** Write `Ad(w_g)|_A = (a -> a ∘ psi_g^-1)` with `psi_g ∈ [T]`. Then
`beta_g(a) = a ∘ tau_g^-1`, where `tau_g = psi_g sigma(g) ∈ [T] sigma(g) = sigma(g)[T] ⊂ N`.
* `beta` is an action and point realizations are unique a.e., so `tau_{gh} = tau_g tau_h` a.e. for all pairs.
* `Lambda` is countable, so restricting to a conull `tau`-invariant set gives a homomorphism `tau: Lambda -> N`
  with `tau_g [T] = rho(g)`.

QED(amenable).

## 4. Consequences for the hole

* Every amenable subgroup of `Q = SL_n(F_2[x,x^-1])` is countable. For such a subgroup take `T = T_-`, `N = N_-`,
  and `rho` the inclusion followed by `Q ≅ N_-/[T_-]` ([BL] Theorem 1).
* The diagonal torus is `≅ Z^(n-1)`, because the units of `F_2[x,x^-1]` are `x^k`. The unipotent upper-triangular
  group is nilpotent, and the Borel subgroup is solvable. All of these lift.
* Combined with [SP] parts 3 and 5 (graphs of finite groups; locally finite subgroups), (HS) holds over every f.g.
  virtually free and every amenable subgroup.
* The cocycle `[c] ∈ H^2(Lambda; [T_-])`, twisted by `Ad sigma`, therefore vanishes on all such `Lambda`. A failure
  of (HS) for `Q` can only come from a non-amenable, non-virtually-free subgroup.

## 5. What is left: a gluing decomposition (proposed, not proved)

* **(G1)** For each Weyl element `w`, the unipotent group `U_w = w U^+ w^-1` lifts by Section 3 (it is nilpotent).
  Every Steinberg relation `[x_ij(a), x_jk(b)] = x_ik(ab)` for `i,j,k` distinct lives in some `U_w`.
* **(G2)** (HS) for `St_n(A)` is equivalent to choosing the `n!` lifts `tau_w` compatibly on shared root groups
  `X_ij`. This is a Čech-type gluing over the Coxeter complex. The relative cocycles live in the normalizer of the
  lifted root groups inside `[T_-]`, and property (T) of `Q` must enter here.
* **(G3)** Passing from `St_n(A)` to `Q` needs `K_2(n, A) = 0` or a lift of its image. `K_2(F_2[x,x^-1]) = 0` by
  the fundamental theorem, but stability injectivity `K_2(n,A) -> K_2(A)` for `n >= 3` is not verified here.

Each of (G1)--(G3) can fail on its own. (G1) is now established.

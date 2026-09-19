---
rg: 2
id: jacobson-haar-orbit-relation-summand-proof
kind: route
title: Compute the rank of an affine element, split the Haar character by whether the translation lies in the image, and cut the orbit-relation summand out by a central projection
target: jacobson-haar-character-restricts-to-orbit-relation-summand
requires:
  - leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity
  - jacobson-el-characters-are-symbol-or-finitary-extensions
  - gl-infinity-f2-trace-simplex-is-extended-naturals
---

Notation is as in the claim. Throughout, `[P]` is `1` if `P` holds and `0` otherwise. For a subspace
`W <= V_n`, `W^⊥ = {xi in X_n : xi|_W = 0}`.

## 1. The affine subgroup and the rank formula

**Lemma 1.1 (ring facts).**
1. `QS = 0`, `TQ = 0`, and `QJQ = F_2 Q`.
2. `JQ` is a left ideal with `F_2`-basis `S^k Q`, `k >= 0`, and `Q (sum_k c_k S^k Q) = c_0 Q`.

*Proof.*
* `QS = S - STS = 0` and `TQ = T - TST = 0`, using `TS = 1`.
* Every element of `J` is a sum of monomials `S^a T^b`. For `(a,b) != (0,0)`, `Q S^a T^b Q = 0` by the
  first bullet, so `QJQ = F_2 Q`.
* `J Q` is spanned by `S^a T^b Q`, and `T^b Q = 0` for `b >= 1`. So `JQ` is spanned by the `S^a Q`, which are
  independent because `J` has basis `S^a T^b`.
* Part 2 follows from `Q S^k Q = 0` for `k >= 1` and `QQ = Q`. `□`

**Lemma 1.2 (affine subgroup).** For `g in E_n` and `v in V_n` put `h(v,g) = [[g, v],[0, 1]]`, an
`(n+1) x (n+1)` matrix over `J`. Then:
1. `h(v,g) in E_(n+1)`.
2. `h(v,g) h(w,k) = h(v + g w, g k)`.
3. `A_n = {h(v,g)}` is a subgroup isomorphic to `V_n x| E_n`, where `E_n` acts on `V_n` by left multiplication.

*Proof.*
* `h(v,g) = h(v,1) h(0,g)`. Here `h(0,g)` is the image of `g` under the corner embedding
  `EL_n(J) -> EL_(n+1)(J)`, and `h(v,1) = prod_i x_(i,n+1)(v_i)` is a product of elementary matrices.
* The product formula is matrix multiplication.
* `g V_n ⊆ V_n` because `JQ` is a left ideal. So `A_n` is closed under products, and
  `h(v,g)^(-1) = h(-g^(-1) v, g^(-1))`. `□`

**Lemma 1.3 (action and rank).** Write `y in JQ` as `y = sum_k c_k(y) S^k Q`. Then `h = h(v,g)` acts on
`V_(n+1) = V_n ⊕ JQ` by

```text
h (x ; y) = (g x + c_0(y) v ; y).                                                    (1.1)
```

Hence:
* `Im(h - 1) = Im(g - 1) + F_2 v`.
* `h in L_(n+1)` iff `g in L_n`.
* For `g in L_n`, `rank(h - 1) = rank(g - 1) + [v notin Im(g - 1)]`.

*Proof.*
* The row `(0, 1)` gives `y -> y`.
* The first block row gives `g x + v y`. By Lemma 1.1, `v_i y = v_i Q y = c_0(y) v_i`, since `v_i = v_i Q`.
* So `(h - 1)(x ; y) = ((g-1)x + c_0(y) v ; 0)`. Taking `y = Q` and `x` free gives the image formula.
* `h - 1` has finite rank iff `g - 1` does.
* By (JH2), an element `k` of `E_n` lies in `L_n` iff `mu(Fix k) > 0`. Here `Fix k = Im(k - 1)^⊥` (Section 3),
  and this has positive measure iff `rank(k - 1) < ∞`. So `L_n` is exactly the set of `k in E_n` with
  `rank(k - 1) < ∞`, and the same holds at rank `n+1`. `□`

## 2. The splitting (AS1)

Fix `m in {1,...,∞}` and `h = h(v,g)`. Write `r = rank(g - 1)`. Use the conventions `2^(-m r) = 0` if
`r = ∞`, or if `m = ∞` and `r > 0`, and `2^(-∞ * 0) = 1`.

* If `g notin L_n`, then `h notin L_(n+1)` (Lemma 1.3), so both sides of (AS1) vanish.
* If `g in L_n` and `v in Im(g-1)`, then `rank(h-1) = r`. The left side is `2^(-mr)`. The right side is
  `(1 - 2^(-m)) 2^(-mr) + 2^(-m) 2^(-mr) = 2^(-mr)`.
* If `g in L_n` and `v notin Im(g-1)`, then `rank(h-1) = r + 1`. The left side is `2^(-m(r+1))`. The right
  side is `0 + 2^(-m) 2^(-mr)`.

This proves (AS1). For `m = ∞` it reads `delta_e|_(A_n) = psi_∞`, with `psi_∞ = delta_e^(A_n)`.

**`psi_m` is a trace.**
* The case `m = 1` is Section 3: there `psi_1` is the trace of a tracial von Neumann algebra composed with a
  unitary representation.
* For `2 <= m < ∞`,

```text
psi_m = psi_1 * ((e sigma_(m-1)^(n)) o pr),                                           (2.1)
```

  a pointwise product of two traces on `A_n`, hence a trace.
* (2.1) is checked pointwise. If `g in L_n`, both sides are `2^(-r) [v in Im(g-1)] 2^(-(m-1) r)`. Otherwise
  both vanish.
* The product is realized by the tensor product of the two GNS representations, so
  `W*(A_n, psi_m) ⊆ L(R_n) ⊗̄ W*(E_n, e sigma_(m-1))`.
* For `m = ∞`, `psi_m = delta_e`.

## 3. The orbit-relation trace

**Action and fixed sets.**
* `E_n` acts on `X_n` by `(g.xi)(x) = xi(g^(-1) x)`. The action is by continuous automorphisms, so it
  preserves `mu`.
* `g.xi = xi` iff `xi o (g^(-1) - 1) = 0`, that is, iff `xi in Im(g^(-1) - 1)^⊥`.
* `g^(-1) - 1 = -(g - 1) g^(-1)` and `g^(-1)` is bijective, so `Im(g^(-1) - 1) = Im(g - 1)`.
  Hence `Fix g = Im(g-1)^⊥`.
* Let `W` have dimension `d < ∞`. Then `X_n / W^⊥ ≅ Hom(W, F_2)`, so `mu(W^⊥) = 2^(-d)`.
* If `d = ∞`, then `W^⊥` lies in closed subgroups of every index `2^k`, so `mu(W^⊥) = 0`.

**Fourier computation.** Put `chi_v(xi) = (-1)^(xi(v))`. Then

```text
∫_(Fix g) chi_v dmu = mu(Im(g-1)^⊥) [v in Im(g-1)^(⊥⊥)] = psi_1(v, g).                (3.1)
```

* A character integrates over a closed subgroup `H` to `mu(H)` if it is trivial on `H`, and to `0`
  otherwise.
* `chi_v` is trivial on `W^⊥` iff `v in W^(⊥⊥)`.
* By Pontryagin duality for the discrete group `V_n` and its compact dual `X_n`, `W^(⊥⊥) = W` for every
  subgroup `W <= V_n`.
* If `g notin L_n`, then `mu(Fix g) = 0` and both sides of (3.1) vanish (Lemma 1.3).
* If `g in L_n`, (3.1) reads `2^(-r) [v in Im(g-1)] = psi_1(v,g)`.

**The representation.**
* `L(R_n)` is the von Neumann algebra of the orbit relation of `E_n ↷ (X_n, mu)`. It has its canonical
  faithful normal trace `tau`.
* It contains `L^∞(X_n)` and the unitaries `u_g` given by the graphs of the maps `g`, with
  `u_g f u_g^* = f o g^(-1)` and `tau(f u_g) = ∫_(Fix g) f dmu` (Feldman--Moore).
* It is generated by `L^∞(X_n)` and `{u_g}`, since `R_n` is generated by the countable group `E_n`.
* `(chi_v o g^(-1))(xi) = (-1)^(xi(g v)) = chi_(gv)(xi)`, so `u_g chi_v u_g^* = chi_(g v)`.
* Hence `pi(v, g) = chi_v u_g` satisfies

```text
pi(v,g) pi(w,k) = chi_v chi_(g w) u_g u_k = chi_(v + g w) u_(gk) = pi(v + g w, g k).
```

  This is a unitary representation of `A_n` (Lemma 1.2).
* By (3.1), `tau o pi = psi_1`. So `psi_1` is a trace, and `W*(A_n, psi_1) ≅ pi(A_n)''` because `tau` is
  faithful.
* The `chi_v` span a weak*-dense subalgebra of `L^∞(X_n)` (Stone--Weierstrass on the compact group `X_n`).
  So `pi(A_n)'' = L(R_n)`.

**Ergodicity.**
* The dual action of `L_n` on `V_n` is its defining action.
* `L_n = GL_fin` is transitive on the infinite set `V_n \ {0}`.
* An action by automorphisms of a compact abelian group is ergodic iff every nontrivial dual orbit is
  infinite. So `L_n`, and hence `E_n`, acts ergodically.
* `mu` is nonatomic, so `R_n` is an ergodic type `II_1` relation and `L(R_n)` is a `II_1` factor.

This proves part 3 of the theorem.

## 4. Convex summands of CE traces

**Lemma 4.1.** Let `H` be a countable group and `tau = t tau_1 + (1 - t) tau_2` with traces `tau_i` and
`0 < t <= 1`. If `tau` is CE, then `tau_1` is CE.

*Proof.*
* Let `M = W*(H, tau)` with GNS unitaries `lambda(h)` and faithful trace `tau`.
* For `a in C[H]`, `tau_1(a^* a) <= t^(-1) tau(a^* a)`. So `a Omega -> a Omega_1` extends to a bounded
  operator, and `tau_1` extends to a normal positive functional `omega_1 <= t^(-1) tau` on `M`.
* `omega_1` is tracial on the weak*-dense algebra `C[H]`, hence on `M` by normality.
* Radon--Nikodym: `omega_1 = tau(z .)` with `0 <= z <= t^(-1)`. Traciality forces `z in Z(M)`.
* Let `p` be the support of `z`. The map `lambda(h) -> lambda(h) p` identifies the GNS algebra of `tau_1`
  with `(M p, tau(z .))`, on which `tau(z .)` is faithful. So it suffices to show that `(M p, tau(z .))` is
  CE.
* `M p` is a corner of the CE algebra `M`. Put `tau_p = tau(. p)/tau(p)`.
  * Embed `M ⊆ R^omega`. Then `p R^omega p` is again an ultrapower of the hyperfinite factor: represent `p`
    by projections `p_k in R` of trace `tau(p)`, and use `p_k R p_k ≅ R`.
  * So `(M p, tau_p)` is CE.
* **Change of trace.** Let `z_j = sum_i c_(ij) q_(ij)` be central step functions with rational `c_(ij) > 0`,
  converging to `z p` in norm on `M p`. Here `sum_i q_(ij) = p`.
  * Each `(M q_(ij), tau_(q_(ij)))` is CE, by the corner argument.
  * A finite direct sum of CE algebras with any weights is CE: choose orthogonal projections in
    `R^omega` with the prescribed traces, and embed the summands in the corresponding corners.
  * So `(M p, tau(z_j .)/tau(z_j))` is CE for each `j`.
  * These traces converge in norm to `tau(z .)/tau(z)`. So the `*`-moments of the generators
    `lambda(h) p` converge uniformly on words of bounded length.
  * CE is equivalent to matricial approximability of all `*`-moments of a generating set, and that property
    passes to such limits. Hence `(M p, tau(z .))` is CE. `□`

## 5. The sandwich (AS3) and the stable equivalence

**Step 1: `m in S_(n+1)` implies `P_n(m)`.**
* Let `m < ∞` with `e sigma_m^(n+1)` CE on `E_(n+1)`.
* The restriction of a CE trace to a subgroup is CE, because `W*(A_n, tau|) ⊆ W*(E_(n+1), tau)`. So the
  left side of (AS1) is CE on `A_n`.
* (AS1) writes it as `t psi_m + (1-t) tau_2` with `t = 1 - 2^(-m) > 0` and
  `tau_2 = (e sigma_m^(n)) o pr`.
* Lemma 4.1 gives `psi_m` CE.
* For `m = ∞`, `psi_∞ = delta_e^(A_n)` is the restriction of `delta_e^(E_(n+1))`.

**Step 2: `P_n(m)` implies `m in S_n`.**
* `E_n` embeds in `A_n` as `g -> h(0, g)`.
* `psi_m(0, g) = e sigma_m^(n)(g) [0 in Im(g-1)] = e sigma_m^(n)(g)`.
* Restriction to this subgroup gives `e sigma_m^(n)` CE.

**Consequences.**
* With `m = 1`, part 3 turns `P_n(1)` into "`L(R_n)` is CE".
* (JH3) of `leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity` turns `1 in S_n` into
  hyperlinearity of `E_n`.
* **Stable equivalence.** If `1 in S_n` for all `n`, then `P_n(1)` for all `n` by Step 1 at `n+1`.
  Conversely, `P_n(1)` for all `n` gives `1 in S_n` for all `n` by Step 2. `□`

## Remarks

**Remark 1 (numerical check).** `experiments/jacobson-affine-sandwich-2026-09-17/check_affine_rank_split.py`
checks the following over `F_2`:
* the rank formula of Lemma 1.3;
* (AS1) for `m = 1, 2, 3`;
* (3.1);
* positive semidefiniteness of `psi_1` and `psi_2`.

The script works in the finite affine groups `F_2^k x| GL_k(F_2)` for `k <= 3`. There
`rank(h-1) = rank(g-1) + [v notin Im(g-1)]` is the same linear algebra, since `h` acts on `F_2^(k+1)` by
`(x, y) -> (g x + y v, y)`.

**Remark 2 (where the Laurent symbol enters).** The summand `(e sigma_m^(n)) o pr` is pulled back from the
quotient `A_n -> E_n`. The summand `psi_m` is not. `psi_1` is supported on the set of `(v,g)` with
`g in L_n` and `v in Im(g - 1)`. That set is the union over `g in L_n` of the cosets `(Im(g-1), g)`. So
`psi_1` is a genuinely affine trace, and its GNS algebra is the whole orbit-relation algebra rather than a
group algebra of `E_n`.

**Remark 3 (the higher `psi_m`).** For `2 <= m < ∞` let `E_n` act diagonally on `X_n^m`. Then

```text
psi_m(v, g) = ∫_(Fix_(X_n^m) g) chi_v(xi_1) dmu^m(xi),
```

since `Fix_(X_n^m) g = (Fix g)^m`. So `(v, g) -> (chi_v ⊗ 1) u_g` realizes `psi_m`, and
`W*(A_n, psi_m) = {L^∞(X_n) ⊗ 1, u_g : g in E_n}''` inside `L(R(E_n ↷ X_n^m))`.

**Remark 4 (structure of `L(R_n)`).**
* *The `L_n`-orbits are the tail classes.* Take `xi` with infinitely many nonzero coordinates, which holds
  for `mu`-almost every `xi`. The `L_n`-orbit of `xi` is the set of `xi'` that differ from `xi` in finitely
  many coordinates `xi(e_i)`.
  * `xi o h` changes only the coordinates of the finitely many `e_i` moved by `h in L_n`.
  * Conversely, suppose `xi'` differs from `xi` on a finite set `F`. Choose `j notin F` with `xi(e_j) = 1`,
    and let `h` fix the `e_k` with `k notin F` and send `e_i -> e_i + e_j` for `i in F`. Then `h in L_n` and
    `xi o h = xi'`.
  * So `R(L_n) = E_0` is the hyperfinite tail relation on `{0,1}^(N x n)`, and `L(R(L_n)) ≅ R`.
* *The quotient acts freely.* Let `g notin L_n`. The set `{xi : g.xi in L_n.xi}` is the countable union of
  the sets `Fix(k^(-1) g)`, `k in L_n`. Each is null, because `k^(-1) g notin L_n` (Section 3).
* *Consequence.* `R(L_n)` is a normal subrelation of `R_n` whose quotient `E_n / L_n = EL_n(F_2[z^(±1)])` acts
  freely. So `L(R_n)` is graded over `EL_n(F_2[z^(±1)])` with trace supported on the identity grade, that is,
  a cocycle crossed product `R ⋊_(α,c) EL_n(F_2[z^(±1)])`.
* This is the object at which the w4 entropy-measure transplant stopped: amenable kernel, sofic Kazhdan
  quotient.
* It contains the GNS algebra of `phi_1`, which is also of the form `R ⋊ EL_n(F_2[z^(±1)])`
  (`jacobson-el-characters-are-symbol-or-finitary-extensions`, "What this does not give").
* Whether that containment is proper is not decided here, and nothing above uses it. At finite stages it
  is proper: in `GL_k(F_2)` acting on `F_2^k`, the permutation unitaries generate a proper subalgebra of
  the orbit-relation algebra `C ⊕ M_(2^k - 1)`.




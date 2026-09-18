---
rg: 2
id: entropy-profile-proofs-of-bernoulli-maximality-relativize-proof
kind: route
title: Approximate a relative generator by a side-informed local code and read off its conditional entropy profile
target: entropy-profile-proofs-of-bernoulli-maximality-relativize
requires:
  - bernoulli-rokhlin-deficit-has-a-finitary-witness
---

Complete direct proof. The notation is that of the target claim.
- `G` is countably infinite, `|A| = q`, `k >= 1`.
- `X = (A^k)^G` carries the uniform product measure `μ`, and `(g·x)(a) = x(g^-1 a)`.
- `G ↷ (Ω, ν)` is any p.m.p. action on a standard probability space, and `Z = X × Ω` carries the diagonal action and `μ × ν`.
- Partitions are countable and measurable. For a partition `P` and `g in G`, `g·P = {g p : p in P}`, and `P_F = ∨_(f in F) f·P`.

## 0. Relative Rokhlin entropy and invariant sets

`h_G(Z | B(Ω))` is the infimum of `H(P | B(Ω) ∨ I)` over partitions `P` with `σ(G·P) ∨ B(Ω) ∨ I = B(Z)`. Here `I` is the σ-algebra of `G`-invariant sets, as in Seward's definition (`seward-weak-containment-relative-entropy-equality`).

**Lemma 0.** `I ⊆ B(Ω)` mod null sets. So `h_G(Z | B(Ω)) = inf { H(P | B(Ω)) : σ(G·P) ∨ B(Ω) = B(Z) }`.

*Proof.*
- **Decomposition.** `L²(Z) = L²(Ω) ⊕ (L²_0(X) ⊗ L²(Ω))`, and both summands are invariant.
- **The first summand is mixing.** Fix an orthonormal basis `1 = e_0, e_1, …, e_(q^k - 1)` of `L²(A^k)`. The products `χ_(S,c) = ∏_(a in S) e_(c(a))(x(a))`, over finite nonempty `S ⊂ G` and labels `c : S -> {1, …, q^k - 1}`, form an orthonormal basis of `L²_0(X)`, and `G` permutes them. The stabilizer of `(S, c)` fixes the finite set `S` setwise, so it is finite. Hence `L²_0(X) = ⊕ ℓ²(G/K_i)` with every `K_i` finite, and every matrix coefficient of this representation `ρ` vanishes at infinity.
- **No finite-dimensional subrepresentation.** Suppose `V` is a nonzero finite-dimensional invariant subspace and `v in V` a unit vector. The closure of `ρ(G)|_V` in `U(V)` is compact. Fix a finite `K ⊂ G` and `ε > 0`. Cover that closure by finitely many balls of radius `ε/2`. Since `G` is infinite, some ball contains `ρ(g_0)|_V, …, ρ(g_N)|_V` for distinct `g_0, …, g_N` with `N > |K|`. The elements `g_0^-1 g_j`, `1 <= j <= N`, are distinct, so one of them, `h`, lies outside `K`, and `‖ρ(h)|_V - id‖ < ε`. So `⟨ρ(h)v, v⟩` does not tend to `0` along `h -> ∞`, contradicting vanishing at infinity. So `ρ` is weakly mixing.
- **No invariant vectors in the product.** A `G`-invariant vector of `ρ ⊗ π` is a Hilbert–Schmidt operator intertwining `π̄` with `ρ`. Its range, the closure of the image of the positive compact operator `T T*`, contains a nonzero finite-dimensional invariant eigenspace of `TT*` inside `ρ`, which does not exist. So every invariant `f in L²(Z)` lies in `L²(Ω)`. ∎

## 1. The side-informed profile

Let `Q` be a finite partition of `Z` measurable with respect to `σ(x|_E) ∨ B(Ω)` for a finite `E ⊂ G`. Write `Q = {q_1, …, q_n}` and `q_i = {(x, ω) : ψ(ω, x|_E) = i}` for a measurable `ψ : Ω × (A^k)^E → [n]`.

**Variables on `Z`.**
- `x_a(z) = x(a)`.
- `y_a(z) = i` exactly when `z in a·q_i`, that is, when `a^-1 z in q_i`. Since `(a^-1·x)(e) = x(a e)`, this gives `y_a = ψ(a^-1 ω, (x(ae))_(e in E))`. So `y_a` is a function of `x_(aE)` and `ω`.

**The profile.** For a finite set `S` of variables put `h_Ω(S) = H(S | B(Ω))`.

**Lemma 1.** `h_Ω` satisfies (H1)–(H5).

*Proof.*
- **(H1).** Let `(μ × ν)_w`, for `w in Ω`, be the disintegration of `μ × ν` over `Ω`. For finite-valued `S`, `H(S | B(Ω)) = ∫ H_((μ×ν)_w)(S) dν(w)`, and each integrand is an entropic vector on the finite ground set. The closure of the entropic cone on a finite ground set is a closed convex cone (Zhang–Yeung), so the integral lies in it.
- **(H2).** `T_g(z) = g z` preserves `μ × ν` and maps `B(Ω)` onto itself. It carries `x_a` to `x_(g^-1 a)` and `y_a` to `y_(g^-1 a)`, because `(a·q_i) = g·((g^-1 a)·q_i)`. So `H(gS | B(Ω)) = H(S | T_g^-1 B(Ω)) = H(S | B(Ω))`.
- **(H3).** `x` is independent of `ω`, and its coordinates are iid uniform on `A^k`.
- **(H4).** `y_g` is a function of `x_(gE)` and `ω`.
- **(H5).** Condition on `ω` and on `x_W`. Then `S` is a function of the coordinates `x` on `supp S \ W`, and `T` is a function of `x` on `supp T \ W`. These sets are disjoint. The coordinates are independent of each other and of `ω`, so `I(S ; T | x_W, B(Ω)) = 0`. ∎

**Remark 2 (auxiliary fields).** Suppose a proof adjoins an iid label field `U = (u_a)` independent of `(x, y)` and extends (H1)–(H5) with `supp u_a = {a}'`, a separate coordinate. Adjoin `U` to `Z` independent of `(x, ω)`. The argument of Lemma 1 applies verbatim, so Theorem 3 holds for that extended class too.

## 2. Approximation of a relative generator

**Theorem 3.** `rho^prof_q(G) <= h_G(Z | B(Ω)) / k`.

*Proof.* Suppose `P` is a partition with `σ(G·P) ∨ B(Ω) = B(Z)` and `H(P | B(Ω)) < ∞`. Fix `δ > 0`. It suffices to find `E`, `F` and `Q` as in Section 1 with

    h_Ω(y_1) + h_Ω(x_1 | y_F) <= H(P | B(Ω)) + 3δ.

**Step 1: choose `F`.** The σ-algebras `σ(P_F) ∨ B(Ω)` increase along finite `F ↑ G`, and they generate `B(Z)`. The coordinate `x_1` is a finite partition. By the martingale convergence theorem for conditional entropy, there is a finite `F` with `H(x_1 | P_F ∨ B(Ω)) < δ`. Fix `F`.

**Step 2: coarsen `P`.** Let `P = {p_1, p_2, …}` and `P_n = {p_1, …, p_n, ∪_(j>n) p_j}`. The σ-algebras `σ(P_n) ∨ B(Ω)` increase to `σ(P) ∨ B(Ω)`, and `H(P | B(Ω)) < ∞`. So `H(P | P_n ∨ B(Ω)) → 0`. Choose `n` with `|F| H(P | P_n ∨ B(Ω)) < δ/2`.

**Step 3: localize.** `σ(x|_E) ∨ B(Ω)` increases to `B(Z)` as `E ↑ G`. The `n+1` atoms of `P_n` can therefore be approximated in measure by sets in `σ(x|_E) ∨ B(Ω)` for a large finite `E`. Correct overlaps to get a partition `Q` with the same index set, measurable in that σ-algebra, and `μ×ν(P_n Δ Q) < ε`. By Fano's inequality,

    H(P_n | Q ∨ B(Ω)) <= h_2(ε) + ε log(n+1)   and   H(Q | P_n ∨ B(Ω)) <= h_2(ε) + ε log(n+1).

Choose `ε` so that both are below `δ/(2|F| + 2)`.

**Step 4: estimate.**
- **The first term.** `h_Ω(y_1) = H(Q | B(Ω)) <= H(P_n | B(Ω)) + H(Q | P_n ∨ B(Ω)) <= H(P | B(Ω)) + δ`.
- **The second term.** `h_Ω(x_1 | y_F) = H(x_1 | Q_F ∨ B(Ω))`. It is at most

      H(x_1 | P_F ∨ B(Ω)) + H(P_F | Q_F ∨ B(Ω))
        <= δ + ∑_(f in F) H(f·P | f·Q ∨ B(Ω))
        =  δ + |F| H(P | Q ∨ B(Ω)),

  where the last equality uses the invariance of `B(Ω)`. Moreover

      H(P | Q ∨ B(Ω)) <= H(P | P_n ∨ B(Ω)) + H(P_n | Q ∨ B(Ω)) < δ/(2|F|) + δ/(2|F|),

  so the second term is at most `2δ`.

Adding the two terms gives the bound. By Lemma 1, `h_Ω` is a profile for `(k, E)`. So `rho^prof_q(G) <= (1/k)(H(P | B(Ω)) + 3δ)`. Take the infimum over `P` and `δ`, and apply Lemma 0. ∎

**Corollary (relativization).** Suppose `rho^prof_q(G) >= log q`. Then `h_G((A^k)^G × Ω | B(Ω)) = k log q` for every `k` and every p.m.p. action `Ω`. The upper bound holds because the coordinate partition `x_1` generates.

## 3. Only the orbit relation matters

**Proposition 4.** Let `G ↷ Ω` and `H ↷ Ω'` be free p.m.p. actions, and let `θ : Ω -> Ω'` be an orbit equivalence. Then for every finite alphabet `L`,

    h_G(L^G × Ω | B(Ω)) = h_H(L^H × Ω' | B(Ω')).

*Proof.*
- **The intrinsic extension.** Let `R` be the orbit relation of `Ω`. Let `X_R` be the space of pairs `(ω, ξ)` with `ξ : [ω]_R -> L`, with the uniform product measure on fibers. `[R]` acts by `φ(ω, ξ) = (φ ω, ξ)`.
- **The shift is this extension.** The map `(x, ω) ↦ (ω, ξ)` with `ξ(a^-1 ω) = x(a)` is well defined by freeness. It is measure-preserving and `G`-equivariant. For `g·(x, ω)`, one gets `ξ'(h^-1 g ω) = x(g^-1 h)`, which is `ξ` evaluated at `(g^-1 h)^-1 ω`.
- **The full group generates nothing new.** Let `φ in [R]`, with `φ = g` on `Ω_g` and `Ω = ⊔ Ω_g`. For a set `p`, `φ(p) = ⊔_g g(p) ∩ π^-1(g Ω_g)`, which lies in `σ(G·P) ∨ B(Ω)`. So `σ([R]·P) ∨ B(Ω) = σ(G·P) ∨ B(Ω)`. The relative generating condition, and `H(P | B(Ω))`, depend only on `(R, X_R)`.
- **Transport.** The map `θ` carries `R` to `R'`. It induces a measure-preserving isomorphism `X_R -> X_(R')` that conjugates the full groups and carries `B(Ω)` to `B(Ω')`. ∎

This is standard in the class-bijective framework of Alpeev–Seward and is included here for completeness. It shows that consequence 3 of the target concerns the orbit relation of `Ω_KT`.

## 4. Calibration and scope

- **Amenable groups.** For amenable `G`, relative Kolmogorov–Sinai entropy gives `h(X × Ω | B(Ω)) = k log q`. So the Theorem imposes nothing false there, and profile proofs along Følner sets are consistent with it.
- **Genuine codes are profiles.** Take `Ω` to be a point. Then Section 1 is exactly the genuine configuration profile, which gives `rho^prof_q <= rho_q`.
- **What is not covered.** A proof that evaluates `psi` at special inputs, or counts microstates in finite models, is not an entropy-profile proof. The linear-code domination in `rokhlin-window-transport-is-dominated` (evaluation on constants) is the graph's example.
- **Open.** Is `rho^prof_q(G) = inf_Ω h_G((A^k)^G × Ω | B(Ω))/k`? And is `rho^prof_q(F_2) = 0`? The second would kill profile proofs outright over every nonamenable group.

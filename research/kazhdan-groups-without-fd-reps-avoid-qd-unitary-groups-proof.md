---
rg: 2
id: kazhdan-groups-without-fd-reps-avoid-qd-unitary-groups-proof
kind: route
title: Kazhdan projection corner plus quasidiagonal Følner projections gives an amenable representation with no invariant vectors, contradicting Bekka–Valette
target: kazhdan-groups-without-fd-reps-avoid-qd-unitary-groups
requires: [amenable-rep-of-kazhdan-has-fd-subrep]
---

Proof (sk-free-5, 2026-09-13). The notation is that of the target claim. `u_g ∈ C*(Γ)` are the canonical unitaries, and `Ψ : C*(Γ) → P` is the unital *-homomorphism extending `ψ`. Put `B = Ψ(C*(Γ))`, which is separable and quasidiagonal by hypothesis.

**Step 1: Kazhdan projection** (self-contained).
- Let `(S, ε)` be a Kazhdan pair with `S` finite and symmetric, and put `h = (2|S|)^{-1} Σ_{s∈S}(u_s + u_s*)`.
- For any unitary representation `π` and vector `ξ`, `⟨(1 − π(h))ξ, ξ⟩ = (2|S|)^{-1} Σ_s ‖π(s)ξ − ξ‖²`.
- So `π(h)ξ = ξ` iff `ξ` is invariant. On the orthogonal complement `V^⊥` of the invariant vectors, `1 − π(h) ≥ ε²/(2|S|) =: c`, by the Kazhdan property applied to the subrepresentation on `V^⊥`, which has no invariant vectors.
- So `spec π(h) ⊆ [−1, 1 − c] ∪ {1}`. Take `f` continuous with `f(1) = 1` and `f = 0` on `[−1, 1 − c]`, and put `p = f(h) ∈ C*(Γ)`.
- In every representation `π(p)` is the projection onto the invariant vectors. So `p` is a projection with `u_gp = pu_g = p` for all `g` (check in the universal representation), and it is central.

**Step 2: the trivial case.** Put `q = Ψ(1 − p)`, a central projection of `B`. If `q = 0` then `Ψ(u_g) = Ψ(u_gp) = Ψ(p) = 1` for all `g`, so `ψ` is trivial.

**Step 3: an essential representation of the corner.** Suppose `q ≠ 0`.
- `qB = Ψ((1 − p)C*(Γ))` is a C*-subalgebra of `B`, unital with unit `q`, and quasidiagonal, since quasidiagonality passes to C*-subalgebras.
- Represent `qB` faithfully and nondegenerately on `H_0`, and put `K = H_0 ⊗ ℓ²(N)`. This representation is faithful, nondegenerate and essential: no nonzero compact operators occur.
- By Voiculescu's theorem, stated in Brown, arXiv:math/0111286, Proposition `thm:QDcase` (read at source: "Let $A \subset B(H)$ be in general position. If $A$ is QD then there exists an increasing sequence of finite rank projections $P_1 \leq P_2 \leq \ldots$, converging strongly to the identity, which asymptotically commutes (in norm) with every element in $A$ …"), there are finite-rank projections `P_n` on `K` with `‖[P_n, b]‖ → 0` for every `b ∈ qB`.

**Step 4: a centralizing state.**
- Put `φ(T) = lim_ω Tr(P_nTP_n)/Tr(P_n)` for `T ∈ B(K)`, a state.
- For `b ∈ qB` and `T ∈ B(K)`: `Tr(P_nbTP_n) − Tr(bP_nTP_n) = Tr([P_n, b]TP_n)`, and `Tr(bP_nTP_n) = Tr(P_nTP_nb) = Tr(P_nTP_nbP_n) + Tr(P_nTP_n[b, P_n])`.
- Each error has absolute value at most `‖[P_n, b]‖‖T‖ Tr(P_n)`. So `φ(bT) = φ(Tb)`.

**Step 5: an amenable representation without invariant vectors.**
- Put `v_g = qΨ(u_g) ∈ U(qB)`. Since `q` is central in `B`, `v_gv_h = v_{gh}`, so `v` is a unitary representation of `Γ` on `K`.
- By Step 4, `φ(v_gTv_g*) = φ(Tv_g*v_g) = φ(T)`, so `v` is amenable in Bekka's sense.
- `b ↦ qΨ(b)` is a representation of `C*(Γ)` on `K` extending `v`. By Step 1, `qΨ(p)` is the projection onto the invariant vectors of `v`. But `qΨ(p) = Ψ((1 − p)p) = 0`, so `v` has no nonzero invariant vector.

**Step 6: contradiction.**
- By `amenable-rep-of-kazhdan-has-fd-subrep` (Bekka–Valette, Math. Z. 212 (1993), Theorem 1; derived on main), `v` has a nonzero finite-dimensional subrepresentation.
- By hypothesis every finite-dimensional unitary representation of `Γ` is a multiple of the trivial one, so `v` has a nonzero invariant vector. That contradicts Step 5.
- So `q = 0`, and `ψ` is trivial. ∎

**Consequences in the claim.**
- **`C*(Γ)` is not QD.** Apply the theorem to `ψ = (g ↦ u_g)`, `P = C*(Γ)`. Then `u_g = 1` for all `g`, which is false for nontrivial `Γ`.
- **QD quotients of `C*(Γ)`.** For a quotient map `C*(Γ) → Q` with `Q` quasidiagonal, the images of the `u_g` are `1`, so the image is `C`.

**Model tests.**
- `Γ = SL_3(Z)` is Kazhdan but has nontrivial finite-dimensional representations. Step 6 fails, and indeed `SL_3(Z) → U(∏ M_n)` is injective through finite quotients.
- `Γ = Z` has no Kazhdan projection. Step 1 fails, and indeed `Z → U(C(T))` is nontrivial with `C(T)` quasidiagonal.
- `Γ = G_X` with the note's LEF models gives `G_X → U(∏M/⊕M)`. The target is not quasidiagonal, so there is no contradiction.

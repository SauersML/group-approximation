# Cartan pairs with finitely many extremal traces have relative uniform Gamma (2026-09-16)

Swarm lane `swarm-stw99-problem-xlix-two-cartans`, target
`stw99-problem-xlix-two-cartans-relative-gamma` (STW Problem XLIX).

## Statement

**Theorem.**
- Let `A` be a unital, simple, separable, nuclear, infinite-dimensional C\*-algebra.
- Assume `T(A)` has finitely many extreme points `tau_1, ..., tau_m`, with `m >= 1`.
- Let `D ⊆ A` be a Cartan subalgebra in Renault's sense.

Then the sub-C\*-algebra `(D ⊆ A)` has uniform property Γ in the sense of
Kopsacheilis–Liao–Tikuisis–Vaccaro, arXiv:2406.09808v4, Definition 3.5.
The partitions constructed below satisfy the trace condition (3.3) for every `a ∈ A`, not only for
`a ∈ D`.

KLTV Corollary 5.3 (text read 2026-09-16) says that a sub-C\*-algebra with uniform property Γ has CPoU in
its case (ii), namely when `(D ⊆ A)` satisfies the assumptions of KLTV Theorem 5.2. Those assumptions are:
`A` separable with nonempty compact trace space, `D` abelian, non-degenerate and regular, the almost extension
property, and a conditional expectation onto `D`. Theorem 5.2 states that Cartan pairs satisfy them. So
`(D ⊆ A)` also has CPoU. (Paraphrase from the arXiv HTML, not a verbatim quotation; referee, 2026-09-16.)

**Corollary (STW Problem XLIX).** Suppose `A` is unital, simple, separable and nuclear, and contains one
Cartan subalgebra with relative uniform Γ and another without. Then `∂_e T(A)` is infinite.

**Proof of the corollary.**
- Relative uniform Γ (KLTV Definition 3.5) presupposes `T(A) ≠ ∅`.
- If `A` is finite-dimensional, then `A = M_d`. A Cartan `D` has `D^U = D`, so
  `κ(D^U) ∩ A' = C1`, and uniform Γ fails for `k = 2`. So no Cartan of `M_d` has relative Γ, and `A` is
  not a witness.
- If `A` is infinite-dimensional and `1 <= |∂_e T(A)| < ∞`, the Theorem gives every Cartan relative Γ.

## Definitions used (checked against the KLTV text, 2026-09-16)

- `U` is a free ultrafilter on `N`.
- `‖x‖_{2,T(A)} = sup_{tau ∈ T(A)} tau(x^*x)^{1/2}`.
- `A^U = l^∞(A) / {(a_r) : lim_U ‖a_r‖_{2,T(A)} = 0}` (KLTV (2.2)).
- `T_U(A)` is the set of limit traces `tau((a_r)) = lim_U tau_r(a_r)`, with `tau_r ∈ T(A)`.
- `κ : D^U → A^U` is induced by the inclusion.

KLTV Definition 3.5 (quoted from the arXiv HTML v4, read 2026-09-16) has the standing hypotheses "`A`
separable and `T(A)` nonempty and compact". Under them, `(D ⊆ A)` has uniform property Γ if
- `(κ(D^U) ⊆ A^U)` is unital, and
- for every `k ∈ N` there is a partition of unity of `A^U` by projections `q_1, ..., q_k ∈ κ(D^U) ∩ A'`
  with

  `tau(q_i a) = (1/k) tau(a)` for `tau ∈ T_U(A)`, `a ∈ D`, `i = 1, ..., k`.  (3.3)

Here `1 ∈ D`: an approximate unit `e_λ ∈ D` of `A` satisfies `e_λ = e_λ 1 → 1`, and `D` is closed.
Hence `κ(D^U)` is unital.

## Imported facts

- **(F1) Normalizer homeomorphisms** (Kumjian, Canad. J. Math. 38 (1986), 1.6; Renault, Irish Math. Soc.
  Bull. 61 (2008), arXiv:0803.2284v1, Proposition 4.6, text read by the referee 2026-09-16: "Given n ∈ N(B),
  there exists a unique homeomorphism α_n : dom(n) → ran(n) such that, for all b ∈ B and all x ∈ dom(n),
  n^*bn(x) = b(α_n(x)) n^*n(x)", under the standing assumption that `B` is abelian and contains an
  approximate unit of `A`).
  - Write `D = C(X)`. For a normalizer `n ∈ N(D)`, set `dom(n) = {n^*n > 0}` and `ran(n) = {nn^* > 0}`.
  - There is a homeomorphism `α_n : dom(n) → ran(n)` with

    `n^* d n = (d ∘ α_n) · n^*n`  for all `d ∈ D`,

    the right side extended by `0` off `dom(n)`.
- **(F2) Weyl twisted groupoid** (Renault 2008, arXiv:0803.2284v1: Theorem 5.6 is the reconstruction
  isomorphism and Proposition 4.7(ii) says that for essentially principal `G` every normalizer has a
  bisection as open support; both read by the referee 2026-09-16. The separable form, with `G` second
  countable, topologically principal, and the twist a Fell line bundle, is quoted as Renault's theorem in
  Takeishi, arXiv:1301.6883v1, Theorem 5.3, also read 2026-09-16).
  - Since `A` is separable, `(A, D) ≅ (C*_r(G, Σ), C(G^(0)))`. Here `G` is a second countable, locally
    compact, Hausdorff, étale, effective groupoid with `G^(0) = X`.
  - `G` is the groupoid of germs of the maps `α_n`. So the orbit relation is
    `R = {(α_n(x), x) : n ∈ N(D), x ∈ dom(n)}`.
  - `G` is second countable, so countably many normalizers `n_p` have `R = ∪_p graph(α_{n_p})`.
  - The reduced norm is the supremum of the norms of the regular representations `π_x` on
    `l^2(G_x; Σ)`. Hence each `π_x` is a representation of `A`. For `d ∈ D`, `π_x(d)` multiplies by
    `d ∘ r`.
- **(F3) Takeishi.** If `C*_r(G, Σ)` is nuclear, then `G` is amenable. This is Theorem 5.4 of Takeishi,
  Publ. RIMS 50 (2014) 251–268, as quoted by Barlak–Li, arXiv:1511.02697v3 (text read 2026-09-16): "If
  C∗r(G, Σ) is nuclear, then by [25, Theorem 5.4], G must be amenable." [25] is Takeishi.
  - Referee check, 2026-09-16: the primary source (Takeishi, arXiv:1301.6883v1) was read. Its Theorem 5.4
    says that for a locally compact Hausdorff étale groupoid `G` the following are equivalent: (i) `G` is
    amenable; (ii) `C*_r(E)` is nuclear for all Fell line bundles `E` over `G`; (iii) `C*_r(E)` is nuclear
    for some Fell line bundle over `G`. The proof of (iii) ⟹ (i) builds a net of compactly supported
    positive definite functions converging to `1` uniformly on compact sets. That is topological
    amenability in the Brown–Ozawa/ADR sense, which is the form (F4) needs.
- **(F4) Topological amenability** (Anantharaman-Delaroche–Renault, *Amenable groupoids*, Monographie
  Enseign. Math. 36, 2000; numbering not verified). An amenable étale `G` has continuous systems
  `x ↦ m^x ∈ Prob(G^x)` such that `sup_{γ ∈ K} ‖γ m^{s(γ)} − m^{r(γ)}‖_1 → 0` for every compact
  `K ⊆ G`. Here `(γ m)(β) = m(γ^{-1} β)`.
- **(F5) Connes–Feldman–Weiss** (Ergodic Theory Dynam. Systems 1 (1981); textbook form in Kechris–Miller,
  *Topics in orbit equivalence*, LNM 1852, 2004; numbering not verified).
  - Let `R` be a countable Borel equivalence relation with a Borel Reiter sequence: Borel
    `p^l : R → [0,1]` with `p^l_x = p^l(x, ·) ∈ Prob([x])` and `‖p^l_x − p^l_y‖_1 → 0` for all
    `(x, y) ∈ R`.
  - Then `R` is `μ`-hyperfinite for every `R`-quasi-invariant Borel probability measure `μ`.
- **(F6) Lusin–Novikov** (Kechris, GTM 156; numbering not verified).
  - A countable Borel equivalence relation is a countable union of graphs of Borel partial injections.
  - Saturations of Borel sets are Borel.
  - A finite Borel equivalence relation has a Borel transversal. The minimum of each class for a Borel
    injection into `R` is one.
- **(F7) Lyapunov (1940).** The range of a finite-dimensional vector measure with nonatomic coordinates is
  compact and convex.

Everything else (Krein–Milman, Riesz representation, regularity of Borel measures on compact metric
spaces, Urysohn) is standard.

## Step 0: reduction to finitely many measures

- `T(A)` is compact convex with `∂_e T(A) = {tau_1, ..., tau_m}`. By Krein–Milman,
  `T(A) = conv{tau_j}`.
- `tau ↦ tau(x^*x)` is affine, so `‖x‖_{2,T(A)} = max_j ‖x‖_{2,tau_j}`.
- Every limit trace has the form `tau((a_r)) = lim_U Σ_j s_j^(r) tau_j(a_r)`, with weights
  `s_j^(r) ≥ 0` and `Σ_j s_j^(r) = 1`.

Let `μ_j` be the Borel probability measure on `X` representing `tau_j|_D`, and `μ = (1/m) Σ_j μ_j`.

## Step 1: three lemmas about traces on a Cartan pair

**Lemma 1 (invariance).** For each trace `tau`, the measure `μ_tau` representing `tau|_D` satisfies
`μ_tau(α_n^{-1}(E)) = μ_tau(E)` for every normalizer `n` and Borel `E ⊆ ran(n)`.

*Proof.*
- Put `ψ = n^*n`. Apply (F1) to `d = nn^*`: `n^*(nn^*)n = (n^*n)^2 = ((nn^*) ∘ α_n) ψ`, so
  `nn^* = ψ ∘ α_n^{-1}` on `ran(n)`.
- By the trace property, `tau(n^* d n) = tau(d nn^*)`. So for `d ∈ C_c(ran(n))`,
  `∫_{dom} (d ∘ α_n) ψ dμ_tau = ∫_{ran} d (ψ ∘ α_n^{-1}) dμ_tau`.
- Thus the Radon measures `(α_n)_*(ψ μ_tau|_dom)` and `(ψ ∘ α_n^{-1}) μ_tau|_ran` agree on `ran(n)`.
- `ψ > 0` on `dom(n)`, so dividing by the positive Borel density `ψ ∘ α_n^{-1}` gives
  `(α_n)_*(μ_tau|_dom) = μ_tau|_ran`. ∎

**Lemma 2 (commutator formula).** For `n ∈ N(D)` and self-adjoint `f ∈ D`,

`[n, f]^* [n, f] = (f − f ∘ α_n)^2 · n^*n ∈ D`.

Hence `‖[n, f]‖_{2,tau}^2 = ∫_{dom(n)} (f − f ∘ α_n)^2 · n^*n dμ_tau ≤ ‖n‖^2 ∫_{dom(n)} (f − f ∘ α_n)^2 dμ_tau`.

*Proof.* Expand `(f n^* − n^* f)(n f − f n) = f n^*n f − f(n^* f n) − (n^* f n) f + n^* f^2 n`. By (F1)
and commutativity of `D`, this is `(f^2 − 2 f (f ∘ α_n) + (f ∘ α_n)^2) n^*n`. ∎

Consequence (the trace-restriction principle). The span of `N(D)` is dense in `A`, and
`‖[a − a', f]‖_{2,T(A)} ≤ 2 ‖a − a'‖` for contractions `f`. So for a sequence `(f_r) ⊆ D`, each of the
following is a statement about the measures `{μ_tau : tau ∈ T(A)}`, the maps `α_n` and the weights
`n^*n` alone:
- whether its class is a projection in `A'`;
- whether it is part of a partition of unity;
- whether it satisfies (3.3) for `a ∈ D`.

This is the only way the non-commutative part of `A` enters. In particular, traces need **not** factor
through the conditional expectation.

**Lemma 3 (no atoms).** Each `μ_j` is nonatomic.

*Proof.*
- Suppose `μ_j({x}) > 0`. By Lemma 1, `μ_j({α_n(x)}) = μ_j({x})` whenever `x ∈ dom(n)`. So every point of
  the orbit `F = [x]_R` has the same positive mass, and `F` is finite.
- `F` is closed and `R`-invariant.
- If `F ≠ X`, pick `0 ≠ d ∈ D` with `d|_F = 0`. The representation `π_x` of (F2) is unital. Its unit
  vectors are sections over `G_x`, whose ranges lie in `F`, so `π_x(d) = 0`. Hence `ker π_x` is a proper
  nonzero ideal of the simple algebra `A`. This is impossible.
- If `F = X`, then `X` is finite and discrete. For each `x`, the isotropy `r^{-1}(x) ∩ s^{-1}(x)` is
  open, so the isotropy bundle is open. Effectiveness then gives `Iso(G) = X`, so `G` is principal and
  finite, and `A` is finite-dimensional. This contradicts the hypothesis. ∎

## Step 2: the orbit relation is hyperfinite modulo `μ`

- By (F3), `G` is amenable.
- Choose compact sets `K_l ↑ G` and systems `m_l` from (F4) with
  `sup_{γ ∈ K_l} ‖γ m_l^{s(γ)} − m_l^{r(γ)}‖_1 < 1/l`.

**Measurability.**
- Cover `G` by countably many open bisections `S_p`, and choose `g_{p,q} ∈ C_c(S_p, [0,1])` increasing to
  `1_{S_p}`.
- For `β ∈ S_p` we have `G^{r(β)} ∩ S_p = {β}`, so `m_l^{r(β)}({β}) = lim_q ⟨m_l^{r(β)}, g_{p,q}⟩`.
  This is a pointwise limit of continuous functions of `r(β)`.
- So `β ↦ m_l^{r(β)}({β})` is Borel.

**Reiter sequence on `R`.** For `(x, y) ∈ R` define `p^l(x, y) = Σ_{β ∈ G^x, s(β) = y} m_l^x({β})`.
- Borel: partition `G` into Borel pieces of the bisections `S_p`. On each piece, `(r, s)` is a Borel
  injection with Borel inverse on its image. The sum is then a countable sum of Borel functions.
- Normalized: `p^l_x = s_*(m_l^x) ∈ Prob([x])`.
- Approximately invariant: for `(x, y) ∈ R`, pick `γ` with `r(γ) = x` and `s(γ) = y`. Left translation
  `β' ↦ γβ'` is a bijection `G^y → G^x` preserving `s`, so `s_*(γ m_l^y) = s_*(m_l^y) = p^l_y`.
  Pushforward is `l^1`-contractive, so `‖p^l_x − p^l_y‖_1 ≤ ‖m_l^x − γ m_l^y‖_1 < 1/l` once `γ ∈ K_l`.
- `R = ∪_p graph(α_{n_p})` is a countable Borel equivalence relation.

**Hyperfiniteness.**
- By Lemma 1, `μ` is `R`-invariant. By (F5), `R` is `μ`-hyperfinite: there is a `μ`-conull Borel set `Y`
  and increasing finite Borel equivalence relations `R_1 ⊆ R_2 ⊆ ...` with `∪_l R_l = R|_Y`.
- The saturation `[X \ Y]_R` is a countable union of images of null sets under the measure-preserving
  maps `α_{n_p}^{±1}`, so it is null. Replace `Y` by `X_0 = X \ [X \ Y]_R`: this is invariant and conull,
  and `R|_{X_0} = ∪_l R_l|_{X_0}`.
- `μ_j ≤ m μ`, so everything holds modulo each `μ_j`.

## Step 3: balanced, almost invariant Borel partitions

Fix `k`, `ε > 0`, and a finite set `N_0` of normalizers.

**Choosing the level `l`.**
- For `n ∈ N_0` let `E_l(n) = {x ∈ dom(n) ∩ X_0 : (α_n(x), x) ∉ R_l}`.
- These sets are Borel and decrease to `∅` as `l → ∞`, because `X_0` is invariant and
  `graph(α_n) ⊆ R`.
- Choose `l` with `μ_j(E_l(n)) < ε` for all `j` and all `n ∈ N_0`.

**Balancing by Lyapunov.**
- Let `T_l ⊆ X_0` be a Borel transversal of `R_l` (F6).
- For Borel `C ⊆ T_l`, set `ν_j(C) = μ_j([C]_{R_l})`.
- Disjoint subsets of a transversal have disjoint saturations, so `ν_j` is a finite Borel measure on the
  standard Borel space `T_l`.
- `ν_j({x}) = μ_j(finite class) = 0` by Lemma 3, so `ν_j` is nonatomic.
- By (F7), iterated `k − 1` times on the remainders, there is a Borel partition `T_l = C_1 ⊔ ... ⊔ C_k`
  with `ν_j(C_i) = 1/k` for all `i` and `j`. Each remainder has vector mass `(t, ..., t)`, and the vector
  `(1/k)(1, ..., 1)` lies on the segment from `0` to it.
- Put `B_i = [C_i]_{R_l}`, and add the null set `X \ X_0` to `B_1`. Then `μ_j(B_i) = 1/k`.

**Almost invariance.** Each `B_i ∩ X_0` is `R_l`-invariant. So for `x ∈ dom(n) ∩ X_0 \ E_l(n)`,
`1_{B_i}(α_n(x)) = 1_{B_i}(x)`. Hence

`∫_{dom(n)} |1_{B_i} ∘ α_n − 1_{B_i}| dμ_j ≤ μ_j(E_l(n)) < ε`.

## Step 4: continuous approximation and estimates

**Construction.**
- Given `η' > 0`, use regularity of `μ` to choose compact sets `K_i ⊆ B_i` with `μ(B_i \ K_i) < η'`.
- The `K_i` are pairwise disjoint and compact. Choose pairwise disjoint open sets `U_i ⊇ K_i` with
  `μ(U_i \ K_i) < η'`.
- By Urysohn, choose `g_i ∈ C(X, [0,1])` with `g_i = 1` on `K_i` and `g_i = 0` off `U_i`.
- Set `f_i = g_i` for `i ≥ 2` and `f_1 = 1 − Σ_{i≥2} g_i`. Then each `f_i ∈ D` takes values in `[0,1]`,
  and `Σ_i f_i = 1` exactly.

**Estimates.**
- `∫ |g_i − 1_{B_i}| dμ ≤ 2η'` and `∫ |f_1 − 1_{B_1}| dμ ≤ 2(k−1)η'`. So `∫ |f_i − 1_{B_i}| dμ_j ≤ η`
  with `η := 2mkη'`.
- **Trace.** `|tau_j(f_i) − 1/k| ≤ η`.
- **Projection defect.** Pointwise `0 ≤ f − f^2 ≤ |f − 1_B|`: if `x ∈ B` use `f − f^2 ≤ 1 − f`,
  otherwise `f − f^2 ≤ f`. So `‖f_i − f_i^2‖_{2,tau_j}^2 ≤ η`.
- **Commutators.** Let `n ∈ N_0` with `‖n‖ ≤ 1`. By Lemma 2 and the fact that values lie in `[0,1]`,
  `‖[n, f_i]‖_{2,tau_j}^2 ≤ ∫_{dom} |f_i − f_i ∘ α_n| dμ_j`. The triangle inequality bounds this by the
  sum of
  - `∫_{dom} |f_i − 1_{B_i}| dμ_j ≤ η`,
  - `∫_{dom} |1_{B_i} − 1_{B_i} ∘ α_n| dμ_j < ε`, and
  - `∫_{dom} |(1_{B_i} − f_i) ∘ α_n| dμ_j = ∫_{ran} |1_{B_i} − f_i| dμ_j ≤ η` (Lemma 1).

  So `‖[n, f_i]‖_{2,tau_j}^2 ≤ 2η + ε`.

## Step 5: assembly in the uniform tracial ultrapower

**Choice of the stages.**
- Fix a dense sequence `(a_p)` in `A`.
- At stage `r`, approximate `a_1, ..., a_r` within `1/r` by finite linear combinations of normalizers
  taken from a finite set `N_r` of normalizers of norm at most `1`. Let `M_r` be the largest coefficient
  sum used.
- Apply Steps 3–4 with `N_0 = N_r`, choosing `ε` and `η` so that `max_j ‖[n, f_i^(r)]‖_{2,tau_j} < 1/(r M_r)`
  for `n ∈ N_r`, `max_j ‖f_i^(r) − (f_i^(r))^2‖_{2,tau_j} < 1/r`, and `max_j |tau_j(f_i^(r)) − 1/k| < 1/r`.
- Let `q_i ∈ κ(D^U)` be the class of `(f_i^(r))_r`.

**Verification.**
- By Step 0, the uniform 2-norm is the maximum over the `tau_j`. So `q_i` is a projection and
  `Σ_i q_i = 1`.
- For `p ≤ r`, `‖[a_p, f_i^(r)]‖_{2,T(A)} ≤ 2/r + 1/r`. By density, `q_i ∈ A'`.

**Trace condition (3.3), for every `a ∈ A`.**
- Fix `j` and put `φ(a) = lim_U tau_j(f_i^(r) a)`.
  - *Positive:* `tau_j(f a^*a) = tau_j(f^{1/2} a^*a f^{1/2}) ≥ 0`.
  - *Bounded by `tau_j`:* `tau_j(f a^*a) = tau_j(a f a^*) ≤ tau_j(aa^*) = tau_j(a^*a)`.
  - *Tracial:* `φ(ab) − φ(ba) = lim_U tau_j([f, a] b)`, and
    `|tau_j([f, a] b)| ≤ ‖[f, a^*]‖_{2,tau_j} ‖b‖ → 0`.
- A tracial positive functional dominated by an extreme trace is a scalar multiple of it. If
  `0 < φ(1) < 1`, then `tau_j = φ(1)(φ/φ(1)) + (1 − φ(1))((tau_j − φ)/(1 − φ(1)))` is a proper convex
  combination.
- Hence `φ = φ(1) tau_j = (1/k) tau_j`.
- For a general limit trace, `tau(q_i a) = lim_U Σ_j s_j^(r) tau_j(f_i^(r) a) = (1/k) tau(a)`: there are
  finitely many `j`, each term converges, and the weights are bounded.

So `(D ⊆ A)` satisfies KLTV Definition 3.5. ∎

## Remarks

1. **Local relative Γ always holds** (sketch only; not part of the Theorem).
   - Drop the finiteness of `∂_e T(A)`, and let `S ⊆ T(A)` be any finite set of traces.
   - Steps 1–4 apply verbatim to the measures `μ_tau`, `tau ∈ S`. They are nonatomic by Lemma 3 applied to
     `tau`, which uses only simplicity.
   - In Step 3, also balance finitely many positive test functions `d_1, ..., d_r ∈ D`, using the
     nonatomic measures `C ↦ ∫_{[C]_{R_l}} d_p dμ_tau` in Lyapunov's theorem.
   - This yields relative Γ for `(D ⊆ A)` in the tracial ultrapower `(A, S)^U` (KLTV (2.2) with `X = S`).
   - So a Cartan subalgebra of a simple separable nuclear algebra can fail relative uniform Γ only through
     a failure of uniformity over infinitely many traces, never at finitely many traces. This parallels
     Toms's failure of absolute uniform Γ.
2. **The dynamical special case is known.**
   - Take a free minimal action of a countably infinite amenable group with finitely many ergodic
     measures, and `D = C(X) ⊆ C(X) ⋊ G`.
   - Kerr–Kopsacheilis–Petrakos (arXiv:2404.04634v2, abstract read 2026-09-12 per
     `research/artifacts/lit-major-findings-2026-09-12.md`) prove that minimal actions whose invariant
     measure simplex has closed, finite-dimensional extreme boundary have the small boundary property.
   - KLTV Theorem 5.4 (text read 2026-09-16) proves that for free amenable actions the small boundary
     property is equivalent to relative uniform Γ.
   - The theorem above is new relative to what was checked, not relative to that special case. It covers
     arbitrary Cartans: twisted, non-dynamical, with isotropy on a meagre set, and with traces not
     factoring through `E`.
3. **Consistency checks.**
   - The projections `q_i` lie in `κ(D^U) ∩ A' ⊆ A^U ∩ A'` and satisfy (3.3) for all `a ∈ A`. By KLTV
     Remark 3.7 (text read 2026-09-16), `(A ⊆ A)` then has uniform property Γ, i.e. `A` has uniform
     property Γ in the absolute sense.
     - This agrees with the expected behaviour of nuclear algebras with finitely many extreme traces.
       The literature attribution for that absolute statement was not re-verified here.
   - A free minimal `Z`-system of positive mean dimension (Giol–Kerr) fails relative Γ by KLTV
     Corollary D. So it must have infinitely many ergodic measures, which agrees with KKP.
   - Any algebra whose canonical Cartan fails relative Γ must likewise have infinitely many extreme
     traces. The repository records such an Elliott–Niu obstruction for Villadsen algebras of the first
     type; that source was not re-read here.
4. **Novelty audit.**
   - The KLTV text (arXiv:2406.09808v4) was searched for "extreme"/"finitely many" statements about Cartan
     pairs, and none were found.
   - STW arXiv:2506.10902v2 (text read 2026-09-16) poses XLIX as an open problem.
   - No external search engine was available in this session, so later literature (2025–26) could not be
     scanned beyond the repository's own audits.
   - Treat priority as unverified.

## Trust boundary

- **Checked in full above:** Steps 0–5 and Lemmas 1–3.
- **Imported, with numbering unverified (standard textbook content):**
  - F4 (Anantharaman-Delaroche–Renault);
  - F5 (Connes–Feldman–Weiss / Kechris–Miller);
  - F6 (Lusin–Novikov);
  - F7 (Lyapunov).
- **Imported, verified at the primary source by the referee (2026-09-16):**
  - F1 and F2: Renault, arXiv:0803.2284v1, Proposition 4.6, Proposition 4.7(ii) and Theorem 5.6. The
    separable, second countable form is quoted in Takeishi, Theorem 5.3.
  - F3: Takeishi, arXiv:1301.6883v1, Theorem 5.4. There amenability is topological, in the
    positive-definite-function form, so the measurewise fallback that was mentioned here earlier is not
    needed.
- **Most delicate imported link:** F4 ⟹ the Borel Reiter sequence ⟹ F5.
  - The measurability argument is given in Step 2.
  - The implication from a Reiter sequence to `μ`-hyperfiniteness is Connes–Feldman–Weiss, taken through
    Zimmer amenability.

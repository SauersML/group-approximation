# Strict comparison divides the unit over C-space tracial boundaries (2026-09-13)

Lane `ex-tw-rotation-gluing` (EX swarm). Target: `strict-comparison-forces-tracially-divisible-unit`,
positive side.

**Outcome.** Not reviewed.
1. **Theorem A.** Let `A` be unital, simple, separable, exact and non-elementary, with strict comparison
   of positive elements. Suppose `T(A)` is a nonempty Bauer simplex and its extreme boundary `K` has
   Haver's property C. Then the unit of `A` is tracially `N`-divisible for every `N`.
2. **Corollary B.** Such an `A` is pure. If `A` is also nuclear with tracially locally finite nuclear
   dimension, it is `Z`-stable.
3. **Where the method stops.** The proof sums local staircase pieces whose rank overshoot is `1/N` per
   active piece. Property C is exactly what makes these overshoots summable without adaptivity.
   Strongly infinite-dimensional boundaries such as the Hilbert cube are outside it (Section 5, part 2).

The proof is in this file (Sections 0–2) and in part 2
(`research/artifacts/ex-tw-c-space-unit-division-part2-2026-09-13.md`, Sections 3–5).

**Credit.** Three ingredients come from the repository, and the new step is combining them.
- Ozawa's central embedding, used as in `bauer-tracially-divisible-unit-gives-bounded-rank-density`.
- Property C screening with summable costs, the architecture of `stw22-c-space-screening-from-local-lifts`
  (a different problem: traces on completions of `C(X) ⊗ U`).
- Rørdam's lemma moves under strict comparison, as in the support-gap theorem
  (`research/artifacts/tw-support-gap-crux-2026-09-12.md`).
- The new step: central staircases turn local order zero maps into global pieces with overshoot `1/N`.
  Strict comparison then makes pieces from different levels exactly orthogonal, so no approximate
  centrality and no partial isometries on overlaps are needed.

## 0. Conventions and standard facts

- `M = A^st` is the strict closure, `K = ∂_e T(A)` compact metrizable, and `μ_τ` is the representing
  measure of `τ ∈ T(A)`. Every `λ ∈ K` extends by continuity to a tracial state of `M`, and
  `‖x‖_{2,u} = sup_{λ∈K} λ(x*x)^{1/2}`.
- `d_τ(x) = lim_k τ(x^{1/k})`. For a positive contraction `b` and a trace `λ`, `μ_{b,λ}` is the
  spectral measure of `b` under `λ`, so `d_λ((b − s)_+) = μ_{b,λ}((s,1])`.
- **Strict comparison.** For `x, y ∈ M_m(A)_+`, if `d_τ(x) < d_τ(y)` for all `τ ∈ T(A)`, then `x ≾ y`.

**(F1) Central functions** (Ozawa, arXiv:1304.3523, Theorem 3, with the Bauer property; read on MSI by lane
`ex-toms-winter`, see `research/artifacts/ex-toms-winter-bauer-divisible-unit-2026-09-12.md`).
- There is a unital `*`-homomorphism `θ: C(K) → M ∩ Z(N)`.
- For `x ∈ A` and `τ ∈ T(A)`, `τ(θ(f)x) = ∫ f(λ)λ(x) dμ_τ(λ)`.
- Consequences used below:
  - `λ(θ(f)x) = f(λ)λ(x)` for `λ ∈ K` and `x ∈ M`, by continuity in `‖·‖_{2,u}`;
  - `‖θ(f) − f(λ)1‖_{2,λ} = 0`, so in the fibre at `λ` the element `θ(f)` is the scalar `f(λ)`;
  - `τ(x) = ∫_K λ(x) dμ_τ` for `x ∈ M`.
- **Ranks integrate.** For `x ∈ M_m(A)_+`, `d_τ(x) = ∫_K d_λ(x) dμ_τ`. Indeed `d_τ` is the increasing
  limit of `τ(f_k(x))` for continuous `f_k ↑ 1_{(0,∞)}`; apply monotone convergence.

**(F2) Spectral bounds.** Let `b` be a positive contraction, `λ` a tracial state and `0 < s ≤ 1/2`. Then
```text
λ(b) − s  ≤  μ_{b,λ}((s,1])  ≤  λ(b)(1 + 2s) + 2 λ(b − b²)/s.
```
- Lower: `λ(b) = ∫ x dμ ≤ s + μ((s,1])`.
- Upper: on `(s, 1−s)` we have `x − x² ≥ s/2`, so `μ((s,1−s)) ≤ 2λ(b − b²)/s`. Also
  `μ([1−s,1]) ≤ λ(b)/(1−s) ≤ λ(b)(1 + 2s)`.

**(F3) Rørdam's lemma** (Kirchberg–Rørdam, Adv. Math. 2002, Lemma 2.2; standard, not re-read).
- If `x ≾ y` in `A`, then for every `ε > 0` there is `c ∈ A` with `cc* = (x − ε)_+` and `c*c ∈ her(y)`.
- By the trace identity `τ(h(c*c)) = τ(h(cc*))` for continuous `h` with `h(0) = 0`, so
  `d_τ((c*c − r)_+) = d_τ((x − ε − r)_+)` for every `r ≥ 0`.

**(F4) Order zero bookkeeping** (Lemma 1.2 of the `ex-toms-winter` artifact; its proof uses only the
structure theorem and traciality, so it holds for order zero maps into `M`).
- Let `φ: M_N → M` be c.p.c. order zero and `e_j = φ(e_jj)`.
- The `e_j` are pairwise orthogonal and sum to `φ(1)`.
- Every tracial state `λ` of `M` has `λ(e_j) = λ(φ(1))/N` and `Σ_j λ(e_j − e_j²) = λ(φ(1) − φ(1)²)`.

**(F5) Approximants** (Step 4 of Theorem 1 of the `ex-toms-winter` artifact).
- Every positive contraction `B ∈ M` is, for every `η > 0`, within `‖·‖_{2,u}`-distance `η` of a
  positive contraction `b ∈ A`.
- Then `|λ(b) − λ(B)| ≤ η` and `|λ(b − b²) − λ(B − B²)| ≤ 3η` for every `λ ∈ K`.

**Property C** (Haver; Addis–Gresham). A space `X` has property C if for every sequence `(U_k)` of open
covers there are families `V_k` of pairwise disjoint open sets, with `V_k` refining `U_k`, whose union
`⋃_k V_k` covers `X`. The facts below are recalled, not re-read, and none is used in the proof of Theorem A.
- Compact metrizable finite-dimensional spaces have property C.
- Countable-dimensional metrizable compacta have property C.
- Spaces with property C are weakly infinite-dimensional, so the Hilbert cube does not have it.

## 1. Local order zero maps

**Lemma 1 (local division).** For `λ_0 ∈ K`, `N ≥ 1` and `δ > 0` there are an open `O ∋ λ_0` and a c.p.c.
order zero `φ: M_N → A` with `λ(1 − φ(1)) < δ` for every `λ ∈ O`.

*Proof.*
- `λ_0` is extreme, so `π_{λ_0}(A)''` is a finite factor. It is infinite-dimensional because `A` is simple
  and infinite-dimensional, so it is of type II_1 and contains a unital `M_N`.
- Kaplansky density gives norm-bounded elements of `A` approximating its matrix units in `‖·‖_{2,λ_0}`.
  Along a free ultrafilter they define a unital `*`-homomorphism `M_N → ℓ^∞(A)/c_{λ_0}`, where `c_{λ_0}` is
  the ideal of `‖·‖_{2,λ_0}`-null sequences.
- Order zero maps from `M_N` lift along surjections (projectivity of `C_0((0,1]) ⊗ M_N`). This gives order
  zero `φ_m: M_N → A` with `λ_0(1 − φ_m(1)) ≤ ‖1 − φ_m(1)‖_{2,λ_0} → 0` along the ultrafilter.
- Pick `φ = φ_m` with `λ_0(1 − φ(1)) < δ`. Since `λ ↦ λ(φ(1))` is continuous on `K`, the inequality holds on
  an open `O ∋ λ_0`. ∎

**Lemma 2 (disjoint families combine).** Let `V_1, …, V_p ⊂ K` be pairwise disjoint open sets. Let
`φ_a: M_N → A` be order zero with `λ(1 − φ_a(1)) < δ` on `V_a`, and let `C_a ⊂ V_a` be closed. Then there is
an order zero `φ: M_N → M` with `λ(1 − φ(1)) < δ` for every `λ ∈ C_1 ∪ … ∪ C_p`.

*Proof.*
- Urysohn gives `g_a ∈ C(K,[0,1])` with `g_a = 1` on `C_a` and support in `V_a`. So `g_a g_b = 0` for `a ≠ b`.
- Put `φ = Σ_a θ(g_a)φ_a`. Since the `θ(g_a)` are central and mutually orthogonal,
  `φ(x)φ(y) = Σ_a θ(g_a)² φ_a(x)φ_a(y)`, so `φ` is order zero. It is c.p.c. because
  `φ(1) = Σ_a θ(g_a)φ_a(1) ≤ 1`.
- For `λ ∈ C_a`, (F1) gives `λ(φ(1)) = λ(φ_a(1))`. ∎

## 2. Central staircases

**Lemma 3 (staircase).**
- **Setting.** Let `φ: M_N → M` be c.p.c. order zero, and `h ∈ C(K,[0,1])` with `λ(1 − φ(1)) < δ` for
  every `λ ∈ supp h`. Let `0 < t ≤ 1` and `r = ⌈Nt⌉`.
- **The element.** Put `z_j = θ(clamp(Nth − j + 1))` for `j = 1, …, r`, where `clamp(x) = min(max(x,0),1)`,
  and
  ```text
  B = Σ_{j=1}^{r} z_j φ(e_jj)  ∈ M.
  ```
- **Conclusion.** `0 ≤ B ≤ 1`, and for every `λ ∈ K`:
  - (i) if `h(λ) = 0` then `λ(B) = λ(B − B²) = 0`;
  - (ii) `t h(λ) − δ ≤ λ(B) ≤ t h(λ)`;
  - (iii) `λ(B − B²) ≤ 1/(4N) + δ`.

*Proof.* Put `e_j = φ(e_jj)`.
- **Bounds.** The `z_j` are central positive contractions and the `e_j` are orthogonal, so
  `B ≤ Σ_j e_j = φ(1) ≤ 1`.
- **Case (i).** By (F1), `z_j` is the scalar `c_j := clamp(Nth(λ) − j + 1)` in the fibre at `λ`, and every
  `c_j = 0` when `h(λ) = 0`.
- **Profile.** Suppose `h(λ) > 0`, so `λ ∈ supp h`. Since `x := Nth(λ) ≤ Nt ≤ r`, we have
  `Σ_{j≤r} clamp(x − j + 1) = x`. By (F1) and (F4),
  ```text
  λ(B) = Σ_j c_j λ(e_j) = (λ(φ(1))/N) · N t h(λ) = t h(λ) λ(φ(1)),
  ```
  which lies in `[t h(λ)(1 − δ), t h(λ)]`.
- **Defect.** Orthogonality of the `e_j` gives `B − B² = Σ_j (z_j − z_j²)e_j + Σ_j z_j²(e_j − e_j²)`.
  - At most one index has `0 < c_j < 1`, namely `j − 1 < x < j`, and `c − c² ≤ 1/4`.
  - `λ(e_j) ≤ 1/N`, and by (F4) `Σ_j λ(e_j − e_j²) = λ(φ(1) − φ(1)²) ≤ λ(1 − φ(1)) < δ`.
  - Hence `λ(B − B²) ≤ 1/(4N) + δ`. ∎

**Remark (why staircases).** A central bump `ψ` times a local near projection `c` has rank `d_λ(c)`
wherever `ψ(λ) > 0`. That overshoot is a full `t` per active piece, which was the failure recorded under
"localized rank bumps" on the crux. The staircase switches on the `N` pieces of a local division one at a
time, so its rank overshoot is at most one piece, `1/N`.

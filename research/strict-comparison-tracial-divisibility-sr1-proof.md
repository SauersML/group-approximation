---
rg: 2
id: strict-comparison-tracial-divisibility-sr1-proof
kind: route
title: Match Winter's divisibility to Fu's list, transfer Fu's (TM) to Fu-Lin's (TM), and apply Fu-Lin
target: strict-comparison-tracial-divisibility-forces-sr1
requires: [fu-exact-simple-tracial-regularity-equivalences, strict-comparison-property-tm-forces-sr1, stable-rank-one-unital-algebras-are-k1-bijective]
artifacts:
  - research/artifacts/stw18-k1-witness-tracial-divisibility-2026-09-16.md
---

Let `A` be as in the target. The artifact holds the details, in Sections 3–4.

**Standard inputs.**

- **(R) Rørdam's lemma.** If `‖x − y‖ < η` and `t ≥ 0`, then
  `(x − η − t)_+ ≲ (y − t)_+`. *Referee's check.* In the unitization,
  `h := x − η − t ≤ y − t ≤ k := (y − t)_+`. For `δ > 0` put
  `g_δ(s) = ((s − δ)_+/s)^{1/2}` for `s > 0` and `0` for `s ≤ 0`, and
  `c = g_δ(h)`, a contraction in `C*(x)`. Then `(h − δ)_+ = chc ≤ ckc`, and
  `ckc = (k^{1/2}c)*(k^{1/2}c) ∼ k^{1/2}c²k^{1/2} ≤ k`. So `(h − δ)_+ ≲ k` for
  every `δ > 0`, hence `h_+ ≲ k`.
- **(C) Elementary Cuntz facts.** `zz* ∼ z*z`; `u ≤ v` gives `u ≲ v`;
  `g(b) ≲ b` for `g ≥ 0` with `g(0) = 0`; `d_τ` is monotone; and `a ≲ b` if and
  only if `(a − ε)_+ ≲ b` for all `ε > 0`.
- **(H) Haagerup–Kirchberg.** As quoted in STW arXiv:2506.10902v2: "If A is an
  exact C*-algebra then all lower semicontinuous quasitraces on A are traces."
- **(M) Monotonicity.** Quasitraces are monotone on positive elements, and
  additive on commuting ones.

**Step 0: Fu's hypotheses.**

- **Algebraic simplicity.** A nonzero ideal `I` has closure `A`, so it contains
  an element within 1 of `1_A`. That element is invertible, so `I = A`.
- **Quasitraces.** A tracial state `τ` extends to the lower semicontinuous trace
  `τ̄ = τ⊗Tr`, `τ̄(x) = Σ_i τ(x_ii)` on `(A⊗K)_+`.
  - Its definition ideal contains the dense subalgebra `∪_n M_n(A)`.
  - By minimality of the Pedersen ideal, `τ̄` is finite on `Ped(A⊗K)`.
  - So `τ̄ ∈ QT~(A) \ {0}` and `τ̄ ∈ QT(A)`.
- The remaining hypotheses (separable, exact, non-elementary) are assumed.
- **All normalized quasitraces are traces.**
  - Let `τ` be an element of Fu's `QT(A)`, or one of Winter's normalized
    quasitraces extended to matrices, and fix `n`. `M_n(A)` is unital and
    exact.
  - `τ(1_{M_n(A)}) = n`: the diagonal units are commuting orthogonal
    projections, each equivalent to `1_A`.
  - Let `u, v ∈ M_n(A)` be positive. Then `u ≤ v + ‖u − v‖·1`, and by (M)
    `τ(v + t·1) = τ(v) + nt`. So `|τ(u) − τ(v)| ≤ n‖u − v‖`, and `τ` is norm
    continuous on `M_n(A)_+`.
  - By (H), `τ` is linear on `M_n(A)`. A tracial positive functional on `M_n(A)`
    is `σ⊗Tr_n` with `σ = τ|_A ∈ T(A)`.
  - So on every `M_n(A)`, each of Fu's `QT(A)` and each of Winter's normalized
    quasitraces agrees with `τ̄` for some `τ ∈ T(A)`, and every `τ̄` occurs in
    both. The divisibility conditions in (b), (c), (6) and (7) only evaluate
    functionals on elements of some `M_k(A)`. So they are the same whichever of
    these sets of functionals is used.

**Step 1: reduce (a), (b) and (c) to (d).**

- **(a).**
  - Scaling does not change Cuntz classes, so the definition holds for all
    `a ∈ M_∞(A)_+`.
  - The inclusion `W(A) → Cu(A)` preserves order, because Cuntz subequivalence
    of elements of `M_∞(A)` is the same in `M_∞(A)` and in `A⊗K`. So `Cu(A)` is
    `m`-almost divisible in the sense of Fu's Corollary 9.2.
  - That corollary gives Fu's (3).
- **(b).** Two facts make (b) the same condition as Fu's (7):
  - `closure(a(A⊗K)a) = closure(aM_k(A)a)` for `a ∈ M_k(A)`;
  - by Step 0, Winter's and Fu's quasitraces are the same functionals.

  Here Fu's Definition 8.1 is read with its typographical slips corrected to
  Winter's form, as `fu-exact-simple-tracial-regularity-equivalences` states it.
- **(c).**
  - The zero map handles `a = 0`.
  - Otherwise (c) gives the inequality for all `τ ∈ T(A)`. By Step 0, that is
    all of Fu's `QT(A)`.
  - So (c) gives (b) with `m = 0`, which is Fu's (6).
  - Read literally, without the contraction assumption, STW's wording holds for
    no unital `A` with `T(A) ≠ ∅`: take `a = 2·1_A` and `ε < 1`.

**Step 2: Fu's (TM).** By `fu-exact-simple-tracial-regularity-equivalences`, in
the exact case all eight properties are equivalent, so (5) holds.

**Step 3: Fu's (TM) gives Fu-Lin's (TM).** Take `e = 1_A ∈ Ped(A)^1_+`, so
`Her(e) = A`.

- **The two `QT(A)`.** The papers use literally the same definitions. Fu's
  Definition 2.6, following Fu-Lin 2.7, gives:
  - `QT~(A)` as the densely defined 2-quasitraces on `A⊗K`;
  - the topology of pointwise convergence on `Ped(A⊗K)`;
  - `QT(A) = {τ : ‖τ|_A‖ = 1}` (Fu Definition 3.1, Fu-Lin 2.8).

  By monotonicity `‖τ|_A‖ = τ(1_A)`. So both papers' weak* closures of
  `QT(A)` are the same set `S`. `S` is compact: it is closed in Fu-Lin's compact
  `QT_{[0,1]}(A)`, from 2.8. `S` does not contain 0, since `τ(1_A) = 1` passes
  to pointwise limits.
- **The zero case.** For `a = 0` use the zero map.
- **Rescaling.** Otherwise put `a' = a/‖a‖`. Fu's (TM) gives order zero
  `φ: M_n → Her(a') = Her(a)` with `‖φ(1_n)a' − a'‖_2 < ε/‖a‖`.
- **Norms.** On `Ped(A⊗K)` both papers' 2-norms are `sup_{τ∈S} τ(x*x)^{1/2}`,
  and quasitraces are homogeneous. So `‖a − φ(1_n)a‖_{2,S} < ε`.

**Step 4: strict comparison in the Fu-Lin form (Lemma 3.5 of the artifact).**
Let `a, b ∈ (A⊗K)_+` with `d_τ(a) < d_τ(b)` for all `τ ∈ QT~(A) \ {0}`, hence for
all `τ̄`. Assume `‖a‖ = 1` and fix `ε ∈ (0, 1)`. Let `p_n` be the unit of
`M_n(A)`, and let `f_δ` be 0 on `[0, δ/2]`, 1 on `[δ, ∞)` and linear in between.

- **Cut down `a`.**
  - Pick `n` with `‖a − y‖ < ε/2`, where `y = p_n a p_n`.
  - (R) gives `(a − ε)_+ ≲ a_1 := (y − ε/2)_+`.
  - With `G(τ) = τ̄(f_{ε/2}(y))`: `d_τ(a_1) ≤ G(τ)`, because
    `f_{1/j}((t − ε/2)_+) ≤ f_{ε/2}(t)` on `[0, 1]`.
  - `G(τ) ≤ d_τ(y) ≤ d_τ(a) < d_τ(b)`, since `y ≲ a` by (C).
- **Approximate `b` from below.**
  - Put `c_k = p_k f_{1/k}(b) p_k ≲ b` and `F_k(τ) = τ̄(c_k)`.
  - The `F_k` are continuous on `T(A)` and increase in `k`, and
    `sup_k F_k(τ) = d_τ(b)`.
- **Compactness.**
  - The open sets `{F_k > G}` increase and cover the compact set `T(A)`, so
    `F_K > G` for some `K`.
  - Since `c_K ≤ f_δ(c_K) + δ p_K`, we get `τ̄(c_K) ≤ d_τ(c_K)`.
  - So `d_τ(a_1) < d_τ(c_K)` for all `τ ∈ T(A)`.
- **Conclude.**
  - The hypothesis on `M_∞(A)` gives `a_1 ≲ c_K`.
  - So `(a − ε)_+ ≲ b` for all `ε`, and `a ≲ b`.

**Step 5: conclude.** `A` is separable and simple with a densely defined
nontrivial 2-quasitrace `τ̄`. It has strict comparison as in Fu-Lin
Definition 2.11 (Step 4) and property (TM) (Step 3). By
`strict-comparison-property-tm-forces-sr1`, (5)⇒(3), so `sr(A) = 1`.

**The listed consequences.**

- Surjective `Γ` is (3)⇒(2) of the same theorem.
- K1-bijectivity follows from `sr(A) = 1` by
  `stable-rank-one-unital-algebras-are-k1-bijective`.

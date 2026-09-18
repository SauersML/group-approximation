---
rg: 2
id: central-deformation-euler-host-has-fng-steinberg-residual
kind: claim
title: The central-deformation Euler host T_p, in which the lamps are non-units and only a central element p becomes 1 on the corner, has a finitely normally generated Steinberg finite residual for some N
distinct_from:
  euler-triangular-steinberg-rf-residual-is-fng: that is the question for T_l, whose lamps π_k are commuting units and carry the symbols {π_0, π_q}; here the lamps are not units, so those symbols are not defined in the host.
  one-sided-inverses-cannot-repair-the-steinberg-residual: that shows one-sided inverses reduce to T_l; here p − 1 is not in the finite residual ideal, so that reduction does not apply.
  euler-ring-steinberg-rf-residual-is-fng: that concerns the quotient D = B/(p − 1); this host maps onto T_l but is not a retract of anything known to carry the symbols.
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
---

**OPEN (2026-09-18, lane gq-k2-q).** For some prime `l` and some `N >= 5`, the finite residual of `St_N(T_p)` is
finitely normally generated. With the verified facts below, this would give a finitely presented residually finite
group `Γ_N(T_p) = St_N(T_p)/St_N(T_p)_rf` containing `Z_(l)`.
- `Z_(l)` survives in `Γ_N(T_p)` unconditionally. `x_12(Z_(l) m_0)` maps injectively to `E_N(T_l)`, which is
  residually finite (`euler-triangular-ring-is-fp-rf`), and `St_N(T_p)_rf` maps into `St_N(T_l)_rf`.
- Residual finiteness of `T_p` itself (check C1) would place `St_N(T_p)_rf` inside `K_2(N, T_p)`.

## The host

- `B = Z<u, b, x, x^(-1)>` with relations
  - `x x^(-1) = x^(-1) x = 1`;
  - `x u x^(-1) = u + l`;
  - `b u = u b`;
  - `x p x^(-1) = p`, where `p = b(u + 1)`.
- `M = B/(Bu + B(p − 1))`, with generator `m_0`.
- `T_p = [[B, M],[0, Z]]`.

## Verified (lane proof, elementary)

1. **`p` is central in `B`.**
   - `b` commutes with `u`, so `π_0 = u + 1` commutes with `b` and with `p`.
   - `x` commutes with `p` by the last relation.
   - `pb = bπ_0 b = b bπ_0 = bp`.
2. **`B/(p − 1) ≅ D`**, the Euler ring of `resolvent-ring-has-path-normal-form`.
   - Modulo `p − 1`, `b π_0 = π_0 b = 1`, so `b = π_0^(-1)`, and the last relation becomes trivial.
   - The inverses `x^k π_0^(-1) x^(-k) = π_k^(-1)` commute, being inverses of the commuting `π_k = u + 1 + kl`.
   - So the quotient is `Z[u][π_k^(-1)][x^(±1); σ] = D`.
   - Since `p` is central, `B(p − 1)` is two-sided, and `M = D/Du`, which is the Euler base `Z_(l)[y^(±1)]` of
     `euler-triangular-ring-is-fp-rf`.
3. **`T_p` is finitely presented and `Z_(l) ⊆ M`.**
   - `B` has finitely many relations, and `M` is a cyclic `B`-module with two relations.
   - Directly, with `b_k = x^k b x^(-k)`: `b_k π_k = x^k p x^(-k) = p`, and `π_k m_0 = (1+kl) m_0`. So
     `(1+kl) b_k m_0 = b_k π_k m_0 = p m_0 = m_0`.
   - `M` is torsion-free, so `m_0` generates a copy of `Z_(l)`. It embeds in `St_N(T_p)` through `m ↦ x_12(m)`, since its image `e_12(m)` in `E_N(T_p)` is injective.
4. **The lamps are not units of `B`.**
   - `u ↦ u`, `b ↦ t/π_0`, `x ↦ x` defines `B -> A_p[x^(±1); σ]`. Here `A_p = Z[u, t][t/π_k : k ∈ Z] ⊂ Q(u)[t]`,
     with `σ(u) = u + l` and `σ(t) = t`. All relations hold, with `p ↦ t`.
   - `A_p` is graded by `t`-degree, with degree-0 part `Z[u]`, so `A_p^x = {±1}`. The units of the skew Laurent
     ring over the domain `A_p` are `±x^k`.
   - So `π_0 ↦ u + 1` is not a unit, and neither is any `π_k`. In particular the Steinberg symbols
     `{π_0, π_q}` of `euler-ring-rational-symbols-are-infinitely-generated` are not defined over `B`. They exist
     only in the quotient `T_p/(p − 1) = T_l`.
5. **`p − 1` is not in the finite residual ideal.**
   - `u, b ↦ 0` and `x ↦ 1` define `B -> F_l`, with `p ↦ 0`. Together with `M -> 0`, this gives a finite quotient
     of `T_p` in which `p ≠ 1`.
   - So `one-sided-inverses-cannot-repair-the-steinberg-residual` does not collapse `T_p` to `T_l`.

## Open checks

- **(C1) Residual finiteness of `B` and `T_p`.** The lamps `b_k` need not commute in `B`. Both `π_j` and `π_k`
  kill `[b_j, b_k]` on the left, because `π_j b_j = p` is central. If some `π_j` is a zero-divisor, `B` is larger
  than its image in `A_p[x^(±1); σ]`.
- **(C2) `K_2`.** `K_2(B) ⊕ K_2(Z)` is a direct summand of `K_2(T_p)`, by the retractions of
  `euler-ring-rational-symbols-are-infinitely-generated`, Part 3. Equality is the triangular theorem of
  Berrick–Keating, not read at source.
  - The question is whether `K_2(N, T_p)` contains an infinitely generated family dying in every finite quotient.
  - The `D`-symbols are absent. The residue invariants `I_p` must be re-derived, since the lines `π_k = 0` are not
    divisors of `Spec A_p`.
- **(C3) Finite quotients.** In a finite quotient, the Fitting decomposition of the central `p` splits the ring
  into a part where `p` is a unit and `π_k` is invertible (Euler type), and a part where `p` is nilpotent. The images
  of `K_2(N, T_p)` in the Euler-type parts are where a `c_q`-type obstruction could reappear.

## Attempts

1. **(C1) The lamps do not commute, even in finite quotients (2026-09-18, lane gq-k2-q).**
   - *Structure.* `B = B_0[x^(±1); σ]`, where `B_0` is the coproduct over `Z[u, p]`, with `p` central, of the
     commutative algebras `Z[u,p][b_k]/(π_k b_k − p)`, for `k ∈ Z`. The relations of `B` are exactly the
     `x`-conjugates of these.
   - *A finite quotient with `[b_0, b_1] != 0`.* Let `V = ⊕_(i ∈ Z/n) F_l^2`.
     - `u` acts by `−1`, so every `π_k ≡ 0` and `p` acts by `0`.
     - `x` shifts the blocks.
     - `b_k` acts on block `i` by a matrix `β_(k+i)`, where `(β_m)` is `n`-periodic.
     - All relations hold, since `u` is scalar and `π_k = 0`.
     - With `β_0, β_1` not commuting, `[b_0, b_1] != 0` in `End(V)`.

     So `B` is not its commutative image `A_p[x^(±1); σ]`, and `π_0`, which kills `[b_0, b_1]`, is a zero-divisor.
   - *Commutation is not finitely presentable this way.* Suppose we add `[b_0, b_j] = 0` for `|j| <= J`. Take
     `n >= 2J + 3`, `β_0 = E_11`, `β_(J+1) = E_12`, and `β_m = 1` otherwise. This satisfies the added relations but
     has `[b_0, b_(J+1)] != 0`. The characteristic-`l` fibre `p = 0` behaves like a free lamplighter.
   - *Consequence.* Any finitely presented variant of this host has non-commuting lamps in its finite quotients.
     Whether that helps (no symbols) or hurts (large `K_2` from the coproduct) is check C2.
2. **(C2, base level) The Euler symbols do not lift to the commutative lamp base (2026-09-18, lane gq-k2-q).**
   This is a lane proof with textbook inputs: Quillen's fundamental theorem for the regular ring `A`, the DVR
   localization sequence, and Matsumoto's theorem.
   - *Claim.* For every `z ∈ K_2(A_p)`, the specialization `w = z|_(t=1) ∈ K_2(A)` has `∂_(π_k) w = 1` for every
     `k`. Hence every `I_p(w) = 0`, and the image of `K_2(A_p) -> K_2(A)` meets the span of the `c_q` only in `0`.
   - *The divisors `E_k`.* Let `v_k` be the exceptional valuation of `(u, t) = (−1−kl, 0)` on `Q(u, t)`, with
     `v_k(π_k) = v_k(t) = 1`.
     - It is `>= 0` on `A_p`: `v_k(t/π_k) = 0`, and `v_k(t/π_j) = 1` for `j != k`, since
       `π_j ≡ (j−k)l`.
     - Its center has local ring `Q[u, t/π_k]_((π_k))`, a DVR with residue field `Q(s_k)`, `s_k = t/π_k`.
     - On `Q(u)` it restricts to `v_(π_k)` with ramification index `1`. So its tame symbol extends `∂_(π_k)`, with
       `Q ⊆ Q(s_k)`.
   - *The argument.*
     - `A_p[1/t] = A[t^(±1)]`. By the fundamental theorem, the image of `z` there is `i(w) + α·{t}`, with
       `α ∈ K_1(A)`. Only `a = det α ∈ A^x = {±Π π_j^(e_j)}` matters in `K_2(Q(u,t))`.
     - `z` comes from the DVR at `E_k`, so `∂_(E_k)(z) = 1`. That is, `∂_(π_k)(w) · c_k s_k^(−e_k) = 1` in
       `Q(s_k)^x`, with `c_k ∈ Q^x`.
     - `s_k` is transcendental, so `e_k = 0` for all `k`, and `a = ±1`. Then `∂_(π_k)(w) = a^(-1)` for every `k`.
       Since `w` has finitely many nontrivial residues, `a = 1`.
     - So every `∂_(π_k)(w) = 1`. ∎
   - *Not covered.* The skew-Laurent level, meaning the image of `K_2(A_p[x^(±1); σ]) -> K_2(D)`, where `I_p` lives
     only on the `K_2(A)_σ` summand. And the non-commutative `B` itself.
3. **(C2) The cheap sufficient condition, `K_2(N, T_p)` finitely generated and central (2026-09-18, lane gq-k2-q).**
   Not established.
   - *Facts proved (elementary).*
     - **Grading.** All relations of `B` are homogeneous for the `b`-degree (`deg u = deg x = 0`, `deg b = 1`).
       So `B = ⊕_(d>=0) B_d`, with `B_0 = Z[u][x^(±1); σ]`, a domain.
     - **Units.** The degree-0 part of a unit is a unit of `B_0`, hence `±x^k`. So `B^x = {±x^k}·(B^x ∩ (1 + B_+))`.
       The units of the commutative image are exactly `±x^k` (Attempt 2 setting).
     - **The lamp commutators are torsion.** From `b_k u = p − (1+kl) b_k` and `[b_j, u] = 0`, expanding `b_k u b_j`
       both ways gives `p(b_j − b_k) = (k−j) l b_k b_j`. Swapping `j` and `k` gives `(k−j) l [b_j, b_k] = 0`.
       So the non-commutation of C1 lives in the torsion of `B`, and is visible only in characteristic dividing
       `(k−j) l`.
   - *Why it does not close.*
     - The Dennis–Stein generation theorem (St) is for commutative rings. No available result generates `K_2(N, B)`
       by symbols for this non-commutative `B`.
     - Listing Dennis–Stein pairs is therefore not a computation of `K_2(N, T_p)`.
       - Among commuting pairs with `1 + ab ∈ {±x^k}`, the ones in `Z[x^(±1)]` give only `K_2(Z[x^(±1)])`, which is
         finite.
       - Pairs with `ab = 0`, such as `⟨p, n⟩` with `pn = 0`, give Swan's elements, which are not controlled.
     - Centrality of `K_2(N, ·)` also needs a stable-range bound, and none is known for `B`.
   - *Remaining route.* The `p`-localization sequence, with the `E_k`-residue invariant of Attempt 2 lifted to the
     skew-Laurent level.
4. **(C2, skew-Laurent level) The Euler symbols are invisible from `T_p`: a `t`-homotopy (2026-09-18, lane gq-k2-q).**
   This supersedes the residue argument of Attempt 2, which it contains. Inputs:
   - Quillen's homotopy invariance `K_2(R[t]) ≅ K_2(R)` for left regular noetherian `R`, applied to `D`.
     `D = A[x^(±1); σ]` is noetherian of global dimension at most 3, since `A` is regular of dimension 2.
     Textbook, not re-read.
   - `abc-twisted-laurent-k-theory-fibration`, applied to `Z[u]`.

   Steps:
   - *The deformation.* `u ↦ u`, `b ↦ t π_0^(-1)`, `x ↦ x` defines a ring map `φ : B -> D[t]` with `p ↦ t`. The
     relations hold because `t` is central and commutes with `x`.
     - `ev_1 ∘ φ` is the quotient `B -> B/(p − 1) = D`.
     - `ev_0 ∘ φ` sends `b ↦ 0`, so it factors as `B -> Z[u][x^(±1); σ] ⊆ D`.
   - *Homotopy.* Both `ev_0` and `ev_1` invert `K_2(D) ≅ K_2(D[t])`, so they agree on `K_2`. Hence the map
     `K_2(B) -> K_2(D)` induced by `B -> D` factors through `K_2(Z[u][x^(±1); σ])`.
   - *That group is finite.* By `abc-twisted-laurent-k-theory-fibration` for the regular ring `Z[u]` and
     `σ(u) = u + l`, it is an extension of `ker(1 − σ on K_1(Z[u]) = {±1})` by
     `coker(1 − σ on K_2(Z[u]) = K_2(Z))`. So it has order at most 4.
   - *Conclusion.* The image of `K_2(B) -> K_2(D)` has order at most 4.
     - The retraction `T_l -> D × Z` restricted to `T_p` factors through `B × Z`. So the image of
       `K_2(T_p) -> K_2(T_l)` meets the free abelian group spanned by the `c_q` only in `0`.
     - The obstruction of `euler-ring-rational-symbols-are-infinitely-generated` does not come from `T_p`.
   - *Not covered.* Classes of `K_2(N, T_p)` in the kernel of `K_2(T_p) -> K_2(T_l)`, the unstable `K_2(N, ·)`,
     and whether such classes die in every finite quotient.
5. **The ideal side (2026-09-18, lane gq-k2-q).** Not decided.
   - *General necessary condition (proved, elementary).* For any ring `T` and `N >= 3`, if `St_N(T)_rf` is finitely
     normally generated, then `I_rf(T)` is finitely generated as a two-sided ideal.
     - Let `g_1, …, g_m` normally generate `St_N(T)_rf`, and let `J` be the two-sided ideal generated by the entries
       of the images `ḡ_s − 1` in `E_N(T)`.
     - *`J ⊆ I_rf`:* each `g_s` dies in every `St_N(T/J')` with `J'` of finite index, so its entries lie in `J'`.
     - *`I_rf ⊆ J`:* for `a ∈ I_rf`, `x_12(a)` lies in `St_N(T)_rf` by `steinberg-rf-forces-ring-rf`. So `e_12(a)`
       lies in the normal closure of the `ḡ_s`, which is contained in the congruence subgroup `GL_N(T, J)`. ∎
   - *For `T_p`.*
     - `T_l` is residually finite and `T_p -> T_l` is the identity on `M` and `Z`. So
       `I_rf(T_p) ⊆ [[I_rf(B) ∩ (p − 1)B, 0],[0, 0]]`.
     - The torsion commutators `[b_j, b_k]` are not in `I_rf(B)`, by C1.
     - So the route needs `I_rf(B) ∩ (p − 1)B` to be finitely generated, and the clean case is `B` residually finite.
       That is open: it needs a normal form for `B`. The rewriting `u b_k -> p − (1+kl) b_k` leaves the overlap
       relations `p(b_j − b_k) = (k−j) l b_k b_j`, which are not monic over `Z`.
   - *Which classes the Euler-type parts see (from Attempt 4, stable `K_2`).*
     - In a finite quotient, the Fitting splitting of the central element `p + e_22` has a part where `p` is a unit.
       That part is a quotient of `T_p[p^(-1)] = [[D[t^(±1)], M],[0, Z]]`.
     - The image of `K_2(B)` in `K_2(D[t^(±1)])` lies in the image of `K_2(D[t]) = K_2(D)`, which has order at
       most 4.
     - So a class of `K_2(T_p)` survives in some finite quotient unless, apart from those `<= 4` classes, it dies in
       every quotient where `p` is nilpotent. The `p`-adic fibre is where the residual lives.
     - The `r <= l − 1` kill result concerns the Euler part, where the `T_p`-classes are already finite, so it is
       not needed there.

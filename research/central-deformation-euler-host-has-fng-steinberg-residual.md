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
  - research/artifacts/gq-referee-a-central-deformation-attempts-4-5.md
  - research/artifacts/gq-referee-b-central-deformation-euler-host-attempt-4.md
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
   *Reviewed:* PASS by `gq-referee-a` (Attempts 4–5) and `gq-referee-b` (Attempt 4); reports in `artifacts`.
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
     `σ(u) = u + l`, it is an extension of `ker(1 − σ on K_1(Z[u]))` by `coker(1 − σ on K_2(Z[u]))`.
     Homotopy invariance for the regular ring `Z` gives `K_1(Z[u]) = {±1}` and `K_2(Z[u]) = K_2(Z)`, on which `1 − σ`
     is zero. So the group has order at most 4.
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
     - *`J ⊆ I_rf`:* each `g_s` dies in the finite group `E_N(T/J') ⊆ GL_N(T/J')` for every `J'` of finite
       index, so the entries of `ḡ_s − 1` lie in `J'`.
     - *`I_rf ⊆ J`:* for `a ∈ I_rf`, `x_12(a)` lies in `St_N(T)_rf` by `steinberg-rf-forces-ring-rf`. So `e_12(a)`
       lies in the normal closure of the `ḡ_s`, which is contained in the congruence subgroup `GL_N(T, J)`. ∎
   - *For `T_p`.*
     - `T_l` is residually finite and `T_p -> T_l` is the identity on `M` and `Z`. So
       `I_rf(T_p) = [[I_rf(B), 0],[0, 0]]` exactly (gq-referee-a): `D` is residually finite, so
       `I_rf(B) ⊆ (p − 1)B`, and a finite-index ideal of `T_p` meets the corner `B` in a finite-index ideal.
     - The torsion commutators `[b_j, b_k]` are not in `I_rf(B)`, by C1.
     - So the route needs exactly that `I_rf(B)` is finitely generated, and the clean case is `B` residually finite.
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
6. **Normal-form data for residual finiteness of `B` (2026-09-18, lane gq-k2-q).** Proved, elementary. RF of `B`
   itself is still open.
   - *Eliminating `u`.* In the lamp subring, `u` is central, and `u b_k = p − (1+kl) b_k`. So for a lamp word
     `w = b_(k_1) ⋯ b_(k_r)` and any position `i`, `u·w = p·(w ∖ i) − (1 + k_i l)·w`, where `w ∖ i` deletes the
     `i`-th letter.
   - *Positional relations.* Comparing two positions gives `p(w ∖ i − w ∖ i') = (k_i − k_(i')) l · w`. These
     relations hold in `B`. The positive-degree part of the lamp subring is spanned over `Z[p]` by lamp words.
     That the positional relations generate all relations among words is expected but not verified: the check
     that higher powers of `u` add nothing is not done.
   - *Consequences.*
     - `w = b_k b_j b_k` with `i = 1`, `i' = 3` gives `p [b_j, b_k] = 0`. So each lamp commutator is killed by `p`,
       by `(k−j) l`, and on the left by `π_j` and `π_k`. It vanishes where `p` is a unit, which is consistent with
       Attempt 4.
     - Modulo `p`, a word is killed by `l·(k_i − k_(i'))` for each pair of positions. In the fibre `B/(p)`, only
       the powers `b_k^r` stay torsion-free in positive degree.
   - *What RF needs.* Enough finite representations to separate the `Z[p]`-module of words modulo the positional
     relations, together with residual finiteness of the commutative image `A_p[x^(±1); σ]`. Neither is done.
7. **The non-commutative part of `B` is exactly its `Z`-torsion (2026-09-18, lane gq-k2-q).** This is a lane proof. The
   inputs are textbook commutative algebra: complete intersections are Cohen–Macaulay, and so have no embedded
   primes.
   - *Rationally the lamps commute.* In `B ⊗ Q`, `(k−j) l [b_j, b_k] = 0` gives `[b_j, b_k] = 0`. So the lamp
     subring of `B ⊗ Q` is a quotient of `S = Q[u, p, b_k : k ∈ Z]/(b_k π_k − p)`.
   - *`S` is a domain, and `S ≅ A_p ⊗ Q`.*
     - For a finite set of `k`, `S_K = Q[u, (b_k)_(k ∈ K)]/(b_k π_k − b_j π_j)` is a complete intersection of
       dimension 2.
     - Over `π_k ≠ 0` for all `k`, it is the irreducible surface `b_k = p/π_k`.
     - Over `u = −1−kl`, the other `π_j = (j−k)l` are units of `Q`, so the fibre is the line `E_k` in `b_k`, of
       dimension 1, and it lies in the closure of that surface.
     - Hence `S_K` is irreducible, and it is generically reduced with no embedded primes, so it is a domain. So is
       the colimit `S`.
     - `S -> A_p ⊗ Q`, `b_k ↦ t/π_k`, is onto, between domains of the same dimension, so it is injective.
   - *Consequence.* `B ⊗ Q ≅ (A_p ⊗ Q)[x^(±1); σ]`.
     - The kernel of `B -> A_p[x^(±1); σ]` is exactly the `Z`-torsion of `B`, which contains the lamp commutators.
     - `A_p[x^(±1); σ] ⊆ D[t]` is residually finite: `D` is (`euler-triangular-ring-is-fp-rf`), and evaluating `t`
       at integers separates polynomials over the torsion-free `D`.
     - So **`B` is residually finite if and only if its `Z`-torsion is separated by finite quotients.** C1 shows
       this for the commutators themselves. The general torsion element is still open.
8. **A Baumslag letter cannot remove the torsion (2026-09-18, lane gq-k2-q).** Design verdict: fails. Proof below;
   lane proof, elementary.
   - *The idea.* This is modelled on `k-infinity-lies-in-a-simple-localization-of-an-fp-ring`. Adjoin a unit `y` with
     `xy = yx` and a doubling relation on the lamp `b`, to force all `[b_j, b_k] = 0` from finitely many relations.
   - *Where it must act.* On the corner `M ⊇ Z_(l)`, `p = 1`, so each `b_k` acts as `π_k^(-1)`. These operators
     commute and are invertible, and `y` acts invertibly and commutes with `x`.
   - *Additive letter, `y b y^(-1) = b + x b x^(-1)`.*
     - On `M`, `y π_0 y^(-1) = h(π_0)`, with `h(a) = (a^(-1) + (a+l)^(-1))^(-1) = a(a+l)/(2a+l)`. The inverses of
       `2π_k + l` exist on `M`, because `b_k + b_(k+1)` is a conjugate of an invertible operator.
     - Conjugating `x u x^(-1) = u + l` by `y` gives `h(π_1) = h(π_0) + l`.
     - Since `h(a+l) − h(a) = 2l(a+l)^2/((2a+l)(2a+3l))`, this forces `l(2π_0^2 + 4lπ_0 + l^2)·M = 0`.
     - On `m_0`, where `π_0 = 1`, the integer `l(2 + 4l + l^2)` kills `m_0`. So `M` has no `Z_(l)`.
   - *Multiplicative letter, `y b y^(-1) = b·x b x^(-1)`.*
     - On `M`, `y π_0 y^(-1) = π_0 π_1`. Commuting with `x` forces `π_1 π_2 = π_0 π_1 + l`, that is,
       `l(2π_1 − 1)·M = 0`.
     - On `m_0`, `l(1 + 2l) m_0 = 0`, so again there is no `Z_(l)`.
   - *The same clash for `s_0 = t/π_0`*, since it is the same lamp.
   - *Why.* On `M` the lamps generate the commutative algebra `A`, and `y` must act on it compatibly with the shift
     `u ↦ u + l`. Baumslag's mechanism needs `y` to double lamps inside a free symmetric algebra, and `A` is not
     one: the lamps are tied to the single variable `u`.
   - *The symbols of `y`.* These are moot, since the design fails.
9. **The `p`-nilpotent side: where the residual can live (2026-09-18, lane gq-k2-q).** The reduction is proved; the
   decision is not.
   - *Grading.* `B = B_0 ⊕ B_+` by `b`-degree, with `B_0 = Z[u][x^(±1); σ]`. So
     `K_2(B) = K_2(B_0) ⊕ K_2(B, B_+)`, and `|K_2(B_0)| <= 4` by ABC for `Z[u]`.
   - *Euler-type quotients see nothing of `K_2(B, B_+)`.*
     - `B[p^(-1)] ≅ D[t^(±1)]`, because inverting `p` makes the lamps commute (`p[b_j, b_k] = 0`) and
       `π_k^(-1) = p^(-1) b_k`.
     - `φ : B -> D[t]` sends `B_+` into `tD[t]`, and `K_2(D[t], tD[t]) = NK_2(D) = 0`.
     - So `K_2(B, B_+)` maps to `0` in `K_2(D[t^(±1)])`, and hence, stably, into every finite quotient where `p` is
       a unit.
   - *The `p`-nilpotent quotients* are quotients of `B/(p^n) × Z`, since `p = 1` on `M` kills `M/p^n M`.
   - *A sufficient condition for vanishing.* The grading gives `τ : B -> B[t]`, `b_d ↦ b_d t^d`, with `ev_1 τ = id`
     and `ev_0 τ = (B -> B_0)`. If `NK_2(B) = 0`, then `K_2(B, B_+) = 0`, the stable `K_2(T_p)` is finite, and only
     unstable and centrality issues remain.
   - *The question (b) becomes.* Is `NK_2(B)`, or at least the part of `K_2(B, B_+)` that dies in every finite
     quotient of every `B/(p^n)`, finitely generated?
     - Candidate detectors in characteristic `l` exist: `K_2(F[X,Y]/(X^2, XY, Y^2)) = K_2(F) ⊕ F^+`, generated by
       `{1+X, 1+uY}` (Dennis–Stein, p. 255). The free lamps of C1 map onto such rings.
     - Heuristic, not claimed: by Farrell-type non-finiteness, `K_2(B, B_+)` is either `0` or not finitely
       generated. So the route needs it to be `0` or detected.
10. **Detection versus vanishing on the `p`-nilpotent side (2026-09-18, lane gq-k2-q).** Final attempt under the
    stall rule. Not decided.
    - *The vanishing shortcut is unavailable (proved, elementary).* Take the finite piece
      `A^(j,k) = Z[u][t/π_j, t/π_k, t] ⊂ Q(u)[t]` of the commutative lamp base.
      - It is the Rees algebra of `J = (π_j, π_k) = (π_j, (k−j)l) ⊆ Z[u]`, and `(π_j, π_k)` is a regular sequence.
        So `A^(j,k) ≅ Z[u, s_j, s_k]/(π_j s_j − π_k s_k)`, a hypersurface.
      - Let `q` be a prime dividing `(k−j)l`, and `𝔫 = (q, π_j, s_j, s_k)`. With `y = π_j`, the equation reads
        `y(s_j − s_k) − (k−j) l s_k`, and it lies in `𝔫^2`.
      - So `A^(j,k)` is singular at `𝔫`, a mixed-characteristic conifold point `xy = qz` where two exceptional lines
        meet in the `q`-fibre.
      - In `A_p` all lamps `s_m` with `q | (m−j)l` pass through that point.
      - Regularity-based `NK_2 = 0` is therefore not available for the lamp base, and a fortiori not for `B`.
    - *Detection is not reached.*
      - There is no generating set for `K_2(B, B_+)`, since Dennis–Stein generation needs commutativity.
      - The natural detectors are:
        - the degree truncations `B -> B/B_(>=n)`, whose relative `K_2` is that of a nilpotent extension of
          `B_0 = Z[u][x^(±1); σ]`;
        - their finite quotients, which include the characteristic-`l` free-lamp representations of C1 and
          Dennis–Stein targets such as `F[X,Y]/(X^2, XY, Y^2)`.
      - Whether these separate `K_2(B, B_+)` is not decided. Farrell's dichotomy was not used and was not read.

## Status: PARKED (2026-09-18, lane gq-k2-q)

`T_p` is finitely presented, carries `Z_(l)` in its residually finite quotient, and avoids the Euler symbols
(Attempt 4). The route to `z-localized-embeds-in-fp-rf-group` through `T_p` still needs:
1. **`I_rf(B)` finitely generated** (Attempt 5, exact form). The clean case is that finite quotients separate the
   `Z`-torsion of `B` (Attempt 7). The Baumslag fix is excluded (Attempt 8).
2. **The residual inside `K_2(B, B_+)` finitely generated** (Attempts 9–10). The strongest form is that finite
   quotients of the truncations `B/B_(>=n)` detect every class. Vanishing via regularity is excluded.
3. **Unstable `K_2(N, T_p)`** against the stable computation, and centrality. No stable-range bound is known.

# sk-deligne-sofic part 1: a finite-action soficity criterion for finite central extensions, and the Deligne instance

Lane sk-deligne-sofic, 2026-09-14. Everything here is unreviewed; review is queued in `sk2/queue/verify.txt`.

## 0. Summary
- **Theorem 1.** Let `Gamma` be finitely presented and residually finite, and `Gamma~` a central extension by a finite
  abelian `A`. If the normalized Hamming norm of the class tends to 0 along some sequence of finite `Gamma`-sets, then
  `Gamma~` is sofic. The approximations are torsors `V x A` over exact finite actions, corrected on a vanishing
  fraction of cells.
- **Theorem 2.** If `Gamma` is moreover stable in finite actions (Gohla–Thom Definition 3.7), `Gamma~` is sofic iff
  that infimum is 0.
- **Instance.** `E_3` is sofic whenever the Deligne class has vanishing finite-action norm over `Sp_4(Z)`. That gives a
  route into `deligne-triple-cover-is-sofic`, hence into Open problem 6.1. The new open claim is
  `deligne-class-finite-action-norms-vanish`.
- **Relation to main.** Theorem S (`weakly-bernoulli-liftable-action-makes-extension-sofic`) gets soficity from a
  weakly Bernoulli liftable action. Theorem 1 gets it from finite actions alone, with no Bernoulli input and no weak
  containment. Gohla–Thom Theorem 3.13 is the stable-base nonsoficity direction under a uniform cosystolic lower
  bound; Theorem 2 is its two-sided form without the cosystolic hypothesis.

## 1. Setting and the norm
- **Presentation.** `Gamma = <S | R>` with `S`, `R` finite, and `1 -> A -> Gamma~ -> Gamma -> 1` central with `A`
  finite abelian. Fix lifts `s~ in Gamma~` of `s in S`, and let `a_r in A` be the value of `r` on the lifts. As in step 1
  of Theorem S (main, `research/artifacts/weakly-bernoulli-lifts-sofic-transfer-and-sp4-2026-09-13.md`),
  `Gamma~ = <S ∪ A | relations of A, [a,s] (a in A, s in S), r = a_r (r in R)>`.
- **Finite Gamma-sets.** For a finite `Gamma`-set `X` (an exact action), a torsor cochain is `b : S x X -> A`. Its
  holonomy along a word `w = s_1^{e_1} ... s_k^{e_k}` at `x` is the sum of the signed values `b(s_i, ·)` read along the
  path of `w` from `x` (for `e_i = +1` the value at the endpoint `s_i·y`; for `e_i = -1` minus the value at `y`),
  matching the permutations `tau(s)(x,t) = (s·x, t + b(s, s·x))` below.
- **Defect and norm.** A cell `(x, r)` is defective if `hol_r(x) != a_r`. Put
  `nu_X(b) = #{defective (x,r)} / (|X| |R|)` and `nu_X(alpha) = min_b nu_X(b)`.
  - This is the normalized Hamming cosystole of the constant class on the presentation complex `Y_X` of the action.
  - It is a class invariant: changing the lifts or `b` by a coboundary changes no defect set.
  - Other finite models and cell weights change `nu` by bounded factors (Gohla–Thom §2.2, as recorded in
    `deligne-class-congruence-cosystole-bounded-below`), so whether the infimum below is 0 does not depend on the
    model.
- **Monotonicity.**
  - (M1) If `X -> X'` is a `Gamma`-map of finite transitive sets, pulling back a cochain along it keeps the defect
    fraction, so `nu_X(alpha) <= nu_X'(alpha)`.
  - (M2) For `X = X_1 ⊔ X_2`, `nu_X` is the weighted average of `nu_(X_i)`, which is at least `min_i nu_(X_i)`.
  - (M3) For a product `X x W` with `Gamma` acting diagonally, pulling back along the projection gives
    `nu_(X x W)(alpha) <= nu_X(alpha)`.
- **The number.** `nu_fin(alpha) = inf_X nu_X(alpha)` over finite `Gamma`-sets `X`.

## 2. Theorem 1 (vanishing finite-action norm makes the extension sofic)
**Theorem 1.** Let `Gamma` be finitely presented and residually finite, `A` finite abelian, and `alpha` the class of
`Gamma~`. If `nu_fin(alpha) = 0`, then `Gamma~` is sofic. More precisely, there are finite `Gamma`-sets `V_n`, cochains
`b_n` and permutations `tau_n` of `V_n x A` giving a sofic approximation of `Gamma~`, with `A` translating the second
factor and the first factor an exact `Gamma`-action.

*Proof.*
1. **Small norm, free actions.**
   - Choose finite `Gamma`-sets `X_n` and cochains `b_n` with `nu_(X_n)(b_n) -> 0`.
   - `Gamma` is residually finite and countable, so there are finite-index normal `N_1 >= N_2 >= ...` with trivial
     intersection. Put `V_n = X_n x Gamma/N_n` and pull back `b_n`. By (M3) the defect fraction does not grow.
   - For `g != 1` and `n` large, `g ∉ N_n`, so `g` moves every point of `V_n`.
   - Credit: this is the residual amplification of Alekseev–Thom arXiv:2512.15494 Lemma 3.2, as recorded in
     `alekseev-thom-stability-finite-actions-boundary`.
2. **Permutations.** Set `tau_n(s)(v,t) = (s·v, t + b_n(s, s·v))` and `tau_n(a)(v,t) = (v, t+a)`. This defines a
   homomorphism from the free group on `S ∪ A` to `Sym(V_n x A)`.
   - The relations of `A` and the commutators `[a, s]` hold exactly.
   - For `r in R`, `tau_n(r)(v,t) = (r·v, t + hol_r(v)) = (v, t + hol_r(v))`, because the base action is exact. So
     `r = a_r` holds at `(v,t)` exactly when `(v,r)` is not defective, which fails on at most `|R| nu_n |V_n|` base
     points.
3. **Words trivial in `Gamma~` act almost trivially.** Let `w` be a word in `S ∪ A` equal to 1 in `Gamma~`. Its image
   in `Gamma` is 1, and moving its `A`-letters to the end (they commute exactly) gives `w' a` with `w'` a word in `S`
   and `a in A`.
   - A van Kampen diagram for `w'` over `<S | R>` has finitely many cells, all within a radius `C_w` of the base point.
   - Because the base action is exact, the diagram maps into `Y_(V_n)` at every base point `v`. The discrete Stokes
     formula then makes `hol_(w')(v)` the signed sum of the cell holonomies.
   - If no cell within radius `C_w` of `v` is defective, every cell contributes its `a_r`, so the sum is the value of
     `w'` on the lifts, which is `-a` since `w = 1`. Then `tau_n(w)(v,t) = (v, t)`.
   - At most `|B_(C_w)| |R| nu_n |V_n|` base points see a defective cell, so `tau_n(w)` is the identity outside a
     fraction `|B_(C_w)| |R| nu_n -> 0`.
4. **Nontrivial elements move almost everything.** Let `w` represent `g~ != 1` with image `g`.
   - If `g != 1`, `tau_n(w)` covers `g` acting on `V_n`, which moves every point for `n` large.
   - If `g = 1`, then `g~ = a in A ∖ 0`. As in step 3, `hol_(w')(v) + a` equals the value of `g~` in `A` outside the
     exceptional fraction, so `tau_n(w)(v,t) = (v, t + a) != (v,t)` there.
5. So `tau_n` is a sofic approximation of `Gamma~`. QED

**Model tests.**
- **Split extensions.** For `Gamma x A`, `b = 0` has no defect, and `Gamma x A` is sofic. The hypothesis holds.
- **Residually finite extensions.** If `Gamma~` is residually finite, then for a finite quotient `Gamma~ -> Q`
  injective on `A`, the set `X = Q/A` carries `b` with no defect. So `nu_fin(alpha) = 0`, and the conclusion matches.
- **Non-residually-finite extensions.** `nu_X(alpha) = 0` on some `X` would give an exact finite quotient of `Gamma~`
  injective on `A`. So `nu_X(alpha) > 0` for every `X`, and only the INFIMUM can vanish. The theorem is not vacuous
  and does not contradict Deligne.

## 3. Theorem 2 (stable bases: soficity iff vanishing norm)
**Theorem 2.** Let `Gamma` be finitely presented, residually finite and stable in finite actions (Gohla–Thom
Definition 3.7: the limit action of every sofic approximation is weakly contained in the finite `Gamma`-actions). Let
`A` be finite abelian and `alpha` the class of `Gamma~`. Then `Gamma~` is sofic iff `nu_fin(alpha) = 0`.

*Proof.*
- **`⇐`.** This is Theorem 1.
- **`⇒`.** Suppose `Gamma~` is sofic, and fix a sofic approximation.
  - Its limit is an `A`-free measured `Gamma~`-Boolean algebra `Q` (`A` is separated, since the approximation is
    sofic). Let `P = Q^A` be the induced limit `Gamma`-action. By Gohla–Thom Theorem 3.4, imported in
    `gohla-thom-class-norm-drops-under-weak-containment` item 2, `theta_*^P(alpha) = 0`.
  - `P` is the limit action of the induced sofic approximation of `Gamma`. By stability it is weakly contained in the
    family of finite `Gamma`-actions.
  - By Gohla–Thom Lemma 2.13 and Corollary 2.14 (item 1 of the same import),
    `0 = |||theta^P(alpha)||| >= inf_(X finite) |||theta^X(alpha)|||`.
  - On a finite action, `|||theta^X(alpha)|||` is the least Hamming measure of a cocycle representative. With a finite
    model whose 2-skeleton is the presentation complex, it is comparable to `nu_X(alpha)` up to model constants.
    So `nu_fin(alpha) = 0`. QED
- **Credit and scope.**
  - The `⇒` direction is Gohla–Thom's mechanism (their proof of Theorem 3.13) read as an equivalence. It needs no
    cosystolic inequality.
  - Their Theorem 3.13 is the contrapositive under a uniform lower bound: a cosystolic inequality gives
    `nu_fin(alpha) > 0`, and then `Gamma~` is not sofic.
  - Theorem 1 is the new `⇐` direction.

## 4. The Deligne triple cover
- **Setting.** `Gamma = Sp_4(Z)` is finitely presented and residually finite. `alpha in H^2(Sp_4(Z), Z/3)` classifies
  `E_3`, and `Res_fin(E_3) = C_3` (`deligne-covers-of-sp2g-z-have-finite-residual-2z`).
- **Corollary 3.** If `nu_fin(alpha) = 0` over `Sp_4(Z)`, then `E_3` is sofic. With
  `fp-sofic-kazhdan-non-rf-via-deligne-triple-cover` (PASS as an implication), this answers Alekseev–Thom Open
  problem 6.1 positively. Route: `deligne-triple-cover-sofic-from-vanishing-finite-norms`.
- **Corollary 4.** If `Sp_4(Z)` is stable in finite actions, then `E_3` is sofic iff `nu_fin(alpha) = 0`. So either
  `E_3` answers 6.1, or `Sp_4(Z)` supports a uniform Hamming lower bound for the Deligne class on all finite actions.
- **Reduction to congruence quotients (remark, import not read at source).**
  - By the congruence subgroup property for `Sp_4(Z)` (Mennicke 1965; Bass–Milnor–Serre, Publ. IHÉS 33 (1967), which
    treats `Sp_2n`, `n >= 2`; neither was re-read here), every finite-index subgroup contains some `Gamma(m)`.
  - By (M1) and (M2), `nu_fin(alpha) = inf_m nu_(Gamma/Gamma(m))(alpha)`. This is non-increasing along divisibility,
    so it is the limit along `Gamma(k!)`.
  - The new open claim is therefore exactly: the normalized Deligne-class cosystole on the principal congruence covers
    tends to 0 along a cofinal chain.
  - `main`'s condition C (`deligne-class-congruence-cosystole-bounded-below`) asks for a positive lower bound along SOME
    chain with trivial intersection, not necessarily cofinal. So C does not refute the new claim unless its chain is
    cofinal, and the new claim refutes C along every chain. The main existing node has no CSP import for `Sp_4`
    (`bms-congruence-kernel-trivial-not-totally-imaginary` covers `SL_n`), so this reduction stays a remark and is not
    a node.
- **What is known against the new claim.**
  - The detecting-cycle floors `4 nu / A_0(N)` and `[Gamma : N] <= m A_0(N)` are both compatible with vanishing, since
    `A_0(N) >= (sys(N) - 1)/(2 max |r|)` grows.
  - Cycle packing gives only `(log m)^-2`. Property (T) controls dimension 1.
  - Local patching is heuristic support for a positive bound, since non-amenable walls carry constant volume.
    Non-local constructions are not excluded.
- **What is known for it.**
  - `k[E_3]` is stably finite over `F_3`.
  - `E_3` is weakly sofic (Glebsky 2023).
  - No Følner-truncation or exact-monomial construction can realize the vanishing: the known dead ends all force a
    fixed exact module. Theorem 1 needs the cochains `b_n` to vary with `n`, which those dead ends do not cover.

## 5. What would decide it
- **For soficity.** Explicit small-support representatives of `alpha|Gamma(m)` on the congruence Borel–Serre models.
  A Maslov-cocycle representative mod 3 is supported on generic triples, so it must be corrected non-locally.
- **Against.** A two-dimensional cosystolic inequality for the congruence covers of `Sp_4(Z)` (a real rank-2 analogue
  of Kaufman–Mass / Evra–Kaufman), together with stability of `Sp_4(Z)` in finite actions, would make `E_3` nonsofic
  by Theorem 2. Neither input is known.

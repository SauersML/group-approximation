# Obstruction states for the 2V gate have one profile

Lane `w7-2v-mixed-support`, 2026-09-12. Artifact for `brin-thompson-2v-order-three-averaging-idempotent-is-full`
and `brin-thompson-2v-nonsurjunctive`.
- [H] is `research/artifacts/brin-thompson-2v-gottschalk-host-2026-09-12.md` (w6-free-neg-d; 4d9ce3b2d,
  a6d7e0a3d, ea9153822).
- [CS] is `research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md`.

## 0. Directive and outcome

After [H], the directive gave three options:
1. prove that 2V fullness is equivalent to V fullness;
2. find mixed-support relations over `H_mix = ⟨V ⊗ 1, 1 ⊗ h, u⟩` that kill the consistent values `b = 0` and
   `b = 2/9`;
3. build a state (firewall).

None of the three is decided. What is proved:
- **The value gap (Section 1).**
  - Every state of `K_0(F_2[2V])` has `b <= 2/9`, and the augmentation realizes `b = 0`.
  - If any state has `b > 0`, some state has `b = 2/9`. So the gate holds iff no state gives `e^(1)` the value
    `1/3`.
  - Such a state has the profile `(1/9, 2/9, 2/9, 4/9)` and `s[E_k] = 3^(-k)`.
  - The bound and the gap hold in every `D`-stable host of [CS] Theorem B, including `V` and the binary Leavitt
    units.
- **Precision on option 2 (Section 2).**
  - `b = 0` cannot be killed, and killing `b = 2/9` alone decides the gate.
  - The values `b` in `(2/9, 1/4]` that [H] Proposition 2.5 allows never occur.
- **Redundancy (Section 3).**
  - The 2V gate fails iff some state of `K_0(F_2[V])` with `s[e] = 1/3` is nonnegative on every class whose image
    in `K_0(F_2[2V])` is nonnegative.
  - Such states are `D`-invariant, and `D`-invariance can always be arranged.
  - No unital ring map from `F_2[⟨V ⊗ 1, u⟩]` into matrices over `F_2[V]` is diagonal on `V`.
  - The equivalence stays open.
- **The mixed host (Section 4).**
  - `1 ⊗ h` is conjugate to `1 ⊗ g` by `1 ⊗ k`, for an explicit `k` in `V`, so it adds no torsion class.
  - `H_mix <= ⟨H_u, 1 ⊗ k⟩`, and `H_u` already contains `1 ⊗ L_3`.

**Not duplicated.**
- `w6-v-extend` (0144b771c, `research/artifacts/v-rank-extension-to-ternary-leavitt-units-2026-09-12.md`) extends
  V rank functions to Leavitt units. Section 3 here extends `K_0` states, and from `V` to `2V`.
- `w7-v-cycle-c2` (ce8be16cd, `v-rank-functions-are-trivial-plus-regular-on-cylinder-groups`, OPEN) would give
  `rk(E_k) = φ_V + (1 - φ_V) 3^(-k)` for a Sylvester rank function on `F_2[V]`.
  - That is Theorem 1.1(a) for states that come from rank functions, with `s(v) = (1 - φ_V) · 2/3`.
  - Theorem 1.1 covers all states and does not use it.
- `w7-el3j-sofic` (07d43b6a3, `binary-jacobson-el3-is-sofic`) concerns `EL_3(J)`, which contains no `V`.

## 1. The value gap

**Setting.**
- Let `Γ` be a host for [CS] Theorem B: a `D`-stable subgroup of the units of `L_(F_2)(1,2)` containing `g` and
  the `π_M`, or `2V` ([H] Proposition 2.1).
- Put `A = F_2[Γ]`, with the notation of [CS] Section 1:
  - `p = [eA]`, `v = [fA]`, so `[A] = p + v`;
  - `p_k = [E_k A]` and `d_k = [(E_k - E_(k+1)) A]`;
  - `ψ'(x) = f D(x)`, and `ι_T` the inclusion of the corner `T = fAf`.

**Theorem 1.1.** Let `s` be a state of `(K_0(A), [A])` and put `x = s(v)`.
- (a) `s(p_(k+1)) = 1 - x (3^(k+1) - 1) / (2 · 3^k)` for every `k >= 0`. Hence `x <= 2/3`, that is `s[e] >= 1/3`.
- (b) If `x > 0`, then `s' = x^(-1) · s ∘ K_0(ι_T) ∘ K_0(ψ')` is a state with `s'(v) = 2/3`.
- (c) If `e` is not full in `A`, the values `s(v)` over all states form the interval `[0, 2/3]`. If `e` is full,
  they form `{0}`.
- (d) If `s(v) = 2/3`, then `s(p_k) = 3^(-k)` and `s(d_k) = 2 · 3^(-(k+1))` for every `k >= 0`.

*Proof.*
- (a)
  - `[A] = p + v` gives `s(p) = 1 - x`.
  - [CS] Lemma 1.2(b) gives `v = 3^k d_k`, so `s(d_k) = 3^(-k) x`.
  - [CS] Lemma 1.2(c) gives `p = p_(k+1) + ((3^k - 1)/2) d_k`. Substitute.
  - `p_(k+1)` is a class in `V(A)`, so its value is nonnegative. Letting `k -> ∞` gives `1 - 3x/2 >= 0`.
- (b)
  - `K_0(ι_T)` is positive and sends `[T]` to `v`. So `s_T = x^(-1) · s ∘ K_0(ι_T)` is a state of `(K_0(T), [T])`.
  - Step 4 => 5 of the proof of [CS] Theorem B shows that `s_T ∘ K_0(ψ')` is a state of `(K_0(A), [A])` with
    value `2/3` at `v`. The reason: `ψ'(f) = f_(K_3) + f_(K_4)`, and `f_(K_2)`, `f_(K_3)`, `f_(K_4)` are pairwise
    equivalent in `T` with sum `f`.
- (c)
  - The augmentation `ε : A -> F_2` is a unital ring map, so `dim ∘ K_0(ε)` is a state. It gives `[eA]` the value
    `ε(e) = 3 = 1`, and so gives `v` the value `0`.
  - States form a convex set and `s -> s(v)` is affine, so the values form an interval containing `0`.
  - The interval lies in `[0, 2/3]` by (a). By (b), it contains `2/3` as soon as it contains a positive value.
  - By [CS] Theorem B (1 <=> 4), `e` is full iff every state has `s(v) = 0`.
- (d) Put `x = 2/3` in (a) to get `s(p_(k+1)) = 3^(-(k+1))`. Also `s(p_0) = 1` and `s(d_k) = 3^(-k) x`. QED

**Remark 1.2.**
- **No averaging.** [CS] Proposition 4.1 normalizes states on `T` by Markov–Kakutani. Theorem 1.1 needs no fixed
  point, because (b) forces the value `2/3`, and (a) shows that no state exceeds it.
- **Not formal.** In a representation of `⟨g⟩ ≅ C_3` over `F_2` where `g` has no fixed vector, `e` acts as `0`. The
  bound `s[e] >= 1/3` comes from the tower (`D` and the `π_M`), not from `C_3` alone.
- **Rank functions.** A Sylvester matrix rank function on `A` gives a state on `K_0(A)`.
  - So every characteristic-two rank function on `F_2[Γ]` has `rk(1 + [g] + [g²]) >= 1/3`, and equality forces
    `rk(E_k) = 3^(-k)`.
  - For `Γ = V`, the open claim `v-rank-functions-are-trivial-plus-regular-on-cylinder-groups` would refine this to
    `rk(E_k) = φ_V + (1 - φ_V) 3^(-k)`.
- **Calibration.** The locally finite host `L_3` of [CS] Remark 2.2 realizes (d). Its regular rank gives `E_k` the
  value `1/|C_3^k| = 3^(-k)`.

**Corollary 1.3 (the 2V profile).** Let `A = F_2[2V]`, and let `a, b, c, d` be as in [H] Proposition 2.5.
- Every state has `b <= 2/9`.
- If the gate fails, the values of `b` over all states form `[0, 2/9]`. If it holds, they form `{0}`.
- A state with `b = 2/9` (equivalently `s[e^(1)] = 1/3`) has:
  - `(a, b, c, d) = (1/9, 2/9, 2/9, 4/9)`;
  - `s[E_k] = 3^(-k)`;
  - `s[E_(k-j) E_j^(2)] = 3^(-k)` for `0 <= j <= k`.

*Proof.* [H] Proposition 2.5 gives `s(v) = c + d = 3b` and `a = 1 - 4b`. Apply Theorem 1.1 to `Γ = 2V`. By [H]
Proposition 2.4(c), the mixed classes are the tower classes. QED

**Corollary 1.4 (the gate as one value).** `e^(1)` is full in `F_2[2V]` iff no state of `(K_0(F_2[2V]), [1])`
gives `e^(1)` the value `1/3`. A firewall needs one such state, and an obstruction has to exclude exactly this
profile.

## 2. Precision on the directive

- **`b = 0` cannot be killed.**
  - The augmentation state attains it (Theorem 1.1(c)), and exists on every group algebra. Other states can also
    have `b = 0`, and when the gate holds every state does.
  - It does not need killing either. A state with `b = 0` gives `v` the value `0`, so it induces no state on `T`.
- **`b` in `(2/9, 1/4]` never occurs.**
  - [H] Section 2 says that the finite-subgroup relations allow every `b` in `[0, 1/4]`. That is correct for those
    relations alone.
  - Positivity of the tower classes `p_(k+1)` in `V(A)` cuts the range to `[0, 2/9]`.
  - The verification of [H] (Section 29 of `research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`) is
    unaffected, because it checks consistency, not realizability.
- **Option 2 comes down to one value.** Relations over `H_mix` decide the gate iff they exclude `s[e^(1)] = 1/3`.
- **L1 check.**
  - The amenable host `L_3` realizes the profile ([CS] Remark 2.2).
  - By [H] Corollary 4.4, an exclusion using only `V_1 × V_2`, `H_u` or `⟨V_2, u⟩` would already decide
    `thompson-v-not-sofic`.
  - So an obstruction specific to `2V` must use a relation of `F_2[2V]` that holds in none of those hosts.

## 3. Redundancy: descending from 2V to V

**Setting.**
- Put `A_V = F_2[V]` and `ι_1 : A_V -> A = F_2[2V]`, `x -> x ⊗ 1`.
- The ascent (fullness over `V` gives fullness over `2V`) is the route
  `brin-thompson-2v-averaging-fullness-ascends-from-v`. The descent is open.
- By Theorem 1.1 for `Γ = V`, the V gate fails iff some state of `(K_0(A_V), [A_V])` gives `e` the value `1/3`.
  Call these *V-obstruction states*, and define *2V-obstruction states* likewise with `e^(1)`.

**Proposition 3.1 (restriction).** If `t` is a 2V-obstruction state, then `s = t ∘ K_0(ι_1)` is a V-obstruction
state with `s ∘ K_0(D_2) = s`.

*Proof.*
- `ι_1` is unital, so `s` is a state, and `s[e] = t[e^(1)] = 1/3`.
- [H] Lemma 2.3(b) gives `D_2(X) ⊗ 1 = u (X ⊗ 1) u^(-1)`. Apply it entrywise to an idempotent matrix `P` over
  `A_V`. Then `ι_1(D_2(P))` is conjugate to `ι_1(P)` by `u · 1_n`, so the two classes agree in `K_0(A)`. QED

**Proposition 3.2 (invariance is free).** If a V-obstruction state exists, then a `D_2`-invariant one exists.

*Proof.*
- The V-obstruction states form a nonempty closed convex subset `S` of the compact state space (Section 2, step 3
  of `research/artifacts/halving-invariant-k0-states-2026-09-12.md`).
- `D_2` is a unital injective ring endomorphism of `A_V`, so `Φ(s) = s ∘ K_0(D_2)` is a state.
- `Φ(s)[e] = s[D_2(e)] = s[e_(K_2)]`, and some `π_M` conjugates `e_(K_1) = e` to `e_(K_2)` ([CS] Section 0). So
  `Φ(S) ⊆ S`.
- `Φ` is affine and continuous, so Markov–Kakutani gives a fixed point in `S`. QED

**Proposition 3.3 (no diagonal descent map).** For no `n >= 1` is there a unital ring homomorphism
`ρ : F_2[H_u] -> M_n(A_V)` with `ρ(x ⊗ 1) = x · 1_n` for all `x` in `V`. So no such map is defined on `F_2[2V]`,
and no group retraction `2V -> V` restricts to the identity on `V_1`.

*Proof.*
- Put `w = ρ(u)`. By [H] Lemma 2.3(b), `w (x · 1_n) w^(-1) = D_2(x) · 1_n` for `x` in `V`.
- `D_2(x)` commutes with `g` ([H] Proposition 2.1, third input). So `c = w^(-1) (g · 1_n) w` commutes with `x · 1_n`
  for every `x` in `V`, and every entry of `c` is central in `A_V`.
- `V` is ICC, so the center of `A_V` is `F_2`, and `c` lies in `M_n(F_2)`.
  - `V` is simple and finitely generated (Cannon–Floyd–Parry, *Introductory notes on Richard Thompson's groups*,
    Section 6; not re-checked against the source here).
  - Its FC-center is normal, hence trivial or all of `V`.
  - If it were all of `V`, the center of `V` would have finite index (B. H. Neumann). That is impossible for an
    infinite simple nonabelian group.
- The augmentation, applied entrywise, is a ring map `M_n(A_V) -> M_n(F_2)`. It gives
  `c = ε(c) = ε(w)^(-1) 1_n ε(w) = 1_n`. So `g · 1_n = w c w^(-1) = 1_n` and `g = 1`, which is false. QED

**Proposition 3.4 (exact descent criterion).** Let `P` be the set of `y` in `K_0(A_V)` with `K_0(ι_1)(y) >= 0` in
`K_0(A)`. A 2V-obstruction state exists iff some V-obstruction state is nonnegative on `P`. Every such state is
`D_2`-invariant.

*Proof.*
- **Only if.** Restrict, as in Proposition 3.1. A restriction is nonnegative on `P` by construction.
- **If.**
  - Let `s` be nonnegative on `P`. `P` contains the kernel of `K_0(ι_1)`, which is a subgroup, so `s` vanishes on
    it.
  - So `s` defines an additive map on the image `Δ` of `K_0(ι_1)`. It has value `1` at `[A]` and is nonnegative on
    `Δ ∩ K_0(A)^+`.
  - A state on a subgroup containing the order unit, nonnegative for the relative preorder, extends to a state of
    the whole group. This is the Zorn and one-step Hahn–Banach argument in the proof of census Theorem A
    (`research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md`); see also Goodearl, *Partially
    ordered abelian groups with interpolation*, Chapter 4, not re-checked here.
  - The extension `t` has `t[e^(1)] = 1/3`.
- **Invariance.** `K_0(ι_1) ∘ K_0(D_2) = K_0(ι_1)` (proof of Proposition 3.1). So `K_0(D_2)(y) - y` lies in the
  kernel for every `y`, and `s` vanishes on it. QED

**Where descent stops.** Proposition 3.4 reduces redundancy to one question. Do the classes of `F_2[V]`-modules that
become nonnegative after induction to `F_2[2V]` exclude every V-obstruction state? The layers of `P` so far:
- **Halving.** `K_0(D_2)(y) - y` and its negative lie in `P`. Handled by Proposition 3.2.
- **The ascending union `N = ∪_n u^(-n) V_1 u^n`.** Handled.
  - `F_2[N]` is the colimit of `A_V` along `D_2`, and `K_0` commutes with filtered colimits.
  - A class is nonnegative there iff some `K_0(D_2)^m(y)` is nonnegative in `K_0(A_V)`, and a `D_2`-invariant
    state is nonnegative on such a class.
- **The crossed product `F_2[H_u] = F_2[N] ⋊ Z`.** Open. Projective `F_2[H_u]`-modules that are not induced from
  `F_2[N]` can add relations, so an invariant state on `K_0(F_2[N])` need not extend.
- **`V_2` and mixed support.** Open. No product construction for states on `K_0` of a tensor product of group
  algebras is available here.
- **No ring shortcut.** Proposition 3.3 rules out a diagonal ring map already at `H_u`, and the coefficient
  expectation `A -> A_V` is not multiplicative.

## 4. The mixed host H_mix = ⟨V ⊗ 1, 1 ⊗ h, u⟩

**Notation.**
- `h = (00, 01, 1) -> (01, 1, 00)`, as in [H] Remark 4.5.
- `H` without a subscript is the ternary index subgroup of [H] Lemma 4.1.

**Proposition 4.1.**
- (a) `k = s_(00) t_(0) + s_(01) t_(10) + s_(1) t_(11)` lies in `V`, and `k g k^(-1) = h`.
- (b) `1 ⊗ h = (1 ⊗ k) u^(-1) (g ⊗ 1) u (1 ⊗ k)^(-1)`.
  - So `H_mix <= ⟨H_u, 1 ⊗ k⟩`.
  - In `K_0(F_2[2V])`, the averaging idempotent of `1 ⊗ h` has class `[e^(2)] = [e^(1)]`.
- (c) Let `X` be a permutation unit of the `3^n` ternary cylinders of length `n`. Then `u^(-n) (X ⊗ 1) u^n = 1 ⊗ X'`,
  where `X'` permutes the same cylinders with the letter order reversed. So `1 ⊗ L_3 <= H_u`.
- (d) `1 ⊗ k` is not in `H_u`.

*Proof.*
- (a) `k` sends `w_1 x -> 00x`, `w_2 x -> 01x` and `w_3 x -> 1x`, between the complete prefix codes `{0, 10, 11}`
  and `{00, 01, 1}`. So `k g k^(-1)` sends `00x -> 01x -> 1x -> 00x`, which is `h`.
- (b) [H] Lemma 2.3(d) gives `u^(-1) (g ⊗ 1) u = 1 ⊗ g`. Conjugate idempotents have equal classes.
- (c)
  - By [H] Lemma 2.3(a), `u^(-1)` sends `(w_i x, y) -> (x, w_i y)`.
  - So for a ternary word `α` of length `n`, `u^(-n)` sends `(w_α x, y) -> (x, w_(α^rev) y)`.
  - Hence `u^(-n) (X ⊗ 1) u^n` sends `(x, w_(α^rev) y) -> (x, w_(X(α)^rev) y)`.
- (d) Otherwise `1 ⊗ h = (1 ⊗ k)(1 ⊗ g)(1 ⊗ k)^(-1)` lies in `H_u`, which contradicts [H] Remark 4.5. QED

**What this means for option 2.**
- In `K_0(F_2[2V])`, the averaging idempotents of `g`, `D_2^j(g)` and `h`, in either coordinate, all have the class
  `[e^(1)]`, because these elements are conjugate in `2V`. The profile fixes that class at `1/3`.
- So relations that only identify averaging idempotents of these conjugates cannot exclude the profile. An exclusion
  over `H_mix` needs a relation that is not a conjugation, for example one using elements of infinite order whose
  supports mix the coordinates.
- Section 6 computes the classes of partial-support torsion, such as `g` acting inside the cylinder `[w_1]` and
  trivially elsewhere. The regular values satisfy every identity found there.

## 5. Where it stops

- **Verified.** `w3-vf-nonlinear` re-derived Theorem 1.1, Corollaries 1.3–1.4, Propositions 3.1–3.4 and 4.1,
  Lemmas 6.1–6.2, Corollaries 6.3–6.4 and Remark 6.5, and PASSED them (verification artifact Section 31,
  83970f5256). Its two wording notes are applied in Section 2 and Remark 6.5.
- **Decided.** Nothing about the gate or the root; both stay OPEN.
- **Firewall.** It needs one state of `K_0(F_2[2V])` with `s[e^(1)] = 1/3`.
  - By Proposition 3.1 such a state restricts to a V-obstruction state, so a 2V firewall is at least as hard as the
    firewall for `thompson-v-order-three-averaging-idempotent-is-full`.
  - The only source of the value `1/3` known here is the regular rank of the amenable subgroup `L_3`.
- **Obstruction.** It needs a relation of `F_2[2V]` that excludes the profile of Corollary 1.3, using an element
  outside `V_1 × V_2`, `H_u` and `⟨V_2, u⟩`, such as `1 ⊗ h`. Finite-subgroup and tower relations cannot do it,
  because `L_3` satisfies them with the profile values.
- **Redundancy.** It needs a `D_2`-invariant V-obstruction state extended across `F_2[N] ⋊ Z` and the mixed
  support.
- **One next lead.** Test the profile against relations of `F_2[⟨H_u, 1 ⊗ k⟩]` whose words use `u` and `1 ⊗ k`
  together. This host contains `H_mix`, and `1 ⊗ k` is not in `H_u` (Proposition 4.1). No reduction of this host
  to `V` is known here.

## 6. Partial-support torsion (addendum)

**Setting.**
- `Γ` is a group and `A = F_2[Γ]`. For an idempotent `x` in a matrix ring over `A`, `[x]` is its class in `K_0(A)`.
- For a finite subgroup `F` of odd order, `e_F = Σ_(z in F) z` is an idempotent, because `e_F² = |F| e_F`.
- `g' = s_1 g t_1 + s_2 t_2 + s_3 t_3` acts as `g` inside `[w_1]` and fixes `[w_2] ∪ [w_3]`. Put `e' = e_(⟨g'⟩)`.

**Lemma 6.1 (line count).** Let `P ≅ C_3^n` with `n >= 1` be a subgroup of `Γ`, and let `K` run over its
`(3^n - 1)/2` subgroups of order three. Then in `K_0(A)`:
`Σ_K [e_K] = ((3^(n-1) - 1)/2) [1] + 3^(n-1) [e_P]`.

*Proof.*
- `F_2[P]` is commutative and semisimple, and `F_2[P] ≅ F_2 × F_4^m` with `m = (3^n - 1)/2`.
  - The factor `F_2` is cut out by `e_P`.
  - Each factor `F_4` is cut out by an idempotent `ε_H`, where `H` is the kernel of the characters `P -> F_4^×`
    realizing it.
  - Factors correspond bijectively to subgroups `H` of index three. A character with kernel `H` factors through
    `P/H ≅ C_3`, which has one Galois orbit of nontrivial characters.
- `e_K` acts on the factor of `H` as `3 = 1` if `K <= H`, and as `1 + ω + ω² = 0` otherwise. So
  `e_K = e_P + Σ_(H ⊇ K) ε_H` is an orthogonal sum.
- Each `H` contains `(3^(n-1) - 1)/2` subgroups of order three, and `Σ_H [ε_H] = [1] - [e_P]`.
- Summing over `K` gives `m [e_P] + ((3^(n-1) - 1)/2)([1] - [e_P])`, and `m - (3^(n-1) - 1)/2 = 3^(n-1)`. QED

**Lemma 6.2 (two torsion classes).**
- (a) A finite subgroup `F <= V` permutes the cylinders of some finite partition of `C`, and each element acts on
  each cylinder by prefix replacement.
- (b) An element of order three in `V` is conjugate in `V` to `g` if it has no fixed point in `C`, and to `g'`
  otherwise.
- (c) Suppose two elements of order three in `2V` each permute the product cylinders of a finite partition of `C × C`
  by prefix replacement in both coordinates, in three-cycles only. Then they are conjugate in `2V`, and so conjugate
  to `g ⊗ 1`.

*Proof.*
- (a) **An invariant partition.**
  - Choose a finite cylinder partition `Q` on which every `x` in `F` acts by prefix replacements `αz -> βz`. Put
    `δ_x(z) = |β| - |α|` for `z` in `[α]`.
    - Refining `Q` does not change it, so it is well defined and locally constant.
    - `δ_(xy)(z) = δ_x(yz) + δ_y(z)`.
  - Put `λ(z) = L - min_(x in F) δ_x(z)`, where `L` is the length of the longest word of `Q`.
    - `λ(z) >= L`, because `δ_1 = 0`.
    - The cocycle identity gives `λ(xz) = λ(z) + δ_x(z)`.
  - `λ` is constant on the cylinder `[z|λ(z)]` of the first `λ(z)` letters, so these cylinders form a finite
    partition.
  - `x` maps `[z|λ(z)]` onto a cylinder of length `λ(z) + δ_x(z)` that contains `xz`, by prefix replacement. That
    cylinder is `[xz|λ(xz)]`.
- (b) **Conjugacy.**
  - By (a) for `⟨x⟩`, an element `x` of order three permutes a partition by prefix replacements. It does so in
    `c_3 >= 1` three-cycles and `c_1` fixed cylinders, and it has a fixed point iff `c_1 >= 1`.
  - Halving the three cylinders of one three-cycle raises `c_3` by one. Halving one fixed cylinder raises `c_1` by
    one. Both keep the action by prefix replacement.
  - So if `x` and `x'` have `c_1 = 0` for both, or `c_1 >= 1` for both, they permute partitions with equal cycle
    counts.
  - Choose a bijection of the two partitions that intertwines the permutations, and apply it by prefix replacement
    on each cylinder. The result is some `ρ` in `V` with `ρ x ρ^(-1) = x'`.
  - `g` permutes `{[w_1], [w_2], [w_3]}` with `(c_3, c_1) = (1, 0)`.
  - `g'` permutes `{[w_1 w_1], [w_1 w_2], [w_1 w_3], [w_2], [w_3]}` with `(c_3, c_1) = (1, 2)`.
- (c) Use the argument of (b) with product cylinders halved in either coordinate. `g ⊗ 1` permutes
  `{[w_i] × C}` in one three-cycle. QED

**Corollary 6.3 (values in V).** Let `s` be a state of `(K_0(F_2[V]), [1])`, `t = s[e]` and `y = s[e']`.
- (a) `s[e_K] = t` for every subgroup `K` of order three without fixed points, and `s[e_K] = y` for the others.
- (b) **Tower.**
  - Every subgroup of order three of `C_3^n` ([CS] Section 1) is fixed-point-free.
  - So Lemma 6.1 gives `3^(n-1) s(p_n) = ((3^n - 1)/2) t - (3^(n-1) - 1)/2`.
  - This is Theorem 1.1(a) with `x = 1 - t`, derived from Lemmas 6.1–6.2 without [CS] Lemma 1.2.
- (c) **Partial class.** `1/3 <= y <= (1 + 2t)/3`. At an obstruction state (`t = 1/3`), `y` lies in `[1/3, 5/9]`.

*Proof.*
- (a) Conjugate idempotents have equal classes. Apply Lemma 6.2(b).
- (b) `C_3^n` translates the length-`n` cylinders freely, so no nontrivial element has a fixed point.
- (c)
  - Fix `n >= 2` and the complete prefix code `α_j = 0^(j-1) 1` for `j < n`, `α_n = 0^(n-1)`.
  - Let `a_j` act as `g` inside `[α_j]` and trivially elsewhere. The `a_j` commute and generate `P_n ≅ C_3^n`.
  - `a_1^(c_1) ... a_n^(c_n)` has a fixed point iff some `c_j = 0`. So `2^(n-1)` subgroups of order three are
    fixed-point-free and `(3^n - 1)/2 - 2^(n-1)` are not.
  - By Lemma 6.1 and (a),
    `((3^n - 1)/2 - 2^(n-1)) y + 2^(n-1) t = (3^(n-1) - 1)/2 + 3^(n-1) s[e_(P_n)]`.
  - `e_(P_n) e_K = e_(P_n)` for `K <= P_n`, so `e_K - e_(P_n)` is an idempotent. Take `K` fixed-point-free to get
    `0 <= s[e_(P_n)] <= t`.
  - Divide by `3^(n-1)` and let `n -> ∞`. Then `s[e_(P_n)] -> (3y - 1)/2`, so `0 <= (3y - 1)/2 <= t`. QED

**Corollary 6.4 (a mixed product in 2V).** Let `s` be a state of `(K_0(F_2[2V]), [1])`, `t = s[e^(1)]` and
`y = s[e' ⊗ 1]`. Then `s[(e' ⊗ 1)(1 ⊗ e)] = (y + 3t - 1)/3`. At the profile of Corollary 1.3 (`t = 1/3`), this is
`y/3 = s[e' ⊗ 1] · s[1 ⊗ e]`.

*Proof.*
- `P = ⟨g' ⊗ 1, 1 ⊗ g⟩ ≅ C_3²`, and `e_P = (e' ⊗ 1)(1 ⊗ e)`.
- `⟨1 ⊗ g⟩ = u^(-1) ⟨g ⊗ 1⟩ u` ([H] Lemma 2.3(d)), so its value is `t`.
- `g' ⊗ g` and `g' ⊗ g²` permute the fifteen product cylinders `[β] × [w_i]` in three-cycles only. Here `β` runs over
  the partition of `g'` in Lemma 6.2(b). By Lemma 6.2(c), both elements are conjugate to `g ⊗ 1`, so their values
  are `t`.
- `⟨g' ⊗ 1⟩` has the value `y`. Lemma 6.1 with `n = 2` gives `y + 3t = 1 + 3 s[e_P]`. QED

**Remark 6.5 (what partial support can and cannot do).**
- **No exclusion.**
  - Put `s[e_F] = 1/|F|` on every finite subgroup `F`, via normalized dimension in the regular representation.
    Normalized dimension is compatible with induction and conjugation, so these values form a family of
    normalized dimensions on the `K_0(F_2[F])`, over the finite subgroups `F` of `V` (or `2V`), compatible with
    inclusion and conjugation. The finite subgroups do not form a directed system (two involutions can generate an
    infinite dihedral group), and the argument uses only this compatibility.
  - It gives `t = y = 1/3` and satisfies Lemma 6.1 and Corollaries 6.3–6.4 (`1/9 = 3^(-2)`).
  - So no identity that every such compatible family satisfies excludes the profile, partial support included.
- **Calibration sharpened.**
  - The counting rank of `L_3` on the length-2 cylinders gives `e'` the value `7/9`, which violates 6.3(c) at
    `t = 1/3`. So it does not extend to a state of `K_0(F_2[V])`.
  - The regular rank of Remark 1.2 is the one compatible with conjugacy in `V`.
- **For a firewall.** A state with `s[e] = 1/3` must give the partial class a value in `[1/3, 5/9]`, and
  `(e' ⊗ 1)(1 ⊗ e)` one third of it.
- **For an obstruction.** Nothing new. An exclusion needs a relation that does not come from finite subgroups, as in
  Section 4.

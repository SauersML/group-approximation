---
rg: 2
id: rover-nekrashevych-fp-iff-finite-lift-presentation-proof
kind: route
title: Run Nekrashevych's normal-form argument with an arbitrary finite self-similar generating set, and detect relators in the fraction group of F modulo a lift ideal
target: rover-nekrashevych-fp-iff-finite-lift-presentation
requires:
  - rover-nekrashevych-finite-presentation-criteria
---

Notation is that of the claim. The one import is Nekrashevych, *Finitely presented groups associated with expanding
maps*, arXiv:1312.5654, proof of Theorem 5.9 (pp. 28–31 of the arXiv version, read 2026-09-18). That proof uses the
nucleus `𝒩` only as a finite generating set closed under sections and inverses, except in its last sentence. That
sentence invokes relations (N) and Propositions 5.2–5.3 to kill products of nucleus elements that are trivial in
`G`. Below, `S` replaces `𝒩` throughout, and §2 isolates exactly what replaces that last sentence.

## 0. Cone copies

- For `v in X^*` and a homeomorphism `f` of `X^ω`, `L_v(f)` acts as `vw ↦ v f(w)` on `vX^ω` and as the identity
  elsewhere. For `v ≠ ∅` and `f in V_d(G)`, `L_v(f) in V_d(G)`.
- Fix the letter `x_1 = 0` and write `L = L_0`. For every nonempty `v`, Nekrashevych fixes a word `A_v` in the
  generators `Σ` of `V_d` with `A_v(0w) = vw`. For a word `W` in `L(S)`, `L_v(W)` denotes the word
  `A_v · W · A_v^{-1}`.
- For `h in V_d` and `u, v in X^*` with `h(uw) = vw` for all `w`: `h L_u(g) h^{-1} = L_v(g)` in `V_d(G)`.

## 1. Lift ideals

**(1a) Basic facts.**

- `N` is a lift ideal. It is normal. If `w` has trivial root permutation and every `w|_x` is trivial in `G`, then
  `w` acts trivially.
- `K_∞ ⊆ M` for every lift ideal `M`. Put `K_0 = 1` and let `K_{n+1}` be the set of words with trivial root
  permutation and all `w|_x in K_n`. Then `K_n ⊆ M` by induction, and `K_∞ = ∪_n K_n`.
- `K_∞` is itself a lift ideal:
  - each `K_n` is normal, because `(uwu^{-1})|_x` is conjugate to `w|_{u^{-1}(x)}`;
  - `K_∞` is lift-closed, because `X` is finite, so the sections of `w` lie in one `K_n`.
  - Hence `K_∞ = ⟨⟨∅⟩⟩_lift`.

**(1b) Section closure.** Let `R ⊆ N` be closed under word-level sections. Then `M = ⟨⟨R⟩⟩_lift` is closed under
sections and `M ⊆ N`.

- `M ⊆ N` because `N` is a lift ideal containing `R`.
- Let `T = {w in M : every iterated section of w lies in M}`. Then `R ⊆ T`.
- Every element of `M` acts trivially on `X^*`, since `M ⊆ N`. So for `w, w' in M`:
  - `(ww')|_x = w|_x w'|_x` and `(w^{-1})|_x = (w|_x)^{-1}`, hence `T` is a subgroup;
  - `(uwu^{-1})|_x = u|_{x} · w|_{x} · (u|_{x})^{-1}` up to the relabelling `x = u^{-1}(x')`, which is a conjugate
    of a section of `w`. Iterating, `T` is normal.
- If `w` has trivial root permutation and every `w|_x in T`, then `w in M` by lift-closure. Every iterated section
  of `w` is `w` itself or an iterated section of some `w|_x`, so it lies in `M`. So `T` is lift-closed.
- Thus `T` is a lift ideal containing `R`, so `T ⊇ M`, and `M = T` is section-closed.

**(1c) Finite section closure.** A word-level section of a word of length `ℓ` in `S^{±1}` has length at most `ℓ`,
because `S` is closed under sections. So each `w in F` has finitely many reduced iterated sections. For a finite
`R ⊆ N`, the set `R'` of all reduced iterated sections of elements of `R` is finite and lies in `N`, and
`⟨⟨R⟩⟩_lift ⊆ ⟨⟨R'⟩⟩_lift ⊆ N`.

**(1d) Injective recursion.** Let `M ⊆ N` be a section-closed lift ideal and `Q = F/M`. Then `ψ` descends to a
homomorphism `ψ_Q: Q -> Q ≀ Sym(X)`, and `ψ_Q` is injective.

- It descends because every `w in M` has trivial root permutation and sections in `M`.
- It is injective because `ψ_Q(wM) = 1` says that `w` has trivial root permutation and sections in `M`, so `w in M`.
- Iterating, `ψ_Q^{(n)}: Q -> Q ≀ Sym(X^n)` is injective for every `n`.

## 2. The group `V̂` and its relator kernel

Let `V̂` be the group with generators `Σ ∪ L(S)` and relations:

- a finite set `R_V` of defining relations of `V_d` (Higman);
- (C) and (S) of the claim. These are Nekrashevych's (C) and (S) with `S` in place of `𝒩`: finitely many, because
  `S` and the chosen generating set `W_0` of the pointwise fixer of `0X^ω` in `V_d` are finite.

All of them hold in `V_d(G)`, so there is a surjection `π: V̂ -> V_d(G)`. It is surjective by Nekrashevych's
Lemma 5.12, whose proof uses only that `S` generates `G`. Since `R_V` presents `V_d`, the subgroup `⟨Σ⟩ <= V̂` is
`V_d`. Lemmas 5.13 and 5.14 hold in `V̂` verbatim; their proofs use only (C) and `R_V`:

- **(5.13)** `h L_u(g) h^{-1} = L_v(g)` whenever `h in V_d` and `h(uw) = vw`;
- **(5.14)** `L_u(g)` and `L_v(g')` commute for incomparable `u, v`.

For a word `w in F` write `L(w)` for the corresponding product of the `L(s)^{±1}`.

**(2a) Word splitting.** For every `w in F`, in `V̂`,

`L(w) = h_w · ∏_{x in X} L_{0x}(w|_x)`,

where `h_w in V_d` maps `0xu ↦ 0 w(x) u` and is the identity off `0X^ω`. The factors commute by (5.14).

- *Letters.* For `s in S` this is (S).
- *Inverse letters.* Invert (S) and move `h_s^{-1}` to the front with (5.13), since
  `h_s L_{0x}(g) h_s^{-1} = L_{0 s(x)}(g)`. This gives `L(s)^{-1} = h_s^{-1} ∏_y L_{0y}((s|_{s^{-1}(y)})^{-1})`.
  Here `h_s^{-1} = h_{s^{-1}}` and `(s|_{s^{-1}(y)})^{-1} = s^{-1}|_y`.
- *Products.* If the formula holds for `u` and `v`, then:
  - `∏_x L_{0x}(u|_x) · h_v = h_v ∏_y L_{0y}(u|_{v(y)})`, by (5.13);
  - regrouping by (5.14), `L(uv) = h_u h_v ∏_y L_{0y}(u|_{v(y)} v|_y) = h_{uv} ∏_y L_{0y}((uv)|_y)`.

**(2b) Lift ideals from normal subgroups.** Let `R ⊆ F` and let `𝔑 = ⟨⟨L(R)⟩⟩_{V̂}`. Then
`M_𝔑 = {w in F : L(w) in 𝔑}` is a lift ideal, so `⟨⟨R⟩⟩_lift ⊆ M_𝔑`.

- `w ↦ L(w)𝔑` is a homomorphism `F -> V̂/𝔑`, and `M_𝔑` is its kernel. So `M_𝔑` is normal.
- *Lift-closed.* Suppose `w` has trivial root permutation and every `w|_x in M_𝔑`.
  - Then `h_w` is the identity of `V_d`, hence of `V̂`.
  - By (2a), `L(w) = ∏_x L_{0x}(w|_x)`.
  - Each factor `L_{0x}(w|_x) = A_{0x} L(w|_x) A_{0x}^{-1}` lies in `𝔑`.

**(2c) The kernel of `π`.** `ker π = ⟨⟨L(N)⟩⟩_{V̂}`.

- `⊇` is clear.
- For `⊆`, follow Nekrashevych's proof after Lemma 5.14 word for word.
  - Relations (S′) (the cone-`v` form of (S), from (S) and (5.13)) and (5.13) put any element in the form
    `g = h L_{v_1}(s_1) ··· L_{v_m}(s_m)`, with `h in V_d` and all `|v_i| = k`.
  - If `π(g) = 1`, then `h` preserves length-`k` prefixes. Regrouping by (5.13)–(5.14) gives `g = ∏_{v in X^k} f_v`,
    where `f_v = L_v(h_v) L_v(W_v)`, `h_v in V_d` and `W_v = s_{v,1} ··· s_{v,m_v}` is a word in `S`.
  - Each `f_v` is trivial in `V_d(G)`. So `h_v` coincides with the action of `W_v^{-1}` on `X^ω`.
  - An element of `V_d` has a table with trivial labels. Hence for some `l` the element `W_v` has all its level-`l`
    sections trivial in `G`, and `h_v in Symm(d^l)` undoes the level-`l` permutation of `W_v`.
  - Splitting `L_v(W_v)` `l` times by (2a) (in its cone-`v` form) gives
    `f_v = L_v(h_v h'_v) ∏_{u in X^l} L_{vu}(W_v|_u)`, with `h'_v in V_d` the level-`l` permutation of `W_v`.
  - Here `h_v h'_v = 1` in `V_d`, and each `W_v|_u in N`. So `f_v in ⟨⟨L(N)⟩⟩`.
  - This is the point where Nekrashevych instead invokes (N) and Propositions 5.2–5.3.

## 3. Sufficiency

Suppose `N = ⟨⟨R⟩⟩_lift` with `R` finite. By (2b), with `𝔑 = ⟨⟨L(R)⟩⟩`, we get `N ⊆ M_𝔑`, so
`L(N) ⊆ 𝔑`. With (2c), `ker π = 𝔑`. Hence `V_d(G) = V̂/⟨⟨L(R)⟩⟩`, a finite presentation, and it is the one displayed
in the claim.

## 4. Necessity

Suppose `V_d(G)` is finitely presented.

**(4a) Finitely many relators.** `V̂` is finitely presented and `V_d(G) = V̂/ker π`. By B.H. Neumann, finite
presentability does not depend on the finite generating set, so `ker π` is the normal closure of finitely many
elements `k_1, ..., k_m`. By (2c), each `k_i` is a product of finitely many conjugates of elements `L(n)^{±1}` with
`n in N`. Collecting these `n` gives a finite `R ⊆ N` with `ker π = ⟨⟨L(R)⟩⟩`. Replace `R` by its finite section
closure `R'` from (1c). Since `R ⊆ R' ⊆ N`, still `ker π = ⟨⟨L(R')⟩⟩`.

Put `M = ⟨⟨R'⟩⟩_lift`. By (1b), `M ⊆ N` and `M` is section-closed. By (1d), `Q = F/M` has injective recursion
`ψ_Q`. Write `q ↦ q(x)` for the root permutation of `q in Q` and `q|_x` for its sections. It remains to show that
`N ⊆ M`.

**(4b) The table group `V_d(Q)`.** `Q` need not act faithfully on `X^*`. So `V_d(Q)` is built from tables, as for
cloning systems (Witzel–Zaremsky, *Thompson groups for systems of groups*) and Brin's categories of fractions.

- A **table** is a bijection `v_i ↦ u_i` between two complete prefix codes `{v_i}`, `{u_i}` of `X^*`, with a label
  `q_i in Q` on each entry. Write it as `{(v_i, q_i, u_i)}`. Heuristically it is `v_i w ↦ u_i q_i(w)`.
- **Expanding** entry `i` replaces `(v_i, q_i, u_i)` by the `d` entries `(v_i x, q_i|_x, u_i q_i(x))`, for
  `x in X`. The result is again a table.
- *Confluence.* Expansions at different entries commute. Hence any two iterated expansions of one table have a common
  iterated expansion. So "having a common iterated expansion" is an equivalence relation. `V_d(Q)` is the set of
  classes.
- *Refining either side.* Expanding entry `i` refines the domain leaf `v_i` into `{v_i x}` and the range leaf `u_i`
  into `{u_i y}`, since `x ↦ q_i(x)` is a bijection. So a table can be expanded until its domain code, or its range
  code, refines any given complete prefix code.
- *Product.* To form `σ·τ`, expand `τ` and `σ` until the range code of `τ` equals the domain code of `σ`. Then
  compose entrywise: `(v, q, u)` in `τ` and `(u, p, u')` in `σ` give `(v, pq, u')`.
  - This is well defined because expansion commutes with entrywise composition. Expanding the composite gives
    `(vx, (pq)|_x, u' (pq)(x)) = (vx, p|_{q(x)} q|_x, u' p(q(x)))`.
  - That is the composite of `τ`'s expanded entry `(vx, q|_x, u q(x))` with `σ`'s expanded entry
    `(u q(x), p|_{q(x)}, u' p(q(x)))`. This is where `ψ_Q` being a homomorphism is used.
- *Group structure.* The product is associative. The identity is `{(∅, 1, ∅)}`, and the inverse of `{(v_i, q_i, u_i)}`
  is `{(u_i, q_i^{-1}, v_i)}`.
- *`V_d` inside.* Tables with all labels `1` compose exactly as the tables of elements of `V_d`. So they form a copy
  of `V_d` in `V_d(Q)`, and the relations `R_V` hold there.

**(4c) Detecting the identity.** Call a table *diagonal* if every entry has the form `(v, q, v)`.

- If a diagonal table has some label `q ≠ 1`, then so does every iterated expansion of it.
  - Expanding `(v, q, v)` gives `(vx, q|_x, v q(x))`.
  - By injectivity of `ψ_Q`, `q ≠ 1` means either `q(x) ≠ x` for some `x`, or `q|_x ≠ 1` for some `x`.
  - In the first case the expansion is not diagonal. In the second it is diagonal with a nontrivial label, and we
    induct. A non-diagonal table stays non-diagonal under expansion.
- Iterated expansions of `{(∅, 1, ∅)}` are exactly the diagonal tables with all labels `1`.
- Hence a diagonal table represents the identity of `V_d(Q)` only if all its labels are `1`.

**(4d) The comparison map `Θ`.** For a nonempty `v` and `q in Q`, let `T_v(q)` be the diagonal table with the entry
`(v, q, v)` and entries `(c, 1, c)` on a complete prefix code of the complement of `vX^ω`. Its class does not depend
on that code.

- `T_v(q) T_v(p) = T_v(qp)`.
- Tables supported on disjoint unions of cones commute. Expand both to a common code refining the supports and
  their complement, and compose entrywise.

Define `Θ` on generators by sending `Σ` to their label-`1` tables and `L(s)` to `T_0(s̄)`, where `s̄ = sM`. Then:

- For `h in V_d` with `h(uw) = vw`, conjugating by the label-`1` table `h` gives `h T_u(q) h^{-1} = T_v(q)`. In
  particular `Θ(L_v(W)) = T_v(W̄)` for every word `W` and every nonempty `v`, using `A_v(0w) = vw`.
- `R_V` holds by (4b).
- (C) holds by the disjoint-support commutation. The pointwise fixer of `0X^ω` in `V_d` consists of label-`1`
  tables with identity entries on a code of `0X^ω`.
- (S) holds.
  - Expanding the entry `(0, s̄, 0)` of `T_0(s̄)` gives the entries `(0x, s̄|_x, 0 s(x))`, where
    `s̄|_x = (s|_x)M` by the definition of `ψ_Q`.
  - The right side `h_s ∏_x T_{0x}((s|_x)M)` composes to the same table.
- `Θ(L(r)) = T_0(r̄) = T_0(1) = 1` for `r in R'`, since `R' ⊆ M`.

So `Θ` is a homomorphism `V̂ -> V_d(Q)` that kills `⟨⟨L(R')⟩⟩ = ker π`.

**(4e) Conclusion.** Let `w in N`.

- `L(w) in ker π ⊆ ker Θ`.
- `Θ(L(w)) = T_0(wM)`, since `Θ` is a homomorphism and the `T_0` compose.
- By (4c), `wM = 1`, that is `w in M`.

Therefore `N = M = ⟨⟨R'⟩⟩_lift` with `R'` finite. ∎

**Remark.** The same maps show more. Let `R ⊆ N` be finite and section-closed, and put `M = ⟨⟨R⟩⟩_lift`. Then
`V̂/⟨⟨L(R)⟩⟩` surjects onto `V_d(F/M)`, and `L(w)` dies in `V̂/⟨⟨L(R)⟩⟩` exactly when `w in M`: `⊇` by (2b),
`⊆` by (4c)–(4e). So each finite section-closed `R` gives a finitely presented group, and these approximate
`V_d(G)` from above through the lift ideals `⟨⟨R⟩⟩_lift`.

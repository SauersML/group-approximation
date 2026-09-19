---
rg: 2
id: pure-loop-self-replicating-groups-are-not-fp-proof
kind: route
title: Proof that finite presentation of a fully self-replicating group is a retraction of the stable presentation along T_k, that Kurosh then forbids free splittings into proper-image factors, and that occurrence tracking makes the stable relators of pure-loop unit-weight recursions pure, killing R°, R' and R_gamma
target: pure-loop-self-replicating-groups-are-not-fp
requires:
  - m11-balanced-loop-host-is-not-finitely-presented
  - m11-balanced-loop-host-has-finite-h1
  - m11-separated-loop-host-has-b1-one
  - fp-quotient-iff-kernel-finitely-normally-generated
  - tits-hosts-for-transitive-local-actions
artifacts:
  - experiments/stable-retract-criterion-2026-09-18/pure_stable_part_checks.py
  - experiments/stable-retract-criterion-2026-09-18/pure_stable_part_checks.out
---

**Status: ESTABLISHED (unreviewed).** Items 1–3 and 5 are proved by hand. Item 4 uses the
script for these finite facts:
- the conditions (U), (A'), (B'), (C'') and (D) for each recursion;
- the orders 55 and 220 of the finite-order loop letters, and the sections of their powers;
- the orbit that proves `b_g α` has infinite order.

The script decides the word problem exactly: a word is trivial iff every word in its free
section closure has trivial root permutation, and that closure is finite because sections do
not raise the weight.

**Conventions.** Right actions: `(uv)|_x = u|_x v|_{x^u}`. Points are `1, …, 11`; the script
codes them `0, …, 10`. For a free word, its *level-`n` action* is the action of its image
in `G` on `X^n`. If `u` and `u'` both act trivially on level `n`, then
`(uu')|_v = u|_v u'|_v` for `|v| = n`, as free words after reduction. So on words that act
trivially on level `n`, `w ↦ w|_v` is a homomorphism.

## 1. Item 1 (retract criterion)

`σ^k(w)` represents `w̄@1^k`, which acts trivially on level `k`. By the convention above,
`T_k(w) = σ^k(w)|_{1^k}` is multiplicative, and `T_k(w^{−1}) = T_k(w)^{−1}`. So `T_k` is an
endomorphism of `F`. A free section represents the section of the image, and
`(w̄@1^k)|_{1^k} = w̄`. So `T_k(w)` represents `w̄`.

*If.* Let `Q ⊆ K` be finite with `T_k(K) ⊆ N_Q = ⟨⟨Q⟩⟩`, and put `H = F/N_Q`. Then `T_k`
induces `τ : G → H`. Let `ρ : H ↠ G` be the quotient map. Then `ρτ(w̄) = w̄`, so `ρτ = id`.
Let `M` be the normal closure in `H` of the finite set `{s^{−1} τρ(s) : s ∈ S}`. Then
`M ⊆ ker ρ`. Modulo `M`, every generator equals an element of `τ(G)`, so `H/M = τ(G)M/M`.
`ρ` is injective on `τ(G)`, so `ker ρ = M`. Hence `G = H/M` is finitely presented. Section
closure of `Q` is not used in this direction.

*Only if.* Let `K = ⟨⟨R⟩⟩` with `R` finite. `σ^k(w)` represents `w̄@1^k`, which is `1` for
`w ∈ K`, so `σ^k(K) ⊆ K`. By the stable-relator lemma
(`m11-balanced-loop-host-is-not-finitely-presented`, item 1), `σ^k(w)|_{1^k} ∈ ⟨⟨Q^∞⟩⟩`
for `k ≥ k_0`. `Q^∞` is finite. It is section-closed, because
`Q^{(k_0+1)} = Q^{(k_0)}` says its nonempty level-1 sections are exactly `Q^∞`. ∎

## 2. Item 2 (free-splitting obstruction)

**`G` is one-ended.**
- `G` is nontrivial, and `|G| = |G|^{|X|}·|P|`, so `G` is infinite. It is finitely
  generated.
- `G^X = G × G^{X∖{x}}` has finite index in `G`. It is a direct product of two infinite
  finitely generated groups, so it is one-ended (cited, standard).
- The number of ends is a commensurability invariant. So `G` is one-ended.
- By Stallings' theorem `G` is not a nontrivial free product, and it is not infinite cyclic.

**Kurosh.** Let `S = S_1 ⊔ S_2` be as in item 2, and let `Q_i ⊆ F(S_i)` be conjugates of the
words of `Q^∞`. Then `Γ = Γ_1 * Γ_2`, with `Γ_i = F(S_i)/⟨⟨Q_i⟩⟩`.
- `τ` from §1 (with `Q = Q^∞`) embeds `G` as `H = τ(G) ≤ Γ`.
- By the Kurosh subgroup theorem, `H` is a free product of a free group and of subgroups
  `H ∩ gΓ_ig^{−1}`.
- `H ≅ G` is freely indecomposable and not `Z`. So `H ≤ gΓ_ig^{−1}` for some `g` and `i`.
- Then `G = ρ(H) ≤ ρ(g) ρ(Γ_i) ρ(g)^{−1}`. So `ρ(Γ_i) ⊇ ρ(g)^{−1}Gρ(g) = G`, and
  `ρ(Γ_i) = ⟨S_i⟩_G = G`.

If both `⟨S_1⟩_G` and `⟨S_2⟩_G` are proper, there is a contradiction. So `G` is not finitely
presented. ∎

## 3. Item 3 (pure-loop class)

*Rooted* letters have all sections empty. *State* letters have some nonempty section. The
*weight* of a word is its number of state letters. By (U), `wt(u|_x) ≤ wt(u)`, and
`|u|_x| ≤ L·wt(u)` with `L` the longest letter section. So (SF) holds. Assume `G = F/⟨⟨R⟩⟩`
with `R` finite, and let `u ∈ Q^∞`.

**(a) A self-section.** Every word of `Q^∞` is a level-1 section of a word of `Q^∞` (§1). So
there is an infinite chain `u = u_0, u_1, u_2, …` in `Q^∞` with `u_j = u_{j+1}|_{x_j}`.
`Q^∞` is finite, so `u_i = u_{i'}` for some `i < i'`. Then `u_i = u_i|_v` with `|v| ≥ 1`,
and `u = u_i|_{v'}`.

**(b) Occurrence tracking.** Write `u_i|_v` before free reduction. By (U), each state
occurrence `o` of `u_i` contributes at most one state occurrence, and rooted letters
contribute nothing. Since `wt(u_i|_v) = wt(u_i)`, this map is a bijection `π` from state
occurrences to state occurrences, and no state letter cancels in the reduction.
- `π` is a permutation of a finite set. So each occurrence `o` returns to itself after
  `π^r = id`.
- The edges used along `v` by `o, π(o), …` therefore form a closed walk in the graph of
  weight-preserving sections. Every edge on a closed walk lies on a directed cycle, so it
  is cycle-capable.
- By (B'), each such edge section is a single state letter.

So the first-step section `u_i|_{v_1}` is state-only, and hence so is `u_i = u_i|_v`.

**(c) A single loop letter.** Let `x = v_1`, and let the first letter of `u_i` be `s^{±1}`.
- Its section is read on a cycle-capable edge `(s, y)`, with `y = x` for `s` and
  `y = x^{π_s^{−1}}` for `s^{−1}`. By (C''), `π_s` fixes `y`, so `y = x`, and `π_s` fixes `x`.
- The next letter `t^{±1}` is therefore read at `x` as well. For `t^{−1}` the edge is
  `(t, x^{π_t^{−1}})`. It is cycle-capable, so `π_t` fixes that point, which is then `x`.
- So in every case `t` has a cycle-capable section at `x`, and `t = s` by (C'').

Inductively `u_i` is a reduced word in `s^{±1}`, so `u_i = s^j` with `j ≠ 0`.

**(d) Purity.** `u_i ∈ K`, so `s` has finite order `o` dividing `j`. `s^o` acts trivially on
every level, so `(s^o)^{j/o}|_{v'} = (s^o|_{v'})^{j/o}`. By (D) the word `s^o|_{v'}` is pure,
hence so is its power `u`.

**(e) Conclusion.** Let `S_st` and `S_rt` be the state and rooted letters. Every word of `Q^∞`
lies in `F(S_st)` or `F(S_rt)`.
- `⟨S_rt⟩_G` is a group of rooted automorphisms, isomorphic to its permutation group. It is
  finite, hence proper.
- Every element of `⟨S_st⟩_G` has root permutation in `P_st ≠ P`, so `⟨S_st⟩_G` is proper.

Item 2 now shows `G` is not finitely presented. ∎

## 4. Item 4 (instances)

The theorem does not depend on the free basis: `G`, `K`, `P` and self-replication are
unchanged by a Nielsen move, and the new letters get the letter sections of their images.
In all cases below, `α, β` are rooted with `⟨α, β⟩ = M_11`, and `P = M_11` has order 7920.

- **`R°`.**
  - It is fully self-replicating (`m11-balanced-loop-host-has-finite-h1`, item 3).
  - Script: the cycle-capable edges are `b|_1 = b`, `C|_4 = C` and `C|_6 = C^{−1}`.
    `P_st = 1`. `ord(b) = 55`, and the iterated sections of `b^55` are `b^55`, `α^55` and
    `β^55`, which are pure.
  - `C` has infinite order (same node, item 1).
- **`R'`.**
  - It is fully self-replicating, and `c'` has infinite order
    (`m11-separated-loop-host-has-b1-one`, items 1–2).
  - Script: the cycle-capable edges are `b|_1` and `c'|_4 = c'`. `P_st = 1`. (D) holds as
    for `R°`.
- **`R''`.** Script: `b` and `c` are both cycle-capable at `1`, so (C'') fails. Nothing
  new is claimed.
- **`R_γ`.** Here `γ = αβ^{−1}`. The script prints its root permutation, which fixes
  `1, 2, 3`.
  - *Fully self-replicating.* For `a ∈ Stab_{M_11}(1)`, `h_a = b_g^{−1} a b_g a^{−1}` has
    sections `s_x^{−1} s_{x^a}`, where `s_x = b_g|_x`. At `x = 1` the section is `1`. For
    `x ≠ 1`, both `x` and `x^a` differ from `1`, and there `s_x` equals `b|_x` of `R_0`. So
    `⟨h_a⟩ = 1 × M_11^{10}`, exactly as in `tits-hosts-for-transitive-local-actions`
    item 6 (B).
    - Hence `c@x ∈ R_γ` for all `c ∈ M_11` and all `x`.
    - `(γb_g)@1 = b_g·((α@2)(β@3))^{−1}`, so `b_g@1 ∈ R_γ`, and `⟨M_11, b_g⟩` is fully
      self-replicating.
    - Steps 2–3 of `m11-balanced-loop-host-has-finite-h1-proof` then apply verbatim, with
      `b_gα` for `bα`: they use only the shape of `C` and the elements `π, π_1 ∈ M_11`.
  - *Nielsen move.* Put `g = γb_g`. Then `g|_x = b_g|_{x^γ}`, so `g = (g, α, β, 1, …)·γ`,
    and `C|_5 = b_gα = γ^{−1}gα`.
  - Script, in the basis `{α, β, g, C}`:
    - (U) holds.
    - `P_st = ⟨γ⟩` has order 4.
    - The cycle-capable edges are `g|_1 = g`, `C|_4` and `C|_6`, which gives (B') and (C'').
    - `ord(g) = 220`, and the iterated sections of `g^220` are `g^220`, `α^220` and `β^220`.
  - In the original basis, (B') fails (`b_g|_1 = γb_g`). This is why the move is needed.
  - *`C` has infinite order.* Since `C^m|_5 = (b_gα)^m`, it suffices that `b_gα` has
    infinite order. For `h = b_gρ` with `ρ ∈ M_11`, let `ℓ` be the length of the `ρ`-cycle
    of `1`.
    - Then `h^ℓ|_1 = γ b_g τ`, where `τ` is the product of `α` and `β` met at `2` and `3`
      along that cycle. Conjugating by `γ` gives `b_g f(ρ)` with `f(ρ) = τγ`.
    - The other cycles give rooted sections. So if `ord(h) = n < ∞`, then `ℓ | n` and
      `ord(b_g f(ρ))` divides `n/ℓ`.
    - The script finds that the `f`-orbit of `α` is eventually periodic, with cycle lengths
      `5, 11` on the period. If `b_gα` had finite order, the order `n*` of `b_gρ*` at a
      point `ρ*` of the period would satisfy `n* ≥ 55·n*`, which is impossible.
    - The same check with `γ = 1` recovers the known infinite order of `bα` in `R_0`.
- **Tits hosts.** `R'` and `R_γ` are fully self-replicating with root image `M_11`. So
  `tits-hosts-for-transitive-local-actions` gives finitely generated simple hosts, finitely
  presented iff `R'`, resp. `R_γ`, is. Neither is finitely presented. ∎

## 5. Item 5 (design rule)

- The first sentence restates items 2 and 3.
- `τ(G) ≅ G` contains every finitary automorphism whose vertex permutations lie in `P`,
  since `P ≤ G` is rooted and `G@v ⊆ G`. This group is infinite and locally finite, and it
  contains `P^{X^n}` for every `n`.
  - A hyperbolic group has no infinite torsion subgroup.
  - A torsion-free subgroup of finite index would meet it trivially, so it would embed in
    a finite quotient.
  - A locally finite subgroup of `GL_d(C)` has an abelian normal subgroup of index at most
    `J(d)` (Jordan). But `P^{X^n}`, a power of a nonabelian simple group, has no nontrivial
    abelian normal subgroup.
- `C'(1/6)` presentations are hyperbolic, so none is available for any `Q` in item 1.
- When `P` is transitive, `G` is level-transitive and `G^{X^n} ≤ G` has finite index, so
  `G` is regular branch over itself. A finitely presented example would then answer the
  Bartholdi–Grigorchuk–Šunić question. ∎

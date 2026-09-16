# Twisted-power cloning groups on finite groups have faithful context-free actions

Swarm lane for `zaremsky-2-16-lehnert-conjecture`, hole
`cloning-system-groups-on-finite-groups-embed-in-v`, 2026-09-16.

## 0. Statement

Throughout, `G` is a finite group with identity `e`, and `φ0, φ1 ∈ End(G)`
satisfy

    ker φ0 ∩ ker φ1 = {e}.                                         (K)

**Theorem.**

(a) `G_n = G^n`, with `ι_{m,n}(g_1,…,g_m) = (g_1,…,g_m,e,…,e)`, trivial
    representation maps `ρ_n`, and cloning maps
    `κ^n_k(g_1,…,g_n) = (g_1,…,g_{k-1}, φ0(g_k), φ1(g_k), g_{k+1},…,g_n)`,
    is a cloning system on finite groups (Witzel–Zaremsky, Def. 2.18).

(b) The group `𝒱 = 𝒱_(G,φ0,φ1)` of Section 4 (refinement classes of labelled
    triple lists) is finitely generated and has a faithful action with finitely
    many orbits whose loop languages are context-free. Hence `𝒱` embeds in
    Thompson's group `V` (claim `faithful-context-free-action-groups-embed-in-v`).

(c) The Thompson-like group `T(G_*)` of the cloning system in (a) is isomorphic
    to a subgroup of `𝒱`, hence embeds in `V`.

For `φ0 = id` the group `𝒱` is the group `V_(H,θ)`, `H = G`, `θ = φ1`, in the
triple-list description of Bodart–D'Angeli–Perego–Rodaro (arXiv:2608.02111v1,
§3.1, p. 17: `(a_i,b_i,h_i)` is replaced by `(a_i0,b_i0,h_i), (a_i1,b_i1,(h_i)θ)`,
and composition multiplies labels after matching codes), so (b) recovers their
Theorem 3.2. The proof below follows the same strategy (a wreath-type action and
a pushdown automaton with a decorated stack), but uses points of the form
`x p^∞` for several periods `p` and an argument (Lemma 3.1) replacing the
triviality of `ker φ0`. Cases not of the form `φ0 = id` include two arbitrary
automorphisms, or `G = (Z/2)^2` with the two coordinate projections
`(x,y) ↦ (x,0)`, `(x,y) ↦ (0,y)` (neither injective). It was not checked whether
some of these groups are isomorphic to groups `V_(H,θ)` or are covered by BDPR's
Theorem 3.5 on FSS groups. The
Zaremsky-guide variation of the direct-power example (two self-monomorphisms of
`G`, arXiv:1606.08762, Example 3.1) is the case of (c) with both `φ` injective.

## 0.1 Conventions and two facts about endomorphisms

Words are over `{0,1}`; `""` is the empty word. For `u = c_1…c_ℓ` put
`φ_u := φ_{c_ℓ} ∘ … ∘ φ_{c_1}` (apply `c_1` first), `φ_"" = id`. Thus

    φ_{uv} = φ_v ∘ φ_u.                                            (0.1)

`S := {φ_u : u ≠ ""} ⊆ End(G)` is a finite semigroup, `S^1 := S ∪ {id}`, and
`E(S)` is its (nonempty) set of idempotents. For `f ∈ End(G)` let `f^ω` be the
unique idempotent power of `f` (it exists because `{f^n : n ≥ 1}` is finite).
Let `N := |G|`.

**Fact 0.2.** For `f ∈ End(G)`: `ker f^n = ker f^N` for all `n ≥ N`, and
`ker f^ω = ker f^N`. Consequently, for `h, h' ∈ G`:
`f^n(h) = f^n(h')` for some `n ≥ 0` iff `f^ω(h) = f^ω(h')`.

*Proof.* `ker f^0 ⊆ ker f^1 ⊆ …` is a chain of subgroups. If
`ker f^{n+1} = ker f^n` and `f^{n+2}(x) = e` then `f(x) ∈ ker f^{n+1} = ker f^n`,
so `x ∈ ker f^{n+1}`; hence once the chain stops growing it is constant. Each
strict step at least doubles the order, so it is constant from `n = N` on. If
`f^ω = f^k` (`k ≥ 1`) then `f^{kn} = f^k` for all `n ≥ 1`, so
`ker f^ω = ker f^{kN} = ker f^N`. Finally `f^n(h) = f^n(h')` iff
`h^{-1}h' ∈ ker f^n ⊆ ker f^N = ker f^ω`, and conversely `f^ω` is a power of `f`. ∎

## 1. The cloning system and the triple-list model

**Proof of (a).** All `G_n` are finite and the `ι_{m,n}` are injective and
compatible. The `κ^n_k` are homomorphisms; `κ^n_k(g) = (e,…,e)` forces
`g_k ∈ ker φ0 ∩ ker φ1` and `g_j = e` for `j ≠ k`, so (K) makes them injective.
Condition (2.5) of Witzel–Zaremsky (arXiv:1405.5491, p. 18): for `g ∈ G^m` and
`k ≤ m`, padding to length `n` and then cloning at `k` gives the same `(n+1)`-tuple
as cloning at `k` and then padding; for `m < k` one clones an entry `e` into
`(φ0(e), φ1(e)) = (e,e)`, which is `ι_{m,n+1}`. With `ρ` trivial, (FCS1)
`(gh)κ_k = (g)κ_{ρ(h)k}(h)κ_k` says that `κ_k` is a homomorphism; (FCS2)
(cloning at `ℓ` then at `k < ℓ` equals cloning at `k` then at `ℓ+1`) holds
because both act on disjoint coordinates in the same way; (FCS3) holds because
both sides are the identity permutation. ∎

**Codes and lists.** A *complete prefix code* is a finite set `A ⊂ {0,1}^*` such
that every infinite binary sequence has exactly one prefix in `A` (the leaf set
of a finite rooted binary tree; `{""}` is allowed). Every word of length
`≥ max_{a∈A} |a|` has exactly one prefix in `A`, and every word either has a
prefix in `A` or is a proper prefix of an element of `A`. Every complete prefix
code is obtained from `{""}` by successively replacing an element `a` by `a0, a1`.
For a word `x = c_1…c_ℓ` the *path code*
`{x} ∪ {c_1…c_{j-1} c̄_j : 1 ≤ j ≤ ℓ}` (`c̄` = the other letter) is a complete
prefix code of size `ℓ+1` containing `x`.

A *triple list* is `g = {(a_i, b_i, h_i) : 1 ≤ i ≤ n}` where
`A = {a_i}`, `B = {b_i}` are complete prefix codes of size `n` (the domain and
range codes), `i ↦ (a_i,b_i)` is a bijection `A → B`, and `h_i ∈ G`. It is
*F-type* if `a_i ↦ b_i` preserves the lexicographic order. The *elementary
refinement* at `i` replaces `(a_i,b_i,h_i)` by `(a_i0, b_i0, φ0(h_i))` and
`(a_i1, b_i1, φ1(h_i))`; `≈` is the equivalence relation generated by elementary
refinements. If the range code of `g = {(a_i,b_i,h_i)}` equals the domain code
of `k = {(b_i,c_i,k_i)}` (*matching codes*) put

    g·k := {(a_i, c_i, h_i k_i)}.                                   (1.1)

Any `g, k` have refinements with matching codes: refine every triple of `g` whose
range word is shorter than `L` and every triple of `k` whose domain word is shorter
than `L` until both codes are `{0,1}^L`, where `L` bounds all word lengths. Put
`g^{-1} := {(b_i, a_i, h_i^{-1})}`; then `g·g^{-1} = {(a_i,a_i,e)}` literally, and
`{(a_i,a_i,e)} ≈ {("","",e)} =: 1` because `φ_c(e) = e`.

**Lemma 1.2 (dictionary with `T(G_*)`).** Sending a triple `(T_-, g, T_+)`
(`T_±` binary trees with `n` leaves, `g = (h_1,…,h_n) ∈ G^n`) to the list
`{(a_k, b_k, h_k)}`, where `a_1 < … < a_n` and `b_1 < … < b_n` are the leaf
addresses of `T_-`, `T_+` in left-to-right order, is a bijection onto the F-type
lists. By the guide (arXiv:1606.08762, §5.1, p. 9), elements of `T(G_*)` are the
classes of such triples under the symmetric transitive hull of expansions, where an
expansion adds a caret to the `k`-th leaf of `T_+` and to the `ρ_n(g)k`-th leaf of
`T_-` and replaces `g` by `(g)κ_k`. Here `ρ` is trivial, so this is the `k`-th leaf
on both sides, and an expansion corresponds exactly to the elementary refinement at
`k`. The guide's product (§5.1: expand to `[T'_-, g', S]` and `[S, h', U'_+]`
and put `[T'_-, g', S][S, h', U'_+] := [T'_-, g'h', U'_+]`) corresponds to (1.1).

*Proof.* Splitting the `k`-th leaf of a tree replaces its `k`-th leaf address `a`
by `a0 < a1` in the same position, and `κ_k` replaces `h_k` by
`φ0(h_k), φ1(h_k)`. An elementary refinement or its inverse keeps an F-type list
F-type (and a non-F-type list non-F-type), so a chain of moves connecting two
F-type lists stays among F-type lists, i.e. the classes of `T(G_*)` (equivalence
generated by expansions) correspond to `≈`-classes of F-type lists. ∎

## 2. The spaces `Ω_p` and the action

Fix a nonempty word `p`. On `X := G × {0,1}^*` let
`j_p(h,x) := (φ_p(h), xp)`, and let `(h,x) ∼_p (h',x')` iff
`j_p^m(h,x) = j_p^{m'}(h',x')` for some `m, m' ≥ 0`. This is an equivalence
relation (for transitivity: if `j^m ξ = j^{m'} η` and `j^n η = j^{n'} ζ` then
`j^{m+n} ξ = j^{m'+n} η = j^{m'+n'} ζ`). Put `Ω_p := X/∼_p`, write `[h,x]_p` for
classes, and `e_p := (φ_p)^ω`.

**Lemma 2.1.**
(i) `[h,x]_p = [h',x]_p` iff `e_p(h) = e_p(h')`.
(ii) `[h,x]_p = [e,""]_p` iff `x ∈ p^*` and `e_p(h) = e`.
(iii) If `x p^m ≠ x' p^{m'}` for all `m, m' ≥ 0`, then `[h,x]_p ≠ [h',x']_p`
      for all `h, h'`.

*Proof.* (iii) is immediate from the definition. (i): `j^m(h,x) = j^{m'}(h',x)`
forces `m = m'` (compare lengths) and `φ_p^m(h) = φ_p^m(h')`; use Fact 0.2 in
both directions (`e_p` is a power `φ_p^k`, `k ≥ 1`). (ii): if
`j^m(h,x) = j^{m'}(e,"") = (e, p^{m'})` then `x p^m = p^{m'}`, so `x` is the
prefix of `p^{m'}` of length `(m'-m)|p|`, i.e. `x = p^{m'-m}`, and
`φ_p^m(h) = e`, so `e_p(h) = e` by Fact 0.2. Conversely, if `x = p^r` and
`e_p = φ_p^k` kills `h`, then `j^k(h,p^r) = (e, p^{r+k}) = j^{r+k}(e,"")`. ∎

**Definition of the action.** Let `g = {(a_i,b_i,h_i)}` with domain code `A`, and
`ξ = [h,x]_p`. Choose `m ≥ 0` such that `x p^m` has a prefix in `A` (any `m` with
`|x p^m| ≥ max|a_i|` works), write `x p^m = a_i u` (`i` is unique), and put

    ξ·g := [ φ_p^m(h) · φ_u(h_i) ,  b_i u ]_p.                      (2.1)

**Lemma 2.2.** (2.1) does not depend on `m`, on the representative `(h,x)`, or on
the representative of the `≈`-class of `g`.

*Proof.* *m.* If `m` is admissible then so is `m+1`, with `x p^{m+1} = a_i (up)`,
and by (0.1) the value is
`[φ_p^{m+1}(h) φ_{up}(h_i), b_i u p] = [φ_p(φ_p^m(h) φ_u(h_i)), (b_i u) p]`,
the `j_p`-image of the value for `m`. Admissible `m` form an up-set, so all give
the same class.
*Representative.* `∼_p` is generated by `(h,x) ↦ j_p(h,x) = (φ_p(h), xp)`. Using
`m ≥ 1` for `(h,x)` and `m-1` for `(φ_p(h), xp)` produces the same word
`a_i u` and the same element `φ_p^{m-1}(φ_p(h)) φ_u(h_i)`.
*Refinement at `i`.* Take `m` with `|x p^m| > max|a_j|`. If `x p^m = a_i u` then
`u = c u'` with `c ∈ {0,1}`, and the refined list uses the triple
`(a_i c, b_i c, φ_c(h_i))`, giving `[φ_p^m(h) φ_{u'}(φ_c(h_i)), b_i c u']`;
by (0.1) `φ_{u'} ∘ φ_c = φ_{cu'} = φ_u`, so the value is unchanged. Points
whose prefix is some `a_j`, `j ≠ i`, are unaffected. ∎

**Lemma 2.3.** (a) `ξ·1 = ξ`. (b) If `g, k` have matching codes, then
`(ξ·g)·k = ξ·(g·k)`. (c) Every list acts bijectively, with inverse `g^{-1}`.

*Proof.* (a) `x p^m = "" u` gives `[φ_p^m(h), x p^m] = [h,x]`. (b) With
`x p^m = a_i u`, `ξ·g = [h', b_i u]` where `h' = φ_p^m(h) φ_u(h_i)`; applying
`k = {(b_i,c_i,k_i)}` to this representative with `m = 0` gives
`[h' φ_u(k_i), c_i u] = [φ_p^m(h) φ_u(h_i k_i), c_i u] = ξ·(g·k)`, since `φ_u` is a
homomorphism. (c) `g·g^{-1} ≈ 1` and `g^{-1}·g ≈ 1`, so (a), (b) and Lemma 2.2
apply. ∎

For a finite set `P` of nonempty words let `Ω := ⊔_{p∈P} Ω_p` and let
`μ(g) ∈ Sym(Ω)` be `ξ ↦ ξ·g` (permutations compose left to right). By
Lemmas 2.2–2.3, `μ` is constant on `≈`-classes, `μ(g·k) = μ(g)μ(k)` for matching
codes, `μ(1) = id` and `μ(g^{-1}) = μ(g)^{-1}`.

## 3. Faithfulness

**Lemma 3.1.** Let `M := {h ∈ G : t(s(h)) = e for all t ∈ E(S), s ∈ S^1}`.
Under (K), `M = {e}`.

*Proof.* `M` is an intersection of kernels, hence a subgroup. It is
`φ_c`-invariant: for `h ∈ M`, `t ∈ E(S)`, `s = φ_u ∈ S^1`, we have
`t(s(φ_c(h))) = t(φ_{cu}(h)) = e` by (0.1). Let `ψ_c := φ_c|_M ∈ End(M)` and
let `T` be the finite semigroup generated by `ψ0, ψ1`; its elements are the
restrictions `φ_u|_M`, `u ≠ ""`, and restriction commutes with composition. Let
`z : M → M` be the constant map to `e`; it is a two-sided zero of `End(M)`.

*The only idempotent of `T` is `z`.* If `τ = φ_u|_M` is idempotent, then
`f := φ_u ∈ S`, `f^ω ∈ E(S)` and `f^ω|_M = τ^ω = τ`; taking `s = id` in the
definition of `M` gives `f^ω(M) = {e}`, so `τ = z`. Since `T` is finite it has an
idempotent, so `z ∈ T`.

*`T` is nilpotent.* Let `n := |T|` and `u = u_1…u_n`. Put
`τ_j := φ_{u_1…u_j}|_M` (`1 ≤ j ≤ n`). If some `τ_j = z` then
`φ_u|_M = φ_{u_{j+1}…u_n}|_M ∘ z = z`. Otherwise `τ_1,…,τ_n` lie in the
`(n-1)`-element set `T ∖ {z}`, so `τ_i = τ_j` for some `i < j`. With
`σ := φ_{u_{i+1}…u_j}|_M ∈ T` we get `τ_i = σ ∘ τ_i`, hence `τ_i = σ^r ∘ τ_i`
for all `r ≥ 1`, hence `τ_i = σ^ω ∘ τ_i = z ∘ τ_i = z`, a contradiction. So
`φ_u(M) = {e}` for every word of length `n`.

*Iterated cloning is injective.* Let `Φ_n : G → G^{{0,1}^n}`,
`Φ_n(h) := (φ_u(h))_{|u|=n}`. `Φ_0 = id`, and `Φ_{n+1}(h)_{uc} = φ_c(Φ_n(h)_u)`.
If `Φ_{n+1}(h) = Φ_{n+1}(h')`, then for each `u` the element
`Φ_n(h)_u^{-1} Φ_n(h')_u` lies in `ker φ0 ∩ ker φ1 = {e}`, so `Φ_n(h) = Φ_n(h')`;
by induction `Φ_n` is injective for all `n`. For `h ∈ M`, `Φ_n(h) = Φ_n(e)` with
`n = |T|`, so `h = e`. ∎

**Lemma 3.2.** Let `P` contain, for each `t ∈ E(S)`, a nonempty word `p_t` with
`φ_{p_t} = t`. If `μ(g) = id` for `g = {(a_i,b_i,h_i)}`, then `a_i = b_i` and
`h_i = e` for all `i` (literally, not only up to `≈`).

*Proof.* Fix `i`.
*`a_i = b_i`.* Suppose not, and pick any `p ∈ P`.
(1) If neither of `a_i, b_i` is a prefix of the other, take `ξ = [e, a_i]_p`; then
`ξ·g = [h_i, b_i]_p`, and `a_i p^m`, `b_i p^{m'}` differ at the first position where
`a_i` and `b_i` differ, so `ξ·g ≠ ξ` by Lemma 2.1(iii).
(2) If `b_i = a_i v` with `v ≠ ""`, choose `u ∈ {0,1}^{|v|}` with `u ≠ v` and take
`ξ = [e, a_i u]_p`, so `ξ·g = [φ_u(h_i), a_i v u]_p`. If
`a_i u p^m = a_i v u p^{m'}` then `u p^m = v u p^{m'}`; both sides have length
`≥ |v| = |u|`, and their prefixes of that length are `u` and `v`, a contradiction.
So `ξ·g ≠ ξ` by Lemma 2.1(iii).
(3) If `a_i = b_i v` with `v ≠ ""`, apply (2) to `g^{-1}`, which contains
`(b_i, a_i, h_i^{-1})` and satisfies `μ(g^{-1}) = id`.
*`h_i = e`.* Now all `a_j = b_j`. For `p ∈ P` and any word `u`, take
`ξ = [e, a_i u]_p`; then `ξ·g = [φ_u(h_i), a_i u]_p`, and `ξ·g = ξ` gives
`e_p(φ_u(h_i)) = e` by Lemma 2.1(i). For `t ∈ E(S)` and `p = p_t`,
`e_p = t^ω = t`. Hence `t(s(h_i)) = e` for all `t ∈ E(S)` and `s ∈ S^1`, i.e.
`h_i ∈ M = {e}` (Lemma 3.1). ∎

Such `P` exists and is finite: `E(S)` is finite and every element of `S` is some
`φ_u`, `u ≠ ""`. Fix such a `P` from now on.

## 4. The group `𝒱` and the subgroup `T(G_*)`

Let `𝒯` be the set of all triple lists and `𝒱 := μ(𝒯) ⊆ Sym(Ω)`. Since any two
lists have refinements with matching codes, `𝒱` is closed under products; it
contains `id = μ(1)` and `μ(g)^{-1} = μ(g^{-1})`. So `𝒱` is a subgroup of
`Sym(Ω)`.

**Lemma 4.1.** `μ(g) = μ(k)` iff `g ≈ k`. Hence `𝒯/≈` with the product
`[g][k] := [g'·k']` (`g' ≈ g`, `k' ≈ k` with matching codes) is a well-defined
group, and `μ` induces an isomorphism `𝒯/≈ → 𝒱`.

*Proof.* "If" is Lemma 2.2. Suppose `μ(g) = μ(k)`. Refine to `g' ≈ g`, `k' ≈ k`
with the same range code `{b_i}`, and write `g' = {(a_i, b_i, h_i)}`,
`k' = {(c_i, b_i, k_i)}`. Then `g'` and `k'^{-1} = {(b_i, c_i, k_i^{-1})}` have
matching codes, and `d := g'·k'^{-1} = {(a_i, c_i, h_i k_i^{-1})}` has
`μ(d) = μ(g)μ(k)^{-1} = id`. By Lemma 3.2, `a_i = c_i` and `h_i = k_i` for all `i`,
so `g' = k'` and `g ≈ k`. The product on classes is then well defined because `μ` is
multiplicative on matching codes, and the induced bijection `𝒯/≈ → 𝒱` is an
isomorphism. ∎

**Proof of (c).** By Lemma 1.2 the elements of `T(G_*)` are the `≈`-classes of
F-type lists with the product of Lemma 4.1. By Lemma 4.1, `μ` restricted to these
classes is an injective homomorphism into `𝒱`. ∎

## 5. Orbits and finite generation

**Lemma 5.1.** Each `Ω_p`, `p ∈ P`, is a single `𝒱`-orbit; so `𝒱` has `|P|`
orbits on `Ω`.

*Proof.* Let `[h,x]_p, [h',x']_p ∈ Ω_p`; replacing representatives by `j_p`-images
we may assume `x, x' ≠ ""`. The path codes of `x` and `x'` contain an element other
than `x` (resp. `x'`); splitting such elements equalises the sizes, giving complete
prefix codes `A ∋ x`, `B ∋ x'` with `|A| = |B|`. Let `g` contain the triple
`(x, x', h^{-1}h')` and pair the other elements of `A` and `B` arbitrarily with
label `e`. By (2.1) with `m = 0`, `u = ""`: `[h,x]_p·g = [h h^{-1} h', x']_p`. ∎

**Lemma 5.2.** `𝒱` is finitely generated.

*Proof.* The lists with all labels `e` are closed under refinement and (1.1), and
their classes form Thompson's group `V` (pairs of complete prefix codes with a
bijection, modulo splitting); `μ` restricted to them is a homomorphism from `V`, and
`V` is finitely generated (claim `thompson-v-finitely-presented-infinite-simple`).
Let `W` be its image, and for `h ∈ G` let `λ_h := {("0","0",h), ("1","1",e)}`. We
show `𝒱 = ⟨W, μ(λ_h) : h ∈ G⟩`. Let `g = {(a_i,b_i,h_i)}`. Literally
`g = {(a_i,b_i,e)}·{(b_i,b_i,h_i)}`, and `d := {(b_i,b_i,h_i)}` is the product of
the lists `d_i` with the same code, label `h_i` at `b_i` and `e` elsewhere. If
`|B| = 1`, first refine `d` to `{("0","0",φ0(h_1)), ("1","1",φ1(h_1))}`, which is
also such a product; so assume `|B| ≥ 2`. Fix `b = b_i`. Let `C` be a complete
prefix code with `|C| = |B|` and `"0" ∈ C` (e.g. `"0"` together with `"1"`
followed by a code of size `|B|-1`), and let `v = {(b_j, c_j, e)}` be a label-free
list with `b ↦ "0"`. Let `δ := {(c_j, c_j, ·)}` have label `h_i` at `"0"` and `e`
elsewhere. Then `v·δ·v^{-1} = d_i` literally, and `δ ≈ λ_{h_i}` (refine
`("1","1",e)`). So `μ(d_i) = μ(v) μ(λ_{h_i}) μ(v)^{-1}`. ∎

## 6. The loop languages are context-free

Let `A` be any finite set of triple lists, regarded as an alphabet (for example
representatives of a finite symmetric generating set of `𝒱`, with or without
formal inverse letters). For `w = g_1…g_ℓ ∈ A^*` write `ξ·w := ξ·g_1·…·g_ℓ`.
Fix `p ∈ P`, `ξ_p := [e,""]_p`, and

    L_p := { w ∈ A^* : ξ_p·w = ξ_p }.

**Proposition 6.1.** `L_p` is context-free.

*Proof.* Let `L_A` be the maximum length of a domain or range word in a letter of
`A`. The stack alphabet is `Σ := ({0,1} × End(G)) ⊔ {#}` (finite). A stack
word `(s_1,κ_1)…(s_r,κ_r)#` (top first) is *correctly decorated* if
`κ_j = φ_{s_j s_{j+1} … s_r}` for all `j`; it is determined by `x = s_1…s_r`, and
we write it `x̂#`. If a word `y = y_1…y_q` is pushed on top of a correctly decorated
stack whose top letter has decoration `κ` (resp. on top of `#`, with `κ := id`), the
result is correctly decorated iff `y_j` gets decoration `κ ∘ φ_{y_j…y_q}` (by
(0.1)); these decorations depend only on `(y, κ)`.

The pushdown automaton (in the sense of BDPR Def. 1.5, which allows popping and
pushing words; BDPR Remark 1.6 notes that this is equivalent to the usual model) has
states `G ⊔ {q_0,…,q_{|p|-1}} ⊔ {accept}`, start state `e`, start stack symbol `#`,
and transitions, for every letter `g = {(a_i,b_i,h_i)} ∈ A` and every `h ∈ G`:

- **T1.** For every `i`, `c ∈ {0,1}`, `κ ∈ End(G)`: read `g`, pop the word
  `a_i c` in which the `j`-th letter of `a_i` carries the decoration
  `κ ∘ φ_{a_i[j:]}` (`a_i[j:]` = the suffix of `a_i` starting at position `j`) and
  `c` carries `κ`; push `b_i c` with decorations `κ ∘ φ_{b_i[j:]}` on `b_i` and `κ`
  on `c`; and move from state `h` to state `h · κ(h_i)`.
- **T2.** For every word `x` that is a prefix of some `a_i` (so `|x| ≤ L_A`): let
  `m ≥ 0` be minimal such that `x p^m` has a prefix in the domain code of `g`
  (`m ≤ L_A`), and write `x p^m = a_k u`. Read `g`, pop `x̂#`, push `(b_k u)^#`, and
  move from state `h` to state `φ_p^m(h) · φ_u(h_k)`.
- **Verification.** `ε`-transitions: from `h ∈ ker e_p` to `q_0`; from `q_j`, pop
  `(p_{j+1}, κ)` for any `κ` and go to `q_{j+1 mod |p|}`; from `q_0`, pop `#` and go
  to `accept`.

There are finitely many transitions (all words involved have bounded length).

*Invariant.* After reading `w_t = g_1…g_t` along a run without verification moves,
the state is `h_t ∈ G`, the stack is a correctly decorated `x̂_t#`, and
`ξ_p·w_t = [h_t, x_t]_p`. This holds for `t = 0`. Suppose it holds at `t` and the
next letter is `g`. Exactly one of the following holds, since the domain code `A_g`
of `g` is a complete prefix code:
(1) `x_t` has a proper prefix `a_i ∈ A_g`, `x_t = a_i c u'`. The only applicable
transition is T1 with parameters `(i, c, κ = φ_{cu'})`. Indeed, a T1 transition
with parameters `(i', c', κ')` matches iff the top `|a_{i'}|+1` stack symbols are
`a_{i'} c'` with the decorations prescribed from `κ'`. Since the stack is correctly
decorated, this happens iff `a_{i'} c'` is a prefix of `x_t` and `κ'` is the
actual decoration of `c'`. As `A_g` is a prefix code, `a_{i'} = a_i`, so `c' = c`
and `κ' = φ_{cu'}`. No T2 transition matches, because it would pop the whole stack
`x_t#` with `x_t` a prefix of some `a_k ∈ A_g`, and then `a_k` would have the proper
prefix `a_i ∈ A_g`. By (2.1) with `m = 0` and `u = cu'`,
`ξ_p·w_t g = [h_t φ_{cu'}(h_i), b_i c u']_p`, which is the new configuration.
(2) `x_t` has no proper prefix in `A_g`, so it is a prefix of some element of
`A_g`. No T1 transition matches, and the only matching T2 transition is the one for
`x = x_t`; by (2.1) it produces `[φ_p^m(h_t) φ_u(h_k), b_k u]_p = ξ_p·w_t g`.
In both cases the new stack is correctly decorated.

*Acceptance.* Transitions reading letters start only in states from `G`, so an
accepting run reads all of `w = g_1…g_ℓ` first, reaching `(h_ℓ, x̂_ℓ#)` as above,
and then uses only verification moves. These reach `accept` iff `h_ℓ ∈ ker e_p` and
`x_ℓ ∈ p^*`, which by Lemma 2.1(ii) means `ξ_p·w = ξ_p`. So the automaton
recognises `L_p`. ∎

## 7. Proof of (b)

Let `A` be a finite symmetric set of triple lists whose images generate `𝒱`
(Lemma 5.2). The action of `𝒱` on `Ω = ⊔_{p∈P} Ω_p` is faithful because `𝒱` is a
group of permutations of `Ω`. It has finitely many orbits, the `Ω_p` (Lemma 5.1),
and for the point `ξ_p` of each orbit the loop language
`{w ∈ A^* : ξ_p·w = ξ_p}` is `L_p`, which is context-free (Proposition 6.1). By
`faithful-context-free-action-groups-embed-in-v` (BDPR Theorem A, "if" direction),
`𝒱` is isomorphic to a subgroup of `V`. With (c), `T(G_*)` embeds in `V` too. ∎

## 8. Remarks

- Condition (K) is exactly injectivity of the cloning maps in (a), which
  Witzel–Zaremsky require (arXiv:1405.5491, p. 17: "injective maps
  `κ^n_k : G_n → G_{n+1}`").
- Lemma 3.2 is where more than one period is needed. If `φ0 = id` then `id ∈ E(S)`
  already gives `M = {e}`, and `P = {"0"}` suffices, which is BDPR's choice of dyadic
  points `v0^∞`.
- Only the V-type group is used for transitivity. The F-type subgroup `T(G_*)` is
  not transitive on `Ω_p` in general (for `p = "0"` it fixes the `x`-part `0^∞`).
- The statement for all cloning systems on finite groups
  (`cloning-system-groups-on-finite-groups-embed-in-v`) remains open. The argument
  depends on the *local* form of the cloning maps (a clone depends only on the
  cloned coordinate). For non-local systems such as the upper-triangular matrix
  groups of Witzel–Zaremsky, labels are not attached to single leaves, and
  Section 2 has no evident analogue.

## 9. Computational sanity check (not part of the proof)

`experiments/zaremsky-2-16-lehnert-conjecture-2026-09-16/twisted_power_cf_action.py`
(single-threaded, about 5 minutes, output below 1 KB):

- (L) Lemma 3.1 checked exhaustively over all endomorphism pairs satisfying (K) for
  `Z/2, Z/3, Z/4, (Z/2)^2, (Z/2)^3, S_3` (234677 pairs; `M = {e}` in every case).
- For up to 12 sampled pairs per group, with `P` = one shortest word per idempotent
  (breadth-first search over `S`), random lists of F- and V-type: (R) refinement
  invariance of (2.1); (H) `(ξ·g)·k = ξ·(g·k)` and inverses; (F) nontrivial lists
  move some point `[e, a_i u]_p` with `|u| ≤ 6`; (P) a direct simulation of the
  automaton of Section 6 on random words (including words `w w^{-1}`) keeps the
  decoration invariant, tracks the orbit point, and accepts exactly the words fixing
  `ξ_p`.

Output: `ALL CHECKS PASSED`.

## 10. Sources

- S. Witzel, M. C. B. Zaremsky, *Thompson groups for systems of groups, and their
  finiteness properties*, arXiv:1405.5491 (PDF read 2026-09-16): cloning maps
  (p. 17, (2.5) on p. 18), Definition 2.18 (p. 19), triples and expansions (p. 19).
- M. C. B. Zaremsky, *A user's guide to cloning systems*, arXiv:1606.08762 (PDF read
  2026-09-16): Example 3.1 and its variation (pp. 3–4), §5.1 product and Figure 4,
  §5.2–5.3.
- C. Bodart, D. D'Angeli, D. Perego, E. Rodaro, *A graph-theoretical
  characterisation of subgroups of Thompson's group V*, arXiv:2608.02111v1
  (3 Aug 2026; PDF read 2026-09-16): Definitions 1.5–1.8 (pp. 6–7), Theorem A
  (p. 2), Theorem B (p. 2), §3.1 including Proposition 3.1 and Theorem 3.2
  (pp. 17–20), Theorem 2.9 (p. 17).

# sk-wp-embedding: simple Kazhdan LEF envelopes with solvable word problem

Lane `sk-wp-embedding` (SK swarm, wave 6), 2026-09-13. Everything here is UNREVIEWED; review is queued with
`sk-verify-4`.

Target from the brief: a Boone–Higman statement with (T) and LEF, "a f.g. residually finite group has solvable word
problem iff it embeds in an infinite f.g. simple Kazhdan LEF group with solvable word problem".

**What is true.** The iff as stated is false in one direction and open in the other, for two separate reasons found
here:
- the envelope is LEF and not residually finite, so its subgroups need not be residually finite (`[[T]]'` already
  embeds in the note's own `G_X`); the statement has to be read inside the class of f.g. RF groups;
- inside that class the forward direction needs EFFECTIVE residual finiteness, which by Rauzy's theorem
  (`rf-higman-embedding-for-decidable-groups-fails`, on main) does not follow from RF plus solvable word problem.

What is proved below: the degree formula for the envelope over any acting group (§2), computability of the Toeplitz
language (§3), and the embedding theorem for perfect groups (§4), with the general case left open and a route (§5).

## 1. Definitions and the chain lemma

**Definition (Rauzy).** A f.g. group `Γ` with finite generating set `S` is *effectively residually finite* (ERF) if
some algorithm, given a word `w` on `S` with `w ≠ e` in `Γ`, produces a homomorphism from `Γ` to a finite group in
which `w` has nontrivial image. The definition is quoted on main in
`rf-higman-embedding-for-decidable-groups-fails`, imported from Rauzy, arXiv:2002.02540.

**Lemma 1 (effective chain).** Let `Γ` be f.g. and ERF with solvable word problem. Then there is a computable
sequence `Γ = K_0 ⊇ K_1 ⊇ ⋯` of finite-index normal subgroups with `∩_m K_m = {e}` such that
- the relation `w ∈ K_m` (a word `w` on `S`, `m ∈ N`) is decidable, and
- `m ↦ (Γ/K_m, images of S)` is computable as a finite group with a generating tuple.

*Proof.* Enumerate all words `w_1, w_2, …` on `S ∪ S^{-1}` in length-lex order. Given `i`, decide `w_i = e` with the
word problem. If `w_i ≠ e`, run the ERF algorithm on `w_i`; it halts and returns a finite group `F_i` and a tuple
`φ_i(S) ∈ F_i^S` defining `φ_i : Γ → F_i` with `φ_i(w_i) ≠ 1`. Put
`K_m = ∩ { ker φ_i : i ≤ m, w_i ≠ e }`, a finite intersection of finite-index normal subgroups, so normal of finite
index; the sequence is descending, and computable because the finitely many tuples `φ_i(S)` are computed by the
above. If `w ≠ e` then `w = w_i` for some `i`, and `w ∉ ker φ_i ⊇ K_i`, so `∩_m K_m = {e}`. Membership is decidable:
evaluate each `φ_i(w)` by multiplying the images of the letters in the finite group `F_i`, and check `φ_i(w) = 1` for
the finitely many `i ≤ m` with `w_i ≠ e`. The finite quotient `Γ/K_m` is the image of `S` in `∏_{i≤m} F_i`, computed
by closing the generated subgroup, which is finite. ∎

The converse also holds: a computable chain with decidable membership and `∩ K_m = {e}` makes `w ≠ e` semi-decidable
(search for `m` with `w ∉ K_m`) and gives the separating quotient, so `Γ` is ERF; if in addition `Γ` is recursively
presented, the word problem is decidable.

**Sharpness (Rauzy, Theorem 2, on main).** Some f.g. RF group with solvable word problem is not ERF. So Lemma 1
cannot be run from "RF with solvable word problem" alone, and every statement below keeps ERF as a hypothesis.

**Inheritance (Rauzy, Fact 4).** F.g. subgroups of ERF groups are ERF. F.p. RF groups are ERF (Fact 3), and so is
every f.g. linear group over a field with computable arithmetic (congruence quotients).

## 2. The word problem of the envelope over any acting group

Let `Δ` be a f.g. group with finite generating set `S_Δ`, let `X ⊆ A^Δ` be a subshift over a finite alphabet, put
`R = LC(X,F_2) ⋊ Δ` and `G = EL_n(R)` for `n ≥ 3`. Write
`L(X) = { (W,p) : W ⊆ Δ finite, p ∈ A^W occurs in X }`, with the elements of `W` given as words on `S_Δ`. Take as
generators of `G` the matrices `e_ij(u_s^{±1})` for `s ∈ S_Δ` and `e_ij(e_a)` for `a ∈ A`, where
`e_a = e_{\{x : x_e = a\}}`. They generate: the translates `u_δ e_a u_δ^{-1}` are the one-letter cylinder indicators,
products give window-pattern indicators, sums give `LC(X,F_2)`, and the elementary identities give all of `EL_n(R)`.

**Theorem B.** `WP(G) ≡_T WP(Δ) ⊕ L(X)`.

*Proof.* (≤) Multiply the word out formally. Each entry becomes a finite sum `Σ_k f_k u_{δ_k}`, where each `δ_k` is a
word on `S_Δ` and each `f_k` is a Boolean combination of window patterns, both produced by the multiplication rules
`(f u_δ)(f' u_{δ'}) = f·(f'∘δ^{-1})·u_{δδ'}` and `u_δ f u_δ^{-1} = f∘δ^{-1}`; the second relabels a window `W` to
`δW`. With an oracle for `WP(Δ)` we decide equality of the position labels and of the `δ_k`, so we collect terms and
reach a normal form `Σ_δ f_δ u_δ` with distinct `δ`. The `u_δ` are `LC(X,F_2)`-independent in the crossed product, so
the entry vanishes iff every `f_δ` is the zero function on `X`. Each `f_δ` is a function of a finite window `W_δ`,
and it vanishes on `X` iff `f_δ(p) = 0` for every `p` with `(W_δ,p) ∈ L(X)`, which is a finite check with the `L(X)`
oracle. The word is trivial iff its difference from `I_n` has all entries zero.

(≥) `WP(Δ) ≤_m WP(G)`: for words `δ, δ'` on `S_Δ`, the element `e_{12}(u_δ)e_{12}(u_{δ'})^{-1} = e_{12}(u_δ-u_{δ'})`
is trivial iff `u_δ = u_{δ'}` iff `δ = δ'` in `Δ`. `L(X) ≤_m WP(G)`: given `(W,p)` with `W = \{w_1,…,w_r\}`, the
pattern indicator is `e_{[p]} = ∏_{i≤r} u_{w_i} e_{p(w_i)} u_{w_i}^{-1} ∈ LC(X,F_2)`, and a group word for
`e_{12}(e_{[p]})` is computed from `(W,p)` by iterating `e_{12}(rs) = [e_{13}(r), e_{32}(s)]`. It is trivial iff
`e_{[p]} = 0` iff `p` does not occur in `X`. ∎

For `Δ = Z` this is the note's corollary `WP(G_X) ≡_T L(X)`, since `WP(Z)` is decidable. Over other acting groups the
word problem of the acting group appears, and it is the only new contribution.

## 3. The Toeplitz language is computable

Let `Δ` be f.g., infinite and ERF with solvable word problem, and let `(Δ_m)` be an effective chain from Lemma 1.
Let `X_Δ` be the Toeplitz subshift of `rf-toeplitz-subshifts-over-residually-finite-groups` built from that chain:
at each level the single hole coset `C_{m-1}` of `Δ_{m-1}` splits into `Δ_m`-cosets, one of which is the new hole
`C_m`, one is valued `1`, and the rest are valued `0`.

**Theorem C.** `L(X_Δ)` is decidable.

*Proof.* Write `x` for the Toeplitz array; the language of the orbit closure is the set of patterns occurring in `x`,
because the orbit of `x` is dense and a pattern is a clopen condition.

*Values.* For `γ ∈ Δ` given as a word, search `m = 1,2,…` for the first level with `γ ∉ C_m`; it halts because
`∩_m C_m = ∅`. Membership in `C_m` is decidable, since `C_m` is one coset of `Δ_m` whose representative the
construction computes level by level from the finite quotients. At that level `x(γ)` is `1` if `γ` lies in the
designated `1`-coset of level `m` and `0` otherwise, both decidable.

*Occurrence.* Let `W = \{w_1,…,w_r\}` be a finite window and `p ∈ A^W`. Search for `M` with `w_iw_j^{-1} ∉ Δ_M` for
all `i ≠ j`; it halts because `∩_m Δ_m = \{e\}` and membership is decidable. Then the elements of `W` lie in distinct
`Δ_M`-cosets, so for any `γ` at most one `w ∈ W` has `γw ∈ C_M`. For each of the finitely many cosets `γΔ_M`,
computed from the finite quotient `Δ/Δ_M`:
- for every `w` with `γw ∉ C_M`, the value `x(γw)` is determined by the coset `γΔ_M` and is computed as above;
- the at most one `w` with `γw ∈ C_M` is unconstrained: the hole coset `C_M` splits at level `M+1` into a hole, a
  `1`-coset and at least one `0`-coset, so replacing `γ` by `γδ` with `δ ∈ Δ_M` moves that single position into a
  `1`-coset or into a `0`-coset while fixing the values at the other positions, which depend only on `γΔ_M`.

So `p` occurs iff for some coset representative `γ` the pattern `p` agrees with the computed values at the determined
positions. That is a finite decidable check. ∎

## 4. Embedding theorem

**Theorem A.** Let `Γ` be f.g. and infinite, and suppose `Γ ≤ [Δ,Δ]` for some f.g. infinite `Δ` that is ERF with
solvable word problem. Then `Γ` embeds in an infinite, f.g., simple group with property (T) that is LEF and has
solvable word problem.

*Proof.* Let `X_Δ` be the Toeplitz subshift of §3 for an effective chain of `Δ`, and
`G = EL_3(LC(X_Δ,F_2) ⋊ Δ)`. By `residually-finite-group-toeplitz-elementary-groups-lef-kazhdan` (reviewed) `G` is
infinite, f.g., simple, Kazhdan and LEF, with trivial centre over `F_2`. By
`rf-groups-embed-in-simple-kazhdan-lef-groups` (reviewed) the map `γ ↦ diag(u_γ,1,1)` is an injective homomorphism
of `[Δ,Δ]`, hence of `Γ`, into `G`; it uses Whitehead's lemma and `diag([a,b],1,1) ∈ E_3`. By Theorem B,
`WP(G) ≡_T WP(Δ) ⊕ L(X_Δ)`, and both are decidable, by hypothesis and by Theorem C. ∎

**Corollary A1 (perfect case).** Every f.g. infinite perfect ERF group with solvable word problem embeds in an
infinite f.g. simple Kazhdan LEF group with solvable word problem. Take `Δ = Γ`.

**Corollary A2.** `SL_n(Z)` for `n ≥ 3`, and every f.p. perfect RF group, embeds in such a group: f.p. plus RF gives
ERF and solvable word problem (Rauzy, Facts 3 and 1, or Mostowski).

**Theorem D (converse).** If a f.g. group `Γ` embeds in a f.g. group `G` with solvable word problem, then `WP(Γ)` is
solvable, and `Γ` is LEF whenever `G` is. *Proof.* Fix words in the generators of `G` representing the images of a
finite generating set of `Γ`; a word on `Γ`'s generators maps to a computable word on `G`'s generators, and it is
trivial in `Γ` iff its image is trivial in `G`. LEF passes to subgroups. ∎

So the class of f.g. groups embedding in an infinite f.g. simple Kazhdan LEF group with solvable word problem sits
between the f.g. infinite perfect ERF groups with solvable word problem and the f.g. LEF groups with solvable word
problem. It is not contained in the RF groups: `[[T]]'` of a computable minimal subshift embeds in the note's own
`G_X` (`topological-full-group-embeds-in-subshift-elementary-group`), is LEF and is not RF.

## 5. What is open, and the route

**Open.** Does every f.g. ERF group with solvable word problem embed in an infinite f.g. simple Kazhdan LEF group
with solvable word problem? Only perfectness is missing. The overgroup of
`rf-groups-lie-in-derived-subgroups-of-rf-groups` is `Δ = ⟨ρ(S), a_s, b_s⟩ ≤ ∏_n Alt(Ω_n)`, where the commutator
witnesses `a_s, b_s` are chosen in each coordinate separately by Ore's theorem. Each coordinate of a word in these
generators is computable, so `WP(Δ)` is co-r.e.; nothing makes it r.e., because the coordinates are chosen with no
coherence. The abelianization obstruction is real and rules out the cheap fixes: for `W = Γ ≀ F` with `F` finite,
`W^{ab} = Γ^{ab}`, and an injective homomorphism `g ↦ (g, α(g))` into a wreath product lands in `[W,W]` only if the
homomorphism `α` induces `-id` on `Γ^{ab}`, which a general `Γ` does not admit. In particular `g ↦ (g,g^{-1},1)` is
not a homomorphism, the same failure as `diag(a,a^{-1},1)`.

**Route (untried).** Choose the Ore witnesses coherently along the chain. The quotients `Δ/Δ_{m+1} → Δ/Δ_m` make
`Ω_{m+1} → Ω_m` fiber-preserving, and `λ_{m+1}(s)` covers `λ_m(s)`. Inside the fiber-preserving subgroup
`Sym(F) ≀ Alt(Ω_m)` the projection is a homomorphism, so the question is whether a commutator decomposition lifts
along it with prescribed images, adjusting arbitrary lifts by kernel elements. Coherent witnesses would make `Δ` an
inverse limit of computable finite data, with decidable word problem, and would give the general theorem.

**Contrast.** Rauzy's Theorem 1 says some f.g. RF group with solvable word problem embeds in no f.p. RF group; the
Boone–Higman theorem embeds groups with solvable word problem in simple subgroups of f.p. groups. Our envelopes are
never f.p., since an infinite simple LEF group is not f.p. (Vershik–Gordon), so this is a different landscape, and
the hypothesis that replaces "solvable word problem" is effective residual finiteness.

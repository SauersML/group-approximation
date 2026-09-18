---
rg: 2
id: leavitt-pairs-embed-sl-n-q-in-steinberg-groups
kind: claim
title: In any ring containing Q and a binary Leavitt pair, SL_N(Q) embeds in the Steinberg group of rank 6N+1
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that is the vanishing of STABLE K-theory of Leavitt tensors; this kills the image of the unstable K_2(N,Q) at the explicit rank 6N+1, which stable vanishing does not give.
  q-coefficient-leavitt-tensor-unit-groups-are-fp: that asks for finite presentation of the whole unit group under K_1 = K_2 = 0; this puts SL_N(Q) inside a Steinberg group with no K-theory hypothesis on the ring.
  fp-central-simple-q-ring-with-trivial-leavitt-k-theory: that asks for a ring with vanishing K_1 and K_2 of its Leavitt tensor; this needs no K-theory at all, only a Leavitt pair and Q.
  sl-n-q-is-colimit-of-lattice-stabilizers: that presents SL_n(Q) as a colimit of lattice stabilizers; this realizes SL_N(Q) inside St_(6N+1) of a ring.
  leavitt-unit-groups-over-every-field-are-simple-mod-scalars: that is about unit groups of L_k(1,2); this is about Steinberg groups of any ring containing a Leavitt pair and Q.
---

**ESTABLISHED (2026-09-17)** through `leavitt-pairs-embed-sl-n-q-in-steinberg-groups-proof`.
The proof (lane `gq-steinberg-q`) is Attempt 1 below. Three independent referee reports
PASS it:
- `research/artifacts/gq-referee-a-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md`
  (proof gaps);
- `research/artifacts/gq-referee-b-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md`
  (citations and hypotheses);
- `research/artifacts/gq-referee-c-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md`
  (re-derivation).

**Priority and credit** (`research/artifacts/gq-gq-lit-arxiv-priority.md` §7). No source
kills the unstable image of `K_2(N,Q)` at an explicit finite rank for an arbitrary
`S ⊇ Q`. Related work:
- stable vanishing: Ara–Brustenga–Cortiñas, arXiv:0903.0056;
- the doubling trick is the usual K-triviality argument for properly infinite rings;
- Khanh, arXiv:2609.08428v1, Thm 5.4: `St_r(L_(F_2)(1,2)) -> GL_r` is an isomorphism for
  `r >= 3`. His Lemma 5.2 is the room lemma (a) below.
What is new here is the explicit rank bound for every ring containing `Q` and a Leavitt
pair.

**Statement.** Let `S` be a unital ring with a unital subring `Q ⊆ S` and elements
`x_1, x_2, y_1, y_2` with `y_i x_j = δ_ij` and `x_1 y_1 + x_2 y_2 = 1`. Let `N >= 3`
and let `τ : [N] -> [6N+1]` be `i -> N+i`. Then the composite

    St_N(Q) --index shift τ--> St_(6N+1)(Q) --> St_(6N+1)(S)

has kernel exactly `K_2(N,Q) = ker(St_N(Q) -> SL_N(Q))`. So `SL_N(Q)` embeds in
`St_(6N+1)(S)`, and `GL_n(Q)` embeds in `St_(6n+7)(S)` for every `n >= 2`, through
`g -> diag(g, det(g)^(-1))`.

Examples of `S`: `L_Q(1,2)`; `B ⊗_Z L_Z(1,2)` for any ring `B ⊇ Q`; the finitely
presented ring `R_L` of `leavitt-resolvent-ring-is-fp-simple-of-char-zero`, whose
generators `s_i, t_i` are a Leavitt pair.

**Why it matters.** Over `Q` the Steinberg relations present `St_N(Q)`, a central
extension of `SL_N(Q)` by Tate's infinitely generated `K_2(Q)`, not `SL_N(Q)`
(`research/artifacts/gq-gq-k2-q-uniformity.md` §3). The claim says one Leavitt pair kills
every Tate symbol at a fixed finite rank. For a finitely presented `S`, `St_m(S)` is
finitely presented for `m >= 4` (`steinberg-finite-presentation-and-kazhdan-theorem`), so
no `K_2` hypothesis on `S` is needed to get a finitely presented overgroup of `GL_n(Q)`.

## Attempts

1. **Proof claimed (lane `gq-steinberg-q`, 2026-09-17), not independently reviewed.**
   It uses only the Steinberg relations, Whitehead's lemma and linear algebra over `Q`.
   Notation: `St_k(S)` has generators `x_ij(r)` (`i ≠ j` in `[k]`) and relations (R1)
   `x_ij(r)x_ij(r') = x_ij(r+r')`, (R2) `[x_ij(r), x_jl(r')] = x_il(rr')` for distinct
   `i,j,l`, (R3) `[x_ij(r), x_kl(r')] = 1` for `j ≠ k`, `i ≠ l`. `π_k : St_k(S) -> E_k(S)`,
   `K_2(k,S) = ker π_k`. An injection `α : [k] -> [k']` induces `ŝ_α : St_k -> St_k'`,
   `x_ij(r) -> x_α(i)α(j)(r)`, since (R1)–(R3) only see equalities of indices; `ŝ` is the
   initial inclusion. `ι` is induced by `Q ⊆ S`. `Q` is central in `S`: the inverse of a
   central unit is central.

   **(a) Room lemma.** If `k < k'` and `z ∈ K_2(k,S)`, then `ŝ(z)` is central in
   `St_k'(S)`. Fix `b ∈ [k'] \ [k]`. The elements `x_cb(r)`, `c ∈ [k]`, commute, and by
   (R2), (R3) conjugation by `ŝ(x_ij(s))` sends `∏_c x_cb(v_c)` to `∏_c x_cb(w_c)` with
   `w = e_ij(s) v`. So conjugation by `ŝ(y)` acts on this column group through `π_k(y)`, and
   likewise on the row group `x_bc(r)` through `π_k(y)^(-1)`. Hence `ŝ(z)` commutes with
   every `x_cb(r)`, `x_bc(r)`, and with `x_bb'(r)` for `b, b' ∉ [k]` by (R3). Finally
   `x_cd(r) = [x_cb(r), x_bd(1)]` for `c, d ∈ [k]`.

   **(b) The doubling map.** `ψ : S -> M_2(S)`, `ψ(r) = (y_s r x_t)_(s,t)`, is a unital ring
   homomorphism: `Σ_t y_s r x_t y_t r' x_u = y_s r r' x_u` and `y_s x_t = δ_st`. Block
   expansion `β : St_N(M_2(S)) -> St_2N(S)`, `x_ij(a) -> ∏_(s,t) x_(i,s),(j,t)(a_st)`, is a
   homomorphism. Its factors commute by (R3), which gives (R1) and (R3). For (R2),
   commutators of factors are `x_(i,s),(l,u)(a_st b_tu)` and commute with all factors, so
   `[∏X, ∏Y] = ∏[X,Y]`. Here `[2N] = [N] × {1,2}` with `(i,1) = i`, `(i,2) = N+i`.
   Put `Φ = β ∘ St_N(ψ) : St_N(S) -> St_2N(S)`. Define `𝒴 ∈ M_(2N×N)(S)` by
   `𝒴_((i,s),j) = δ_ij y_s` and `𝒳 ∈ M_(N×2N)(S)` by `𝒳_(i,(j,t)) = δ_ij x_t`. Then
   `𝒳𝒴 = I_N`, `𝒴𝒳 = I_2N` and `π_2N(Φ(y)) = 𝒴 π_N(y) 𝒳`. For `q ∈ Q`, `ψ(q) = q I_2`,
   so `Φ(ι x_ij(q)) = x_ij(q) x_(N+i),(N+j)(q)`. The two factors commute by (R3), so
   `Φ(ι y) = ι(ŝ(y) ŝ_τ(y))` for all `y ∈ St_N(Q)`, with `τ : i -> N+i`.

   **(c) A square swap.** `W = [[𝒴, 0], [0, 𝒳]] ∈ M_3N(S)` (row blocks `2N, N`, column
   blocks `N, 2N`) has inverse `[[𝒳, 0], [0, 𝒴]]`. For `A ∈ GL_N(S)`,
   `W diag(A, I_2N) W^(-1) = diag(𝒴 A 𝒳, 𝒳𝒴) = diag(𝒴 A 𝒳, I_N)`. By Whitehead's lemma,
   `D = diag(W, W^(-1))` lies in `E_6N(S)`:
   `[[W,0],[0,W^-1]] = u(W) l(-W^-1) u(W) · u(-I) l(I) u(-I)`, with `u(B) = [[I,B],[0,I]]`
   and `l(B) = [[I,0],[B,I]]`. So `D diag(A, I_5N) D^(-1) = diag(𝒴 A 𝒳, I_4N)`.

   **(d) Two lifts agree.** Put `M = 6N` and `m' = M+1`. Choose `ω ∈ St_M(S)` with
   `π_M(ω) = D`. Define `f_1, f_2 : St_N(S) -> St_m'(S)` by
   `f_1(y) = ŝ(ω) ŝ(y) ŝ(ω)^(-1)` and `f_2(y) = ŝ(Φ(y))`. Then
   `c(y) = f_1(y) f_2(y)^(-1) = ŝ(e(y))` with `e(y) = ω ŝ(y) ω^(-1) ŝ(Φ(y))^(-1) ∈ St_M(S)`.
   By (b) and (c), `π_M(e(y)) = I`, so `c(y)` is central by (a), with `M < m'`. Hence
   `c(yy') = f_1(y) c(y') f_2(y)^(-1) = c(y') c(y)`: `c` is a homomorphism to an abelian
   group. `St_N(S)` is perfect, since `x_ij(r) = [x_ik(r), x_kj(1)]` with `k ∉ {i,j}`.
   So `c = 1` and `f_1 = f_2`.

   **(e) The swindle.** Let `z ∈ K_2(N,Q)`. Then `ιz ∈ K_2(N,S)`, so `ŝ(ιz)` is central in
   `St_m'(S)` by (a) and `f_1(ιz) = ŝ(ιz)`. By (b),
   `f_2(ιz) = ŝ(ι(ŝ(z) ŝ_τ(z))) = ŝ(ιz) · ŝ_τ(ιz)`. By (d), `ŝ_τ(ιz) = 1` in `St_m'(S)`.

   **(f) Conclusion.** The composite in the statement is `y -> ŝ_τ(ιy)`. Its kernel contains
   `K_2(N,Q)` by (e). It is contained in `K_2(N,Q)`: `π_m'(ŝ_τ(ιy))` is `π_N(y)` placed in
   rows and columns `N+1, …, 2N`, and `SL_N(Q) -> GL_m'(S)` is injective because
   `Q -> S` is. Over the field `Q`, `E_N(Q) = SL_N(Q)` by row reduction. So the image is
   `St_N(Q)/K_2(N,Q) ≅ SL_N(Q)`. For `GL_n(Q)`, apply this with `N = n+1`.

   *Where it could fail (for the referees):* the block-expansion homomorphism (b), the
   room lemma (a) for noncommutative `S`, and the use of central `q` in (b).

2. **Optional sharpening (cited, not needed).** If for a field `F` and `m >= 3` the maps
   `ŝ_α : K_2(3,F) -> K_2(m,F)` are onto for every index embedding `α` (Steinberg,
   *Lectures on Chevalley groups*, §§6–7; Matsumoto 1969; not re-read at source), then (e)
   with `N = 3` gives `K_2(m,Q) -> K_2(m,S)` zero for every `m >= 19`. Then
   `SL_m(Q) ≤ St_m(S)` for all `m >= 19`.

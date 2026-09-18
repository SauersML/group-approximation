# Referee report (gq-referee-c): leavitt-pairs-embed-sl-n-q-in-steinberg-groups

- **Node:** `research/leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md`, landed b9dd69f0a by lane `gq-steinberg-q`.
- **Lens:** independent re-derivation of every step, plus calibration.
- **Verdict: PASS.** Steps (a)–(f) of Attempt 1 are correct as written, for noncommutative `S`, and I found no gap.
  The embedding `SL_N(Q) ≤ St_(6N+1)(S)` and `GL_n(Q) ≤ St_(6n+7)(S)` hold.

## 1. Statement checked

`S` is unital, with `Q ⊆ S` a unital subring and `x_1, x_2, y_1, y_2 ∈ S` such that `y_i x_j = δ_ij` and
`x_1 y_1 + x_2 y_2 = 1`. For `N >= 3` and `τ(i) = N + i`, the map `y ↦ ŝ_τ(ι y)`,
`St_N(Q) -> St_(6N+1)(S)`, has kernel exactly `K_2(N,Q)`.

`Q` is central in `S`: integers are central, and the inverse of a central unit is central. This is the only
place (b) needs `q ∈ Q` rather than a general `r ∈ S`.

## 2. Step-by-step re-derivation

**(a) Room lemma.** Let `k < k'`, `b ∈ [k'] \ [k]`, and `C_b = {∏_c x_cb(v_c)}`.
- The factors commute: `c ≠ c'` falls under (R3), and `c = c'` is (R1). So `v ↦ ∏_c x_cb(v_c)` is an isomorphism
  `S^k -> C_b`.
- Conjugation by `x_ij(s)` with `i, j ∈ [k]`:
  - It fixes `x_cb(v)` for `c ≠ j`, by (R3) (`j ≠ c`, and `i ≠ b` since `b ∉ [k]`).
  - It sends `x_jb(v)` to `[x_ij(s), x_jb(v)] x_jb(v) = x_ib(s v) x_jb(v)`, by (R2).
  - So it acts on `C_b` as `v ↦ (I + s e_ij) v`.
- Hence conjugation by `ŝ(y)` acts through `π_k(y)`.
- On rows, `x_ij(s) x_bi(v) x_ij(s)^(-1) = x_bi(v) x_bj(-v s)`, so conjugation acts as `v ↦ v π_k(y)^(-1)`.
- For `z ∈ K_2(k,S)` both actions are trivial. `x_bb'(r)` with `b, b' ∉ [k]` commutes with `ŝ(St_k)` by (R3), and
  `x_cd(r) = [x_cb(r), x_bd(1)]` covers the rest.
- So `ŝ(z)` is central. The argument needs only one spare index and uses no commutativity of `S`. ✓

**(b) Doubling.** `ψ(r)_(st) = y_s r x_t` is a unital ring homomorphism `S -> M_2(S)`: the sum over `t` of
`x_t y_t` is 1, and `y_s x_t = δ_st`.

`β` is a homomorphism from `St_N(M_2(S))`: check (R1)–(R3) on the images.
- The four factors of `β(x_ij(a))` commute pairwise by (R3), since `i ≠ j`. That gives (R1). (R3) is immediate,
  because the row and column blocks are disjoint.
- For (R2), `[X_st, Y_t'u]` equals `x_(i,s),(l,u)(a_st b_tu)` when `t = t'` and is 1 otherwise, by (R3), since
  `(j,t) ≠ (j,t')` and `i ≠ l`.
- Every such commutator commutes with all the `X`'s and `Y`'s, by (R3). So `[∏X, ∏Y] = ∏[X,Y]`, which is
  `∏_(s,u) x_(i,s),(l,u)(Σ_t a_st b_tu) = β(x_il(ab))`. The order `a_st b_tu` is kept, so noncommutative `S` is
  fine. ✓
- `𝒳𝒴 = I_N` uses `Σ_t x_t y_t = 1`, and `𝒴𝒳 = I_2N` uses `y_s x_t = δ_st`.
- `π_2N ∘ Φ` and `y ↦ 𝒴 π_N(y) 𝒳` are homomorphisms that agree on the generators. For the second, the entries of
  `𝒴 (r e_ij) 𝒳` sit in block `(i,j)` with `i ≠ j`, so the elementary factors multiply to `I` plus their sum. ✓
- For `q ∈ Q`, `ψ(q) = q I_2`. So `Φ(ι x_ij(q)) = x_ij(q) x_(N+i),(N+j)(q)`, and the two factors commute.
  `ŝ(St_N)` and `ŝ_τ(St_N)` commute elementwise, so `y ↦ ŝ(y) ŝ_τ(y)` is a homomorphism, and it equals `Φ ∘ ι` on
  `St_N(Q)`. ✓

**(c) Square swap.**
- `W = [[𝒴,0],[0,𝒳]]` has inverse `[[𝒳,0],[0,𝒴]]`: both products are `diag(I_2N, I_N)` and `diag(I_N, I_2N)`.
- `W diag(A, I_2N) W^(-1) = diag(𝒴A𝒳, 𝒳𝒴) = diag(𝒴A𝒳, I_N)`.
- The Whitehead identity: `u(W) l(-W^(-1)) u(W) = [[0,W],[-W^(-1),0]]` and `u(-I) l(I) u(-I) = [[0,-I],[I,0]]`.
  Their product is `diag(W, W^(-1))`. The block unipotents are products of commuting elementary matrices, so
  `D ∈ E_6N(S)`. ✓
- The index conventions agree: `[2N] = [N] × {1,2}` is the same in (b) and in the first `2N` coordinates of (c).

**(d) The two lifts agree.**
- `e(y) = ω ŝ(y) ω^(-1) ŝ(Φ(y))^(-1)` has `π_6N(e(y)) = D diag(A, I_5N) D^(-1) diag(𝒴A𝒳, I_4N)^(-1) = I`, where
  `A = π_N(y) ∈ E_N(S) ⊆ GL_N(S)`.
- So `c(y) = ŝ(e(y))` is central in `St_(6N+1)` by (a), with `k = 6N < k' = 6N+1`. This is where the "+1" is used.
- `c(yy') = f_1(y) c(y') f_2(y)^(-1) = c(y') c(y)`, so `c` is a homomorphism to an abelian group.
- `St_N(S)` is perfect for `N >= 3`. So `c = 1`. ✓

**(e) Swindle.** For `z ∈ K_2(N,Q)`:
- `ŝ(ιz)` is central by (a), so `f_1(ιz) = ŝ(ιz)`.
- `f_2(ιz) = ŝ(ι ŝ(z)) · ŝ(ι ŝ_τ(z)) = ŝ(ιz) · ŝ_τ(ιz)`.
- So `ŝ_τ(ιz) = 1`. ✓

**(f) Kernel.** `π_(6N+1)(ŝ_τ(ιy))` is `π_N(y)` in rows and columns `N+1..2N`, and `M_N(Q) -> M_N(S)` is injective.
So the kernel is exactly `K_2(N,Q)`, and the image is `St_N(Q)/K_2(N,Q) ≅ E_N(Q) = SL_N(Q)`. For `GL_n(Q)`, use
`g ↦ diag(g, det g^(-1))` into `SL_(n+1)(Q)` with `N = n+1 >= 3`, which gives rank `6n+7`. ✓

## 3. Calibration: why this does not contradict `K_2(Q) ≠ 0`

- **The mechanism is ψ_* = id and ψ ∘ ι = ι ⊕ ι, so ι_* = 2ι_*.** The claim is the unstable, explicit form of
  "`K_2(Q) -> K_2(S)` is zero". `ψ : S ≅ M_2(S)` is the Morita equivalence given by the Leavitt pair, so it acts
  as the identity on K-theory. But on `Q` it is the block sum `ι ⊕ ι`. So `ι_* = 2ι_*` and `ι_* = 0`.
  - (d) is "ψ_* = id" at finite rank: conjugation by a lift `ω` of `D` realizes `Φ` on `St_N(S)`, and `f_1 = f_2`.
  - (b)'s formula `Φ ∘ ι = ŝ · ŝ_τ` is "ψ ∘ ι = ι ⊕ ι".
  - `K_2(Q)` itself stays nonzero. Its image dies in `St(S)`, never in `St(Q)`.
- **Where `S^N ≅ S^(2N)` is used.** Exactly once, in (c): `𝒳𝒴 = I_N` and `𝒴𝒳 = I_2N` make `W` invertible. This is
  a module isomorphism `S^N ≅ S^(2N)` whose entries are `x_t, y_t ∉ Q`. Over `S = Q` there is no such `W`: the
  lift `ω` does not exist, (d) has no `f_1`, and `K_2(N,Q)` survives in `St(Q)`, as it must.
- **Consistency with known K-theory.** For `S = L_Q(1,2)`, Ara–Brustenga–Cortiñas give an exact sequence
  `K_i(Q) --(1-2)--> K_i(Q) -> K_i(L)`. Here `1 - 2 = -1` is an isomorphism, so `K_*(L_Q(1,2)) = 0`, which agrees
  with the claim. The same count at `K_1` predicts that `diag(q, 1)` becomes elementary in `GL(S)`. That is
  consistent with `K_1(L_Q(1,2)) = 0`.
- **O1 (no residually finite overgroup).** `St_(6N+1)(S)` is not residually finite whenever it contains
  `SL_N(Q)`. No contradiction arises: nothing in the proof passes through a residually finite group.
- **Distortion and FW.** These are not relevant to an embedding statement. The route's (T) claim for
  `St_(6n+7)(R_L)` is consistent with containing `SL_3(Z)`.

## 4. Scope notes for the route `gl-n-q-explicit-via-steinberg-group-of-resolvent-ring`

These are not defects of the reviewed node.

- **Finite presentation.** The Problem 2.7 route also needs `steinberg-finite-presentation-and-kazhdan-theorem`
  (for `R` finitely presented and `n >= 4`, `St_n(R)` is finitely presented). I did not re-derive it here, and
  the embedding does not use it. That node should get its own referee pass before anyone calls Problem 2.7
  answered.
- **Simplicity of R_L.** The route also needs `leavitt-resolvent-ring-is-fp-simple-of-char-zero`. For the
  embedding alone, the route only needs `R_L` to be a finitely presented ring that contains `Q` unitally and a
  Leavitt pair. Simplicity is not used. The unital `Q ⊆ R_L` holds by the model and the `1/m` formula (see my
  report `gq-referee-c-leavitt-resolvent-ring-is-fp-simple-of-char-zero.md`).
- **Priority.** Mikaelian (arXiv:2507.04347v8, §1.4) announces an explicit embedding of `GL(n,Q)` into a
  finitely presented `Γ_n` produced by his Higman-embedding algorithm (Kourovka 14.10(c)). A comparison of
  "natural" belongs in the route node. The present claim is a different construction.

# Referee report (gq-referee-c): one-steinberg-group-contains-every-gl-n-q

- **Node:** `research/one-steinberg-group-contains-every-gl-n-q.md` and the route
  `gl-n-q-explicit-via-st-4-of-divisible-ring`, landed 27d360184 by lane `gq-deep-free-1`.
- **Lens:** independent re-derivation plus calibration.
- **Verdict: PASS, conditional on four classical inputs.** Every step (a)–(e) re-derives correctly from the
  inputs listed in §2. The one citation that carries the proof is C1, the centrality of `K_2(4, M_k(Q))`.
  Referee B must confirm it at the primary source before this node is flipped. For step (b) I give a variant
  (§3) that needs only centrality, not Matsumoto's generation by symbols.

## 1. Setup checked

- `Q` is central in `S`.
- **Cuntz families of every size from the Leavitt pair:** `t_k = x_2^(k-1) x_1` (`k < m`) and `t_m = x_2^(m-1)`.
  - `t_j^* t_k = δ_jk`, using `y_1 x_2 = 0 = y_2 x_1`, which hold in any ring with a Leavitt pair.
  - `Σ t_k t_k^* = 1` by telescoping `x_2^(k-1)(1 - x_2y_2)y_2^(k-1)`.
- `e_ij = t_i t_j^*` are matrix units commuting with `Q`. So `ι_m : M_m(Q) -> S` is a unital ring map, and it is
  injective (`t_k^* ι_m(a) t_l = a_kl`).
- For `S = D`: `Q ⊆ Z(D)`, and `w, v, sw, vt` form a Leavitt pair (my report
  `gq-referee-c-finitely-presented-divisible-ring-engine.md`, PASS).

## 2. Step-by-step

**(a) The block map β_k : St_4(M_k(Q)) -> St_4k(Q).**
- It is a homomorphism. This is the argument of `leavitt-pairs-embed-sl-n-q-in-steinberg-groups` (b), which I
  verified in `gq-referee-c-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md` §2.
- It is surjective: generators within one block are commutators of generators in off-diagonal blocks.
- It is an isomorphism for `k >= 2`, given:
  - **C1:** `K_2(4, M_k(Q))` is central in `St_4(M_k(Q))`. This is the centrality theorem for
    `n >= sr(A) + 2`, with `sr(M_k(Q)) = 1`. Cited through Voronetsky, arXiv:2004.08551, introduction; the
    primary source is van der Kallen. I did not re-read it.
  - **C2:** `St_n(F)` is centrally closed for `n >= 5` (Kervaire 1970; Steinberg). So `St_4k(Q)` is the universal
    central extension of `SL_4k(Q)` for `4k >= 8`.
- With these, `μ` exists. `β_k μ = id` by universality, and `μ β_k = id` because an endomorphism of a perfect
  central extension that lies over the identity is the identity. ✓

**(b) Scalar blocks.**
- `β_(mN) ∘ St_4(j_N) = b_N ∘ β_m`: both send `x_ij(a)` to `∏_(s,t,c) x_((i,s,c),(j,t,c))(a_st)`. ✓
- `b_N` is `β'` (block expansion) composed with `q ↦ q I_N`, so it is a homomorphism.
- `b_N = ∏_c ŝ_c` on all of `St_4m(Q)`, since the `ŝ_c` have disjoint indices and commuting images. ✓
- `ŝ_c(y) = ŝ_1(y)` for `y ∈ K_2(4m,Q)`. The node derives this from Matsumoto's symbols. The variant in §3 derives
  it from centrality alone. ✓

**(c) Torsion.**
- **C3:** `K_2(n,F) ≅ K_2(F)` for a field and `n >= 3` (Matsumoto).
- **C4:** `K_2(Q) = Z/2 ⊕ ⊕_(p odd) F_p^x` is torsion (Tate; Milnor, *Introduction to algebraic K-theory*, §11).

So every element of `K_2(4m,Q)` has finite order. ✓

**(d) Killing x.**
- `t'_(i,c) = t_i u_c` is a Cuntz family: `(u_c^* t_i^*)(t_j u_d) = δ_ij δ_cd`, and `Σ t_i u_c u_c^* t_i^* = 1`.
- So `ι_(mN)(a ⊗ I_N) = ι_m(a)` and `ι_m = ι_(mN) ∘ j_N`.
- `β_(mN)(St_4(j_N)(x)) = ŝ_1(β_m(x))^N = 1`, and `β_(mN)` is injective by (a). The case `mN = 1` is trivial.
- So `St_4(ι_m)(x) = 1`. ✓

**(e) Kernel.**
- `ker ⊇ K_2(4, M_m(Q))` by (d).
- `ker ⊆ K_2(4, M_m(Q))` because `E_4(ι_m)` is injective.
- The image is `E_4(M_m(Q)) = SL_4m(Q)`. ✓

## 3. Variant for (b) needing only centrality

- Let `P ∈ SL_(4mN)(Q)` be the permutation matrix swapping the index blocks `c = 1` and `c`. Its sign is
  `(-1)^(4m) = 1`, so `P ∈ E(Q)`. Choose `ω` with `π(ω) = P`.
- Then `f_1(y) = ω ŝ_1(y) ω^(-1)` and `f_2(y) = ŝ_c(y)` have the same image in `SL`. So `f_1 f_2^(-1)` takes
  values in `K_2(4mN, Q)`. That group is central, by the classical centrality of `K_2(n,F)` for a field and
  `n >= 3` (the theorem of C1 with `A = Q` and `n = 4mN`).
- As in `leavitt-pairs-embed-sl-n-q-in-steinberg-groups` (d), `f_1 f_2^(-1)` is a homomorphism to an abelian
  group on the perfect `St_4m(Q)`, so it is trivial.
- Hence `ŝ_c = ω ŝ_1 ω^(-1)`. On the central `ŝ_1(K_2(4m,Q))` this gives `ŝ_c = ŝ_1`.
- This removes the need for symbol generation and index-independence in (b).

## 4. Calibration

- **The mechanism.** On `K_2`, `j_N` is multiplication by `N`, and `ι_m = ι_(mN) ∘ j_N` because `S` absorbs
  `M_N`. So `ι_*(x) = ι_*(N x)`. Since `K_2(Q)` is torsion, some `N` kills `x`. No contradiction with
  `K_2(Q) ≠ 0` arises: the classes die only in `St_4(S)`.
- **Leavitt pair used exactly where needed.** The proof needs Cuntz families of *every* size `N`, and a binary
  pair supplies them.
  - Compare `S = L_Q(1,3)`, which has Cuntz families only of odd size.
  - By Ara–Brustenga–Cortiñas, `K_2(Q) --(1-3)--> K_2(Q) -> K_2(L_Q(1,3))`. So `K_2(L_Q(1,3))` contains
    `K_2(Q)/2`, which contains the class of `{-1,-1}`.
  - The proof correctly fails there: `{-1,-1}` has order 2 and needs `N` even.
- **The torsion of K_2(Q) is used.** Over a field with non-torsion `K_2`, step (c) fails, and this proof does
  not apply. The citation-free swindle of `leavitt-pairs-embed-sl-n-q-in-steinberg-groups` still works over any
  such field, at growing rank. The two proofs are consistent.
- **O1.** `St_4(S)` is not residually finite, since it contains `(Q,+)`. That is consistent.
- **(T).** The route cites property (T) for `St_4(D)`. That is consistent with containing `SL_3(Z)`.

## 5. What the route to Problem 2.7 still needs

- **`steinberg-finite-presentation-and-kazhdan-theorem`** (for finitely presented `R` and `n >= 4`, `St_n(R)` is
  finitely presented). It is not reviewed by me. It is needed for "one finitely presented group" and should
  get its own referee pass.
- **C1 at source.** Load-bearing. Without C1, (a) and hence (d) fail.
- **Priority.** Mikaelian (arXiv:2507.04347v8, §1.4) announces an explicit finitely presented `Γ_n ⊇ GL(n,Q)`,
  built with his algorithm. The single group `St_4(D)` for all `n` is a different, algebraic construction.

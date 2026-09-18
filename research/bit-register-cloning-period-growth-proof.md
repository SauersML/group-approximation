---
rg: 2
id: bit-register-cloning-period-growth-proof
kind: route
title: "Configuration action of the bit-register cloning group, gate placement by F, and a reversible counter of order lcm(1..2^s-1)"
target: bit-register-cloning-group-has-doubly-exponential-period-growth
requires: []
artifacts:
  - experiments/cloning-period-growth-2026-09-17/check_cloning_axioms.py
  - experiments/cloning-period-growth-2026-09-17/phi_and_counter_circuit.py
  - experiments/cloning-period-growth-2026-09-17/output.txt
---

Direct proof. The only imports are the definitions of a cloning system and of `T(G_*)`, quoted verbatim below. Numerical
cross-checks are in `experiments/cloning-period-growth-2026-09-17/`: axioms for `n ≤ 3`, invariance of `φ`, the placement
maps, and the full circuit through the group action for `s = 2..5`.

## 0. Imports (verbatim)

M. C. B. Zaremsky, *A user's guide to cloning systems*, arXiv:1606.08762 (PDF read 2026-09-17). The rigorous
construction is Witzel–Zaremsky arXiv:1405.5491 [WZ17], which the guide cites.

- Axioms, §2.4: "In the axioms, we always have 1 ≤ k < ℓ ≤ n and g, h ∈ Gn.
  (C1): (Cloning a product) (gh)κn_k = (g)κn_ρn(h)k (h)κn_k.
  (C2): (Product of clonings) κn_ℓ ◦ κn+1_k = κn_k ◦ κn+1_ℓ+1.
  (C3): (Compatibility) ρn+1((g)κn_k)(i) = (ρn(g))ςn_k(i) for all i ≠ k, k + 1."
  Maps are written on the right ("notation like (g)κn_k is our convention"). So (C2) says
  `((g)κ^n_ℓ)κ^(n+1)_k = ((g)κ^n_k)κ^(n+1)_(ℓ+1)`.
- Directed system, §2.1: the `ι_(m,n)` are injective, `ι_(n,n) = id`, and they compose.
- Representation maps, §2.2: "ρn((g)ιm,n) = (ρm(g))ιm,n (1)".
- Cloning maps, §2.3: "ιm,n ◦ κn_k = κm_k ◦ ιm+1,n+1 (2) for all 1 ≤ k ≤ m ≤ n".
- Definition 2.1: "If the quadruple ... satisfies (C1), (C2) and (C3) then we call it a cloning system."
- Elements and expansions, §5.1: "An element of the Thompson-like group T(G∗) is represented by a triple (T−, g, T+).
  Here T− and T+ are trees ... with the same number of leaves, say n, and g ∈ Gn. ... The equivalence relation is the
  symmetric transitive hull of moves called expansions. An expansion of (T−, g, T+) is a triple (U−, h, U+), where U+ is
  the tree obtained from T+ by adding a caret to the kth leaf of T+, for some 1 ≤ k ≤ n, U− is the tree obtained by adding
  a caret to the (ρn(g)k)th leaf of T−, and h = (g)κn_k."
- Product, §5.1: "Find a common expansion S of T+ and U−, for instance their union, and then perform expansions on the two
  triples to get [T−, g, T+] = [T′−, g′, S] and [U−, h, U+] = [S, h′, U′+] ... then the product is defined by
  [T−, g, T+][U−, h, U+] := [T′−, g′h′, U′+]. This turns out to be a well defined group operation."
- Basic properties, §5.2: "for n ∈ N and T any tree with n leaves, the map g ↦ [T, g, T] is a monomorphism Gn ֒→ T(G∗)
  [WZ17, Observation 3.1]. Also, any T(G∗) also contains Thompson's group F in a natural way, namely as the subgroup of
  elements of the form [T−, 1, T+]."

Trees are finite rooted binary trees. We identify a tree with its dyadic subdivision of `[0,1]`: leaf `i`, counted left
to right, is a standard dyadic interval `[a_i, b_i]`, and adding a caret to a leaf halves it.

## 1. The bit-register cloning system

- `G_n = Sym({0,1}^n)`, with `(gh)(x) = g(h(x))`.
- `(σ)ι_(m,n)(x_1..x_n) = (σ(x_1..x_m), x_(m+1)..x_n)`.
- `ρ_n ≡ 1`.
- For `1 ≤ k ≤ n`, write `δ_k(x_1..x_(n+1)) = (x_1..x_k, x_(k+2)..x_(n+1))`, which deletes coordinate `k+1`. Then
  `(σ)κ^n_k (x) = y`, where `y_(k+1) = x_(k+1)` and `δ_k(y) = σ(δ_k(x))`.

**Axioms.**

- Each `κ^n_k` is an injective homomorphism `G_n → G_(n+1)`. This gives (C1), since `ρ` is trivial.
- (C3) holds because both sides are the identity permutation of `i`. Note `ς^n_k(id) = id`: cloning the identity
  permutation gives the identity.
- (1) is trivial.
- For (2), take `σ ∈ G_m` and `k ≤ m`.
  - `(σ)ι_(m,n)κ^n_k` acts by `σ` on the coordinates `{1..m+1} \ {k+1}`, in order, and trivially elsewhere.
  - `(σ)κ^m_k ι_(m+1,n+1)` does the same.
- For (C2), take `k < ℓ`.
  - `(σ)κ^n_ℓ` fixes coordinate `ℓ+1`, and `σ` acts on the remaining coordinates in order.
  - Applying `κ^(n+1)_k` inserts a new fixed coordinate at `k+1 ≤ ℓ`. The old fixed coordinate moves to `ℓ+2`.
    So the result acts by `σ` on `{1..n+2} \ {k+1, ℓ+2}`, in order.
  - `(σ)κ^n_k` fixes coordinate `k+1`. Applying `κ^(n+1)_(ℓ+1)` inserts a fixed coordinate at `ℓ+2 > k+1`, so this
    result acts the same way.

So this is a cloning system on finite groups. The index pattern is exactly the one satisfied by the guide's Example 3.1
(direct powers, `(g1..gn)κ_k = (g1..gk, gk, ..., gn)`), and `check_cloning_axioms.py` confirms this reading of (C2).
Let `T = T(G_*)`.

**Expansions and products, pure case.**

- An expansion of `(T_-, σ, T_+)` at leaf `k` adds a caret to leaf `k` of both trees and replaces `σ` by `(σ)κ_k`.
- Hence `[T, 1, T]` is the identity of `T`, since `(1)κ_k = 1` and it acts as an identity under the product rule.
- If `U` expands `T`, then `[T, σ, T] = [U, σ', U]` for some `σ'`.
- `[U, g, U][U, h, U] = [U, gh, U]`.

## 2. A configuration action φ

- Let `D_0 = Z[1/2] ∩ [0,1)`. Let `Ω = {0,1}^(D_0)` be the set of all configurations `c: D_0 → {0,1}`.
- For a triple `x = (T_-, σ, T_+)` with `n` leaves:
  - let `f_x: [0,1] → [0,1]` be the PL homeomorphism sending leaf `i` of `T_+` affinely onto leaf `i` of `T_-`;
  - let `A(T) = {a_1 < … < a_n}` be the set of left endpoints of the leaves of `T`.
- `f_x` has dyadic breakpoints and slopes that are powers of 2, and it fixes `0` and `1`. So it bijects `D_0` and maps
  `A(T_+)` onto `A(T_-)` in order.
- Define `φ(x): Ω → Ω` by `c ↦ c'`, where:
  - `c'(f_x(p)) = c(p)` for `p ∈ D_0 \ A(T_+)`;
  - `(c'(a^-_1), …, c'(a^-_n)) = σ(c(a^+_1), …, c(a^+_n))`, where `a^±_i` are the left endpoints for `T_±`.
- `φ(x)` is a bijection, with inverse `φ(T_+, σ^(-1), T_-)`.

**(a) Invariance under expansion.**
- Expand at leaf `k`. The map `f` does not change: it is affine on the halves.
- `A(T_+)` gains the midpoint `m` of leaf `k`, at position `k+1`. `A(T_-)` gains `f(m)`.
- The new group element `(σ)κ_k` acts by `σ` on the other `n` positions and copies position `k+1`. So
  `c'(f(m)) = c(m)`, which is what the old rule gives, since `m ∉ A(T_+)`.
- All other values agree.
- Hence `φ` is constant on equivalence classes and defines `φ: T → Sym(Ω)`.

**(b) Multiplicativity.**
- Take `x = (T, g', S)` and `y = (S, h', U)`, so that `f_x f_y` sends leaves of `U` to leaves of `T`.
- For `p ∉ A(U)`: `f_y(p) ∉ A(S)`, so `φ(x)φ(y)c` takes the value `c(p)` at `f_x f_y(p)`.
- On `A(T)`, the values are `g'(h'(c|_(A(U))))`.
- This is `φ(T, g'h', U)`. By the product rule, `φ` is a homomorphism.

**(c) Consequences.**
- For `x ∈ T` and `k ≥ 1`, `x^k = 1` implies `φ(x)^k = id`. So `ord(x) ≥ ord(φ(x))`.
- For `f = [T_-, 1, T_+] ∈ F`, `φ(f)` is relabelling: `c ↦ c ∘ f^(-1)`.

## 3. The subgroup Γ and gate placement

Put `p_t = 1 − 2^(−t)` for `t ≥ 0`.

**Generators in F.**
- `A = [T_-, 1, T_+]`, where `T_+` has leaves `[0,1/4], [1/4,1/2], [1/2,1]` and `T_-` has leaves `[0,1/2], [1/2,3/4],
  [3/4,1]`.
  - On `[1/2,1]`, `A(t) = 3/4 + (t − 1/2)/2`. So `A(p_i) = p_(i+1)` for `i ≥ 1`.
  - `A^(-1)` maps `[0, p_j]` into `[0, p_(j−1)]` for `j ≥ 2`, and maps `[0, 1/2]` into `[0, 1/4]`.
- `B_1 = [T'_-, 1, T'_+]`, where `T'_+` has leaves `[0,1/2], [1/2,5/8], [5/8,3/4], [3/4,1]` and `T'_-` has leaves
  `[0,1/2], [1/2,3/4], [3/4,7/8], [7/8,1]`.
  - `B_1` is the identity on `[0,1/2]`. On `[1/2,1]` it is `u A u^(-1)` with `u(t) = (1+t)/2`.
  - Since `u(p_j) = p_(j+1)`, `B_1` fixes `p_0, p_1` and sends `p_i ↦ p_(i+1)` for `i ≥ 2`.
- `B_m := A^(m−1) B_1 A^(−(m−1))`.
  - It fixes `p_0, …, p_m`: `A^(−(m−1))` sends them into `[0, 1/2]`, where `B_1` is the identity.
  - It sends `p_i ↦ p_(i+1)` for `i > m`, since `A^(−(m−1))(p_i) = p_(i−m+1)` with `i − m + 1 ≥ 2`.
  - `B_m^r = A^(m−1) B_1^r A^(−(m−1))` has word length `2(m−1) + r`.

**Placement maps.** For `1 ≤ i < j < k`, put

`f_(ijk) = B_j^(k−j−1) B_i^(j−i−1) A^(i−1)` (as maps, the rightmost factor acts first; empty powers are omitted).

- `A^(i−1)` sends `(p_1, p_2, p_3)` to `(p_i, p_(i+1), p_(i+2))`.
- `B_i^(j−i−1)` fixes `p_i` and sends the other two points to `(p_j, p_(j+1))`.
- `B_j^(k−j−1)` fixes `p_i, p_j` and sends `p_(j+1)` to `p_k`.

So `f_(ijk)(p_1, p_2, p_3) = (p_i, p_j, p_k)`. Its word length in `{A^(±1), B_1^(±1)}` is at most
`(j+k−3) + (i+j−3) + (i−1) ≤ 5k`.

**Gates.**
- `T_4` is the tree with leaves `[0,1/2], [1/2,3/4], [3/4,7/8], [7/8,1]`, so `A(T_4) = {p_0, p_1, p_2, p_3}`.
- For `g ∈ Sym({0,1}^3)`, put `G_g = [T_4, 1 ⊗ g, T_4]`, where `1 ⊗ g ∈ G_4` fixes bit 1 and applies `g` to bits 2, 3, 4.
- By §2, `φ(G_g)` applies `g` to `(c(p_1), c(p_2), c(p_3))` and fixes all other values.

**Γ.** Let `Γ = ⟨S⟩` with `S = {A^(±1), B_1^(±1)} ∪ {G_g : g ∈ Sym({0,1}^3)}`. This `S` is finite and symmetric.

**Conjugation.** For `f ∈ F`, `φ(f G_g f^(-1))` applies `g` to `(c(f(p_1)), c(f(p_2)), c(f(p_3)))` and fixes all other
values. Indeed, pull back by `f`, apply `g` at `p_1, p_2, p_3`, and push forward.

So for any three distinct wires `q_1, q_2, q_3 ∈ {1, …, w}` and any 3-bit permutation `g` applied to
`(c(p_(q_1)), c(p_(q_2)), c(p_(q_3)))`:
- sort the wires as `i < j < k`;
- choose `g' ∈ Sym({0,1}^3)` to be `g` with its inputs reordered;
- take `f_(ijk) G_(g') f_(ijk)^(-1) ∈ Γ`.

This has word length at most `10w + 1` in `S`, and its image under `φ` is exactly that gate.

**Torsion.**
- Expand `f = [T_-, 1, T_+]` and `G_(g')` over a common expansion `U` of `T_+` and `T_4`. This gives
  `f G_(g') f^(-1) = [T''_-, h, T''_-]`.
- So a product of finitely many such conjugates lies in `{[V, h, V] : h ∈ G_N}` for a common expansion `V` of all the
  trees `T''_-`.
- That set is the image of the finite group `G_N` under the monomorphism of Observation 3.1. Hence every such product
  has finite order.

## 4. The counter circuit

Fix `s ≥ 2` and `w = 3s` wires (wire `t` is the bit `c(p_t)`):
- the register `a_1..a_s` (wires `1..s`);
- the counter `v_1..v_s` (wires `s+1..2s`, with `v_1` the least significant bit);
- ladder ancillas `z_1..z_(s−2)`;
- two flags `f1, f2`.

A *gate* is a 3-bit permutation on three distinct wires. NOT and CNOT are padded with idle wires.

**MCX.** Let `MCX(c_1^(e_1), …, c_k^(e_k); t)` flip `t` iff `c_i = e_i` for all `i`.
- `k = 0, 1, 2`: one gate (NOT, CNOT, Toffoli with polarities).
- `k ≥ 3`: compute `z_1 ^= [c_1 = e_1][c_2 = e_2]` and `z_i ^= z_(i−1)[c_(i+1) = e_(i+1)]` for `i = 2..k−2`. Then
  apply `t ^= z_(k−2)[c_k = e_k]` and undo the first `k−2` gates in reverse order.
- The ancillas end at 0 if they start at 0.
- Gate count `≤ max(1, 2k−3)`.

**Increment `Inc`.** For `j = s, s−1, …, 1`, apply `MCX(v_1^1, …, v_(j−1)^1; v_j)`.
- Higher bits are processed first, so each `v_j` flips iff all lower bits of the input are 1. This is `v ↦ v+1 mod 2^s`.
- Gate count `≤ Σ_(j=1)^s max(1, 2j−5) ≤ s^2`.

**Swap `T_a`.** This swaps the counter values `a` and `1^s` and fixes the others.
1. `EQ_a(f1)`: CNOT `a_i` into `v_i` for all `i`, then `MCX(v_1^0, …, v_s^0; f1)`, then undo the CNOTs. This flips `f1`
   iff `v = a`. Gate count `≤ 4s`.
2. `EQ_1(f2) = MCX(v_1^1, …, v_s^1; f2)`. Gate count `≤ 2s`.
3. For `i = 1..s`, apply `v_i ^= [f1 = 1][a_i = 0]`. Then for `i = 1..s`, apply `v_i ^= [f2 = 1][a_i = 0]`. Gate count
   `2s`.
4. `EQ_1(f1)`, then `EQ_a(f2)`. Gate count `≤ 6s`.

Why `T_a` is correct, with ancillas and flags starting at 0:
- After steps 1–2, `f1 = [v = a]` and `f2 = [v = 1^s]`.
- Step 3 sets `v := 1^s` if `f1 = 1`, and `v := a` if `f2 = 1`. Flipping `v_i` exactly where `a_i = 0` turns `a` into
  `1^s`, and `1^s` into `a`.
  - If `a ≠ 1^s`, at most one flag is set. The flags are not changed during step 3. So exactly the intended block acts:
    - `f1 = 1` gives `v: a ↦ 1^s`, and the `f2` block is idle;
    - `f2 = 1` gives `v: 1^s ↦ a`, and the `f1` block was idle.
  - If `a = 1^s`, step 3 does nothing, which is correct.
- With `v_new = T_a(v_old)`, we have `[v_old = a] = [v_new = 1^s]` and `[v_old = 1^s] = [v_new = a]`. So step 4 returns
  both flags to 0.
- `T_a` uses at most `14s` gates.

**The circuit `C_s = Inc ∘ T_a`.** It has `N_s ≤ s^2 + 14s ≤ 8s^2` gates. On inputs with ancillas and flags at 0, it
maps `(a, v, 0) ↦ (a, P_a(v), 0)` with `P_a = Inc ∘ T_a`.

**Cycles of `P_a`.** For `0 ≤ a ≤ 2^s − 2`, write the counter values as integers.
- `0 → 1 → … → a → Inc(1^s) = 0` is a cycle of length `a + 1`.
- `a+1 → … → 2^s − 1 → Inc(a) = a + 1` is a cycle of length `2^s − 1 − a`.

So `ord(C_s restricted to the ancilla-zero inputs)` is divisible by `lcm(1, …, 2^s − 1)`.

## 5. The elements w_s

Let the gates of `C_s`, in the order applied, be `γ_1, …, γ_N`. Let `h_t ∈ Γ` be the conjugate from §3 with
`φ(h_t) = γ_t` (acting on `c(p_1), …, c(p_w)`, and fixing all other values). Put

`w_s = h_N h_(N−1) ⋯ h_1 ∈ Γ`.

**Order.**
- `φ` is a homomorphism, so `φ(w_s)` applies `C_s` to the bits `c(p_1..p_w)` and fixes the rest.
- Restricted to configurations whose ancilla and flag bits are 0, it has order divisible by `lcm(1..2^s−1)`.
- `w_s` has finite order by §3 (Torsion), and `ord(w_s) ≥ ord(φ(w_s))` by §2(c).
- So `ord(w_s) ≥ lcm(1, …, 2^s − 1)`.

**Length.**
`‖w_s‖_S ≤ N_s (10w + 1) ≤ 8s^2 · 31s = 248 s^3`.

**Lcm bound (Nair).** For `1 ≤ m ≤ n`, put `I = ∫_0^1 x^(m−1)(1−x)^(n−m) dx`.
- By the Beta integral, `I = 1/(m·C(n,m))`.
- Expanding `(1−x)^(n−m)`, `I = Σ_(i=0)^(n−m) (−1)^i C(n−m, i)/(m+i)`. So `lcm(1..n)·I ∈ Z`, and hence
  `m·C(n,m)` divides `lcm(1..n)`.
- With `n = 2m`: `C(2m,m)` is the largest of the `2m+1` binomial coefficients, which sum to `4^m`. So
  `lcm(1..2m) ≥ m·4^m/(2m+1) ≥ 4^m/3`.
- Take `2m = 2^s − 2`, so `m ≥ 1` for `s ≥ 2`. Then `lcm(1..2^s−1) ≥ 2^(2^s−2)/3`.

**Conclusion.** For `s ≥ 2`, `w_s ∈ Γ` has finite order, `‖w_s‖_S ≤ 248 s^3`, and
`ord(w_s) ≥ lcm(1..2^s−1) ≥ 2^(2^s−2)/3`.

**Check.** `phi_and_counter_circuit.py` builds `C_s` for `s = 2..5`. It places every gate by evaluating the actual PL
words `f_(ijk)`, confirms `(a, v, 0) ↦ (a, P_a(v), 0)`, and computes the order and word length. Output is in
`experiments/cloning-period-growth-2026-09-17/output.txt`.

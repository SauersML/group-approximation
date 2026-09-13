# The regular HNN intertwiner cocycle on Thompson's V, and the Toeplitz commutator

Lane `w7-hnn-cocycle`, 2026-09-12. Every decision here is **OPEN**; re-derivation requested from `w3-vf-linear`.

Sources (live tip):
- `research/artifacts/char-three-level-factoring-and-hnn-models-2026-09-12.md`, Sections 2–3 (Theorem 2.1, Theorem 2.3,
  Corollary 2.4, Remark 2.5, Section 3).
- `research/artifacts/v-rank-extension-to-ternary-leavitt-units-2026-09-12.md` (w6-v-extend, Proposition 5.2).

The target is `v-detecting-rank-functions-extend-to-ternary-leavitt-units`. The equivalence used is the corrected
one: target ⟺ (link 1 ⟺ V gate), equivalently target ⟺ (link 1 ⟹ V gate), since V gate ⟹ link 1 is known.
- **V gate:** `thompson-v-ternary-rank-functions-are-augmentation`.
- **Link 1:** `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`.

Peer lanes are cited, not duplicated:
- The set `{T(0,1), T(1,0), T(1,00), T(00,1)}` belongs to `w7-escape-set`.
- `w7-v-cycle-c3` landed `2e8bf4f44`.
- `w7-yh-rank-firewall` and `w7-gl3-f3-states` had no landing visible at the time of writing.

## 0. Setting

Notation:
- `R = L_(F_3)(1,2)` and `G_3 = R^x`, with `z = −1`.
- `L = ∪_j L_j` with `L_j = GL_(2^j)(F_3)`, the level units (the degree-zero units).
- `σ_reg = lim_ω σ_j`, where `σ_j` is left multiplication on `V_j = F_3[L_j] ε_−`, and `M` is the rank ultraproduct.
- For `g ∈ G_3`: `B_g = {a ∈ L : g a g^(−1) ∈ L}` and `φ_g(a) = g a g^(−1)`.
- Theorem 2.3 gives `X_g ∈ M^x` with `X_g σ_reg(a) X_g^(−1) = σ_reg(φ_g(a))` for every `a ∈ B_g`.
- **Candidate (b)** is `σ_reg` together with these intertwiners, for `g ∈ V`.

## 1. The domains for elements of V

**Lemma 1.1.** Let `v ∈ V` act by prefix replacements `β_i γ -> α_i γ`. Put `δ_v = |α_i| − |β_i|` on `β_i` (a locally
constant function), and `Ω_k = {δ_v = k}`.
1. `B_v` is the group of level units that are block diagonal for the partition `{Ω_k}`: no matrix entry joins two
   cylinders with different `δ_v`.
2. `φ_v` carries level units of `Ω_k` at depth `d` to level units of `v(Ω_k)` at depth `d + k`.
3. `B_(v^(−1)) = φ_v(B_v)`. The signed diagonal `E` lies in `B_v`, and `φ_v(τ_C) = τ_(v(C))`.

*Proof.*
- Refine to a depth `j` at which `δ_v` is constant on cylinders, and write `a = Σ a_(αβ) s_α t_β` over depth-`j` words.
- Then `v s_α t_β v^(−1) = s_(v(α)) t_(v(β))`, which is homogeneous of degree `δ_v(α) − δ_v(β)`.
- These elements are linearly independent, being the images of matrix units under an automorphism. So `v a v^(−1)`
  has degree zero iff `a_(αβ) = 0` whenever `δ_v(α) != δ_v(β)`.
- A unit of `R` lying in `R_0 = ∪_j M_(2^j)(F_3)` is a unit of `R_0`.
- Item 3: `a ∈ B_v` iff `φ_v(a) ∈ L`, and then `φ_v(a) ∈ B_(v^(−1))`. Diagonal elements have degree zero, and
  `v P_C v^(−1) = P_(v(C))`. QED

**The level part of V.** `V ∩ L = ∪_j Sym({0,1}^j)`, the dyadic permutations. For `k ∈ V ∩ L`, `B_k = L`.

## 2. The cocycle

**Definition 2.1.** For `u, v ∈ V` put `c(u,v) = X_(uv)^(−1) X_u X_v` and `B_(u,v) = {a ∈ B_v : φ_v(a) ∈ B_u}`.
- `c(u,v)` commutes with `σ_reg(B_(u,v))`. For `a ∈ B_(u,v) ⊆ B_(uv)`, both `X_u X_v` and `X_(uv)` conjugate `σ(a)`
  to `σ(φ_(uv)(a))`.
- Put `B_(u,v,w) = {a ∈ B_w : φ_w(a) ∈ B_(u,v)}`.

**Cocycle identity (associativity).** Expanding `X_u X_v X_w` in two ways gives
`c(u, vw) c(v, w) = c(uv, w) · Ad(X_w^(−1))(c(u, v))`.
- Both sides lie in `σ_reg(B_(u,v,w))'`.
- `B_(u,v,w)` lies in `B_(u,vw)`, `B_(v,w)` and `B_(uv,w)`.
- `Ad(X_w^(−1))` maps `σ(B_(u,v))'` into `σ(B_(u,v,w))'`.

**Change of intertwiners.** Every other intertwiner is `Y_v = X_v m_v` with `m_v ∈ σ(B_v)'`, and
`c_Y(u,v) = m_(uv)^(−1) c(u,v) Ad(X_v^(−1))(m_u) m_v`.

The class `[c]` is **trivial** if some choice with `Y_k = σ(k)` for `k ∈ V ∩ L` gives `c_Y = 1`. Then `v -> Y_v` is
a homomorphism `V -> M^x` agreeing with `σ_reg` on `V ∩ L`. Theorem 3.1 uses only the homomorphism property.

**Lemma 2.2 (what triviality means).** Let
`Ĝ_V = (L ∗_(V∩L) V) / ⟨⟨ v a v^(−1) = φ_v(a) : v ∈ V, a ∈ B_v ⟩⟩`.
1. `[c]` is trivial iff `σ_reg` extends to a homomorphism `Ĝ_V -> M^x`.
2. `G_3` is a quotient of `Ĝ_V`: the relations hold in `G_3`, and `G_3 = ⟨V, x⟩` with `x = 1 + s_00 t_01 ∈ L_2`.
3. A model of `G_3` extending `σ_reg` is a trivialization that also kills `ker(Ĝ_V -> G_3)`. No presentation of that
   kernel is recorded.

*Proof.* A homomorphism on `Ĝ_V` restricting to `σ_reg` on `L` restricts on `V` to intertwiners that form a
homomorphism, with `Y_k = σ(k)`. The converse is the universal property. QED

**Lemma 2.3 (normalization over the level part).** Take `X_k = σ(k)` for `k ∈ V ∩ L`. Choose `X_v` on double-coset
representatives, and set `X_(k v k') = σ(k) X_v σ(k')`.
- This is well defined, and `X_(kw) = σ(k) X_w`, `X_(wk') = X_w σ(k')` for all `w`.
- Hence `c(kv, v') = c(v, v')`, `c(vk, v') = c(v, kv')` and `c(v, v'k') = Ad(σ(k')^(−1)) c(v, v')`.
- So `c` is determined by the values `c(u, k v)` with `u, v` representatives and `k ∈ V ∩ L`.

*Proof.*
- **Well defined.** If `k v k' = v`, then `k' ∈ B_v`, since `v k' v^(−1) = k^(−1) ∈ L`. So
  `σ(k) X_v σ(k') = σ(k) σ(k^(−1)) X_v = X_v`.
- **Domain.** `X_(kvk')` intertwines on `B_(kvk') = k'^(−1) B_v k'`.
- The identities follow by substitution. QED

## 3. The barrier: a trivialization decides the V gate

**Theorem 3.1.** Let `ρ_V : V -> M^x` be a homomorphism with each `ρ_V(v)` an intertwiner for `φ_v` on `B_v`. Then
`ρ_V` is injective. Hence:
1. `rk(A) = rank_M(ρ_V(A))` is a Sylvester matrix rank function on `F_3[V]` with `rk(1 − [v]) > 0` for `v != 1`.
   This proves `thompson-v-carries-ternary-nonaugmentation-rank-function` and refutes the V gate.
2. Lifting `ρ_V` stagewise gives `F_3`-linear sofic approximations of `V`. This is the converse of steps 1–2 of
   `non-linear-sofic-via-thompson-v-ternary-augmentation`.

*Proof.*
- `ker ρ_V` is normal in the simple group `V`. Suppose it were all of `V`.
- Take `v` with `v[0] != [0]`. Then `τ_[0] ∈ E ⊆ B_v`, so `σ(τ_(v[0])) = ρ_V(v) σ(τ_[0]) ρ_V(v)^(−1) = σ(τ_[0])`.
  That contradicts injectivity of `σ_reg` on `L` (Theorem 2.1).
- So `ρ_V` is injective, and `rank(ρ_V(v) − 1) > 0` for `v != 1`, because the rank on `M` is faithful.
- Extend linearly and pull back the normalized rank of matrices over `M`. QED

**Corollary 3.2.** The V gate implies `[c]` is nontrivial. Proving `[c]` trivial is at least as hard as refuting the
V gate, which is at least as hard as the soficity problem for `V`. So the coboundary question **cannot be settled by
checking relators by hand**. Any trivialization is itself an `F_3`-linear sofic approximation of `V` compatible with
`σ_reg`.

**Proposition 3.3 (if it also descends to G_3).** Suppose a trivialization kills `ker(Ĝ_V -> G_3)`, giving
`ρ : G_3 -> M^x`. Then:
1. `rk_ρ(1 − [z]) = rank(2) = 1`. So link 1 is false, and the target holds, since its conclusion does.
2. `rk_ρ` restricts on `F_3[L]` to the twisted regular rank function. Consequences:
   - `rk(1 − [τ_C]) = 1/2` for `∅ != C != X` (the parity law).
   - `rk(1 − [k]) = 1 − 1/ord(k)` for level `k ∈ V ∩ L`, by freeness over `⟨k, z⟩ ≅ C_ord(k) × C_2`.
   - The same values hold on every element of `G_3` conjugate into `L`.
3. **Weakly finite.** `M` is von Neumann regular with a faithful rank function, hence stably finite.
   - `ρ(ε_−) = 1`, so `ρ(S_−)` is a nonzero stably finite quotient of `S_− = ε_− F_3[G_3]`.
   - This is the first alternative of Proposition 5.2 of w6-v-extend.
   - It refutes `ternary-anti-central-summand-has-no-weakly-finite-image`, as that node's text says any nontrivial
     characteristic-three rank model does.
4. `ρ` is injective on `G_3`.
   - `ker ρ ∌ z`, and `PG_3` is simple (as consumed in `ternary-leavitt-rank-models-move-z-proof`). So either
     `ker ρ ⊆ ⟨z⟩` or `ker ρ · ⟨z⟩ = G_3`.
   - The second option would give an index-two subgroup, which the perfect group `G_3` does not have.
   - So `G_3` would be `F_3`-linear sofic.

**Remark 3.4 (the no-covariant-model theorem does not touch candidate (b)).**
`thompson-v-cantor-system-has-no-covariant-rank-model` needs a unital ring map on `LC(X, F)`.
- `σ_reg` represents `E` only as a group.
- `P_C^− = (1 − σ(τ_C))/2` is not additive over disjoint `C`: `τ_(C ⊔ D) = τ_C τ_D`, and every `P_C^−` has rank `1/2`.

**Which extensions [c] obstructs.** A nontrivial `[c]` obstructs only extensions whose restriction to `L` is conjugate
to `σ_reg`. Other anti-central models of `L` have different statistics. For example, the natural `F_3^(2^j)` module
gives a depth-`d` transposition rank `2^(−d)`, where `σ_reg` gives `1/2`.

Turning `[c] != 0` into link 1 would need two things:
1. Every anti-central model becomes free on finite subgroups after odd tensor powers. This is the non-projective-part
   gap of Section 3 of the HNN artifact.
2. Free models of `L` are unique up to conjugacy in `M^x`.

Neither is proved.

## 4. Relator checks by hand

**4.1 Level relators.** On `(V ∩ L)^2`, `c = 1` exactly, with `X_k = σ(k)`.

**4.2 Involutions.** If `g^2 = 1`, then `B_g = B_(g^(−1)) = φ_g(B_g)`. `L` is locally finite, so `B_g` is exhausted by
the `g`-invariant finite subgroups `⟨Γ, φ_g(Γ)⟩`. Remark 2.5 gives `X_g^2 = 1`, so `c(g,g) = 1`.

**4.3 Order three, invariant domain.** Take `C : 0 -> 11 -> 10 -> 0`, with `δ_C = (+1, 0, −1)` on `(0, 11, 10)`.
- `C` permutes the three blocks, so `B_C = φ_C(B_C) = B_(C^2)`.
- Remark 2.5 gives `X_C^3 = 1`, and `X_(C^2) := X_C^2 = X_C^(−1)` intertwines on `B_(C^2)`.
- So `c` is trivial on `⟨C⟩`.

**4.4 A square root.** Take `g : 00 -> 100 -> 01 -> 101 -> 00`, fixing `11`, with shifts `(+1, −1, +1, −1)`.
- `g` swaps `Ω_(+1) = [00] ∪ [01]` with `Ω_(−1) = [100] ∪ [101]`, so `B_g` is `g`-invariant.
- `g^2` is level and lies in `B_g`.
- Free transport over `F_3[⟨Γ_i, g⟩] ε_−`, with `Γ_i ∋ g^2, z` finite and `g`-invariant, gives `X_g^2 = σ(g^2)`.
- So `c` is trivial on `⟨g⟩`.

**4.5 First undecided torsion relator (order three, non-invariant domain).**
- **The element.** Use the code `{000, 001, 0100, 0101, 011, 100, 101, 11}` and
  `g : 000 -> 001 -> 0100 -> 000`, `100 -> 101 -> 11 -> 100`, fixing `0101` and `011`.
- **Its blocks.** `Ω_0 = {000, 100, 0101, 011}`, `Ω_(+1) = {001, 11}`, `Ω_(−1) = {0100, 101}`.
- **Non-invariance.** `a = 1 + s_000 t_100 ∈ B_g`, but `φ_g(a) = 1 + s_001 t_101 ∈ L \ B_g`, and
  `φ_g^2(a) = 1 + s_0100 t_11 ∉ L`.
- **What the relator needs.**
  - Every `g`-invariant subgroup of `B_g` lies in the core `B_g ∩ B_(g^2) = B_(g,g)`, which does not contain `a`.
  - `X_(g^2) = X_g^(−1)` intertwines on `B_(g^2) = φ_g(B_g)` automatically.
  - So the relator is exactly: some `m ∈ σ(B_g)'` has `(X_g m)^3 = 1`. Here `c(g,g) = X_g^3 ∈ σ(B_(g,g))'`.
- **The local check passes.** The nilpotent parts `s_000 t_100`, `s_001 t_101`, `s_0100 t_11` have pairwise zero
  products, so `⟨a, g⟩ = (Z/3)^3 ⋊ Z/3` is finite.

**Lemma 4.5.1.** `K = ⟨B_g, g⟩ ⊆ G_3` is not locally finite. So the transport of Remark 2.5 does not apply, even with
finite subgroups of `G_3` in place of finite subgroups of `L`.

*Proof.* `span(K)` contains `A_g = span(B_g)`, the block algebra, and its conjugates by `g` and `g^2`. We have:
- `s_1010 t_0100 ∈ A_g` (block `Ω_(−1)`);
- `s_110 t_000 = φ_g(s_1010 t_0100)`;
- `s_000 t_1010 = φ_g^2(s_001 t_110)`, with `s_001 t_110 ∈ A_g` (block `Ω_(+1)`);
- `s_0100 t_11 = φ_g^2(s_000 t_100)`.

Their product is `s_110 t_000 · s_000 t_1010 · s_1010 t_0100 · s_0100 t_11 = s_110 t_11 = s_11 s_0 t_11 =: T`.
- `T^k = s_11 s_0^k t_11` are nonzero of distinct degrees, so `span(K)` is not locally finite-dimensional.
- If `K` were locally finite, finitely many elements of `span(K)` would lie in the finite-dimensional span of a finite
  subgroup. QED

Stagewise, 4.5 asks for an order-3 letter on a `Z/3`-symmetric triangle of level groups glued along `B`-subgroups,
whose span contains a Toeplitz isometry. **Not decided.**

**4.6 First undecided commutation relator.**
- **The elements.** Let `g = τ_(00,010)` (swap `00γ <-> 010γ`) and `h = τ_(10,110)`. They have disjoint supports,
  so `gh = hg`.
- **Shifts.** `δ_(gh) = +1` on `00` and `10`, and `−1` on `010` and `110`.
- **The gap.** `a = 1 + s_00 t_10 ∈ B_(gh)`, but `a ∉ B_g` (`δ_g(00) = +1`, `δ_g(10) = 0`) and `a ∉ B_h`. So
  `X_g X_h = X_(gh)` must intertwine at an element neither letter constrains.
- **Where it sits.** Letters supported on their cylinders would commute, but `σ_reg` has no such locality (the
  Section 3 gap). **Not decided.**

**4.7 Cannon–Floyd–Parry relators.** (Literature, not re-read locally.)
- The two relators of `F` are commutations of disjointly supported depth-changing elements, the kind in 4.6.
- The torsion relators of `V` involve torsion letters: 4.2–4.4 settle invariant domains, 4.5 is the non-invariant kind.
- No explicit presentation of `V` is recorded on main.

## 5. Task 2: the Toeplitz commutator is a V-conjugate level relation

**Proposition 5.1.** Let `K` be any field and `R = L_K(1,2)`. Identify `M_3(R) = R` through the code
`(c_1, c_2, c_3) = (0, 10, 11)`, so that `E_ij(r) = s_(c_i) r t_(c_j)`. Put
`w = (00 -> 0, 01 -> 101, 10 -> 100, 11 -> 11) ∈ V`. Then:
- `x_12(t0) = 1 + s_0 t_100 = w (1 + s_00 t_10) w^(−1)`;
- `x_23(s0) = 1 + s_100 t_11 = w (1 + s_10 t_11) w^(−1)`;
- `x_13(1) = 1 + s_0 t_11 = w (1 + s_00 t_11) w^(−1)`.

So `[x_12(t0), x_23(s0)] = x_13(1)` is the `w`-conjugate of the Steinberg relation
`[1 + e_(00,10), 1 + e_(10,11)] = 1 + e_(00,11)` in `GL_4(K) = L_2`.
- The three elements generate `w UT_3(F_p) w^(−1)` over the prime field `F_p`.
- For `F_3` this has order 27, and 54 with `z`. For `F_2` it is `D_8`.

*Proof.*
- `t0 t_10 = (s_10 s0)^* = t_100` and `s_10 s0 = s_100`.
- `w s_α t_β w^(−1) = s_(w(α)) t_(w(β))` for domain-code words `α, β`.
- `{0, 100, 101, 11}` is a complete prefix code, so `w ∈ V`. QED

**Consequences.**
1. **No obstruction.** The relation holds in every homomorphism from `G_3`, and by itself it cannot force
   `rk(1 − [z]) = 0`.
   - The finite group `⟨x_12(t0), x_23(s0), z⟩` has anti-central models, for example `σ_reg ∘ Ad(w^(−1))`.
   - The premise "nonsofic subgroup containing `z`" fails for this relation.
2. **Candidate (b) satisfies it** once the three root elements take the coherent values `X_w σ(·) X_w^(−1)`.
   - Such a value intertwines `φ_(wxw^(−1))` only on `{b ∈ B_(w^(−1)) : x (w^(−1) b w) x^(−1) ∈ B_w}`.
   - Recovering the full single-letter domain is the cocycle problem for the triple `(w, x, w^(−1))`, not a new relation.
3. **Char 2.** `natural-compressor-extension-fails-at-toeplitz-commutator` (one transvection) and
   `natural-fock-quantized-compressors-miss-toeplitz-by-a-quarter` (rank `1/4`) constrain models that follow the
   natural level assignment on the finitary compressor system. By Proposition 5.1, the failure belongs to that
   assignment, not to the relation. This is consistent with `toeplitz-coefficient-factoring-kills-leavitt-el3-rank-models`,
   which concerns `x_12(1 − s0 t0)` and coefficient factoring.
4. **Where an obstruction must live.** By the firewall recorded on the target, an obstruction needs a configuration
   generating a nonsofic subgroup with `z`, in particular one not simultaneously conjugate into `L`. The recorded
   candidate is the four-transvection set owned by `w7-escape-set`.

## 6. Status

- **Proved here, held OPEN pending `w3-vf-linear`:**
  - Lemmas 1.1, 2.2 and 2.3.
  - Theorem 3.1, Corollary 3.2 and Proposition 3.3.
  - The checks 4.1–4.4, and Lemma 4.5.1.
  - Proposition 5.1 and its consequences.
- **Refuted:** the premise that the Toeplitz commutator generates a nonsofic subgroup with `z`.
- **Open:**
  - Whether `[c]` is trivial (at least as hard as refuting the V gate).
  - The relators 4.5 and 4.6.
  - The kernel of `Ĝ_V -> G_3`.
  - Whether `[c] != 0` obstructs every extension.
- **Where it stopped:** relator 4.5, the smallest torsion relator of `V` whose group `⟨B_g, g⟩` is not locally finite.
- **Next lead:** decide 4.5, that is, whether some `m ∈ σ(B_g)'` gives `(X_g m)^3 = 1`. Test first whether `⟨B_g, g⟩`
  contains a corner copy of `G_3` (its span already contains `s_11 s_0 t_11`). If it does, 4.5 is as hard as the whole
  problem. If not, look for a rank count on `F_3[Γ]ε_−` over the three pairwise domains.

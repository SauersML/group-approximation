---
rg: 2
id: fpbs-mal-sym-levels-embed-orbits-at-every-depth-proof
kind: route
title: Pulling X_d back along phi splits off one fixed point and leaves X_(d-1) up to the reflection x -> 1-x, and the prefix cosets of t_(j+1) are read off from those of t_j by three extra letters, so an induction on j separates the vertices of C_j by their values on the fixed points
target: fpbs-mal-sym-levels-embed-orbits-at-every-depth
requires: []
artifacts:
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/eb_family.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/family_d4_d10.txt
---

A complete direct proof. Notation is as in the target. For an `L`-set `Y`,
`φ^*Y` is the set `Y` with `y ⋆ w := y·φ(w)`. It is an `L`-set because `φ` is
a homomorphism. Also `(φ^{i+1})^*Y = (φ^i)^*(φ^*Y)`, since
`y·φ^{i+1}(w) = y·φ(φ^i(w))`.

## 1. Lemma R: one pull-back step

**Lemma R.** Let `d ≥ 3`, `p_0 = d − 1` and `S = X_d ∖ {p_0}`. Then `φ(L)`
fixes `p_0` and preserves `S`. The map `ι : S → X_{d−1}`,
`ι(x) = 1 − x mod (d − 1)`, is an isomorphism of `L`-sets from `S ⊆ φ^*X_d`
to `X_{d−1}`. That is, for `x ∈ S` and `w ∈ L`,

```text
ι(x·φ(w))  =  ι(x)·w      (right side computed in X_{d−1}).
```

*Proof.* It suffices to check the generators.
- `φ(a) = a` acts as `α = (0 1)`. It fixes `p_0` because `d ≥ 3`, and it
  preserves `S`.
- `φ(b) = b a b^{-2}` acts by `x ↦ α(x + 1) − 2 mod d`:
  - `x = d − 1`: `0 ↦ 1 ↦ d − 1`. So `p_0` is fixed.
  - `x = 0`: `1 ↦ 0 ↦ d − 2`.
  - `1 ≤ x ≤ d − 2`: `x + 1 ∈ {2, …, d−1}` is fixed by `α`, so `x ↦ x − 1`.

  On `S = {0, …, d−2}` this is `x ↦ x − 1 mod (d − 1)`.
- Put `y = ι(x)`, so `x = 1 − y`. Then:
  - `ι(x·φ(b)) = ι(x − 1) = 2 − x = y + 1 = y·b` in `X_{d−1}`;
  - `ι` swaps `0` and `1` and `α` swaps `0` and `1`. So
    `ι(x·a) = ι(x)·a` in `X_{d−1}` for every `x ∈ S`. ∎

**Corollary R.** For `d ≥ 3`: `φ^*X_d ≅ X_{d−1} ⊔ {p_0}` as `L`-sets, and

```text
T_{j+1}(d)  =  {p_0}  ⊔  ι^{-1} T_j(d−1),       T_j(d) := Fix(L_j, X_d).
```

*Proof.* The first statement is Lemma R. For the second: `x` is fixed by
`L_{j+1} = φ(L_j)` iff `x = p_0`, or `x ∈ S` and `ι(x)` is fixed by `L_j` in
`X_{d−1}`. ∎

## 2. Item 1: the orbit structure

Iterate Corollary R. For `j ≤ d − 2`, every intermediate degree
`d, d − 1, …, d − j + 1` is at least 3. So

```text
(φ^j)^* X_d  ≅  X_{d−j}  ⊔  (j fixed points).
```

`L` acts on `X_{d−j}` through `(0 1)` and the `(d−j)`-cycle `x ↦ x + 1`.
These generate `Sym(d − j)`, since `d − j ≥ 2`. Now `H_j = π_d(φ^j(L))` is
the image of `L` in `Sym((φ^j)^* X_d)`. So `H_j` fixes the `j` points
`T_j = T_j(d)` and acts as `Sym(d − j)` on the rest. Hence
`|H_j| = (d − j)!`.

## 3. Item 4: the case d = j + 2

Here `|H_j| = 2`. Also `α = π_d(a) ∈ H_j` and `α ≠ id`, so `H_j = <α>`. The
element `τ_j = π_d(t_j)` acts on the two moved points as the image of `b` in
`X_2`, which is the swap `x ↦ x + 1 mod 2`. So `τ_j ≠ id`, hence `τ_j = α`.

On the Cayley level `g·w = g π_d(w)`, the `L_j`-orbit of `g` is `g H_j`.
This is `{g, gα}`, and `a` and `t_j` both act on it by `g ↦ gα`.

## 4. The vertices of C_{j+1} in terms of C_j

Write `φ(b^{-1}) = b b a^{-1} b^{-1}`.

**Reduction of `φ(t_j)`.** Let `t_j = ℓ_1 ⋯ ℓ_n` be reduced. Both `φ(b)` and
`φ(b^{-1})` begin with `b` and end with `b^{-1}`. So in the concatenation
`φ(ℓ_1) ⋯ φ(ℓ_n)` the only cancellations are:
- one pair `b^{-1} b` at each junction `φ(b)φ(b)`, giving
  `b a b^{-1} · a b^{-2}`;
- one pair `b^{-1} b` at each junction `φ(b^{-1})φ(b^{-1})`, giving
  `b b a^{-1} · b a^{-1} b^{-1}`.

The junctions with `a^{±1}` do not cancel, and `b b^{-1}` does not occur in
`t_j`. Each cancellation leaves a reduced junction, so nothing cascades.
Deleting a cancelling pair only removes the prefix between its two letters.
So every prefix of the reduced word `t_{j+1}` is equal in `L` to a prefix
`φ(ℓ_1 ⋯ ℓ_k)·s` of the concatenation, with `s` a proper prefix of
`φ(ℓ_{k+1})` (or `s = ∅`).

**Vertex types.** The vertices of `C_{j+1}` are the cosets `L_{j+1}p`, with
`p` a prefix of `t_{j+1}`. Every prefix of `t_j` lies on the `t_j`-path of
`C_j`. Its `b`-letters traverse `b`-edges `e = (c → c·b)` of `C_j`, forwards
for `b` and backwards for `b^{-1}`. Put

```text
s_1 = b,    s_2 = b a,    s_3 = b a b^{-1}.
```

- If `ℓ_{k+1} = a`, then `s = ∅`.
- If `ℓ_{k+1} = b`, then `s ∈ {∅, s_1, s_2, s_3}`, with `u = ℓ_1 ⋯ ℓ_k` at the
  tail `c` of the edge `c → c·b`.
- If `ℓ_{k+1} = b^{-1}`, put `u' = u b^{-1}`. Then `φ(u) = φ(u') b a b^{-2}`,
  so the prefixes `φ(u)·{b, bb, bba^{-1}}` are
  `φ(u') s_3`, `φ(u') s_2` and `φ(u') s_1`. Here `u'` is at the tail of the
  edge `c' → c'·b` traversed backwards.

`φ(L_j) = L_{j+1}`, so `L_{j+1} φ(g u) s = L_{j+1} φ(u) s` for `g ∈ L_j`.
Hence every vertex of `C_{j+1}` is one of:

```text
(O)    O(c)    = L_{j+1} φ(u_c)          for a vertex c of C_j,
(S_k)  S_k(e)  = L_{j+1} φ(u_c) s_k      for a b-edge e = (c → c·b) of C_j, k = 1, 2, 3.
```

Also

```text
S_3(c → c·b)  =  L_{j+1} φ(u_c) b a b^{-2} · b  =  L_{j+1} φ(u_{c·b}) b.      (4.1)
```

## 5. Item 2: induction on j

Write `ev^d_j(v) = (x·v)_{x ∈ T_j(d)}` for a coset `v = L_j w`. It is
well defined, because `L_j` fixes `T_j(d)` pointwise.

**Statement `(*)_j`.** For every `d ≥ j + 2`, `ev^d_j` is injective on
`V(C_j)`.

**Base `j = 0`.** `C_0` has one vertex.

**Step `j → j + 1`.** Let `d ≥ j + 3`, so `d ≥ 3` and `d − 1 ≥ j + 2`. Then
`(*)_j` holds at `d − 1`. By Corollary R, the coordinates of
`ev^d_{j+1}(v)` are the `p_0`-coordinate and the coordinates
`x ∈ ι^{-1} T_j(d−1)`.

*The `p_0`-coordinate.* `p_0 = d − 1` is fixed by `φ(L)`, so
`p_0·φ(u) = d − 1`. Then:
- `O(c) ↦ d − 1`;
- `S_1(e) ↦ (d−1)·b = 0`;
- `S_2(e) ↦ 0·a = 1`;
- `S_3(e) ↦ 1·b^{-1} = 0`.

These three values `d − 1, 0, 1` are distinct, since `d ≥ 3`.

*The other coordinates.* For `x ∈ S`, Lemma R gives
`x·φ(u) = ι^{-1}(ι(x)·u)`, with `ι(x)·u` computed in `X_{d−1}`. So
`(x·φ(u))_{x ∈ ι^{-1}T_j(d−1)}` determines `ev^{d−1}_j(L_j u)`. By `(*)_j`
at `d − 1`, it therefore determines the vertex `L_j u` of `C_j`.

Now let `v ≠ v'` be vertices of `C_{j+1}` with `ev^d_{j+1}(v) = ev^d_{j+1}(v')`.
Their `p_0`-coordinates agree. So either both are of type (O), or both are
of type `S_2`, or both are of types in `{S_1, S_3}`.

- **(O), (O).** `v = O(c)`, `v' = O(c')`. The other coordinates give
  `c = c'`, so `v = v'`.
- **`S_k`, `S_k`, same `k`.** `v = S_k(c → cb)` and `v' = S_k(c' → c'b)`.
  The coordinates are `x·φ(u_c)·s_k` and `x·φ(u_{c'})·s_k`, and `s_k` is a
  bijection. So `x·φ(u_c) = x·φ(u_{c'})` for all `x ∈ ι^{-1}T_j(d−1)`, hence
  `c = c'`. The `b`-edge out of `c` is unique in the folded graph `C_j`, so
  `v = v'`.
- **`S_1`, `S_3`.** `v = S_1(c → cb) = L_{j+1}φ(u_c) b` and, by (4.1),
  `v' = S_3(c' → c'b) = L_{j+1}φ(u_{c'b}) b`. As above, cancelling `b` gives
  `c = c'·b` in `C_j`. So `L_j u_c = L_j u_{c'b}`, hence
  `L_{j+1}φ(u_c) = L_{j+1}φ(u_{c'b})`, and `v = v'`.

Each case contradicts `v ≠ v'`. This proves `(*)_{j+1}`. ∎

**Cosets.** Let `c ≠ c'` and suppose `H_j π_d(u_c) = H_j π_d(u_{c'})`, say
`π_d(u_c) = h π_d(u_{c'})` with `h ∈ H_j`. Then for `x ∈ T_j`,
`x·u_c = (x·h)·u_{c'} = x·u_{c'}`. This contradicts `(*)_j`. So the right
cosets `H_j π_d(u_c)` are pairwise distinct, which is item 2.

## 6. Item 3: (E) on the Cayley level and on its covers

**Lemma 6.1 (disjoint translates give (E)).** Let `Q` be a finite `L`-set.
Suppose that for every `L_j`-orbit `O` of `Q` the sets `O·u_c`,
`c ∈ V(C_j)`, are pairwise disjoint. Then `Q` satisfies (E) at depth `j`.

*Proof.* Let `Δ` be the unfolded graph whose fold is `Γ_j(Q)`: real vertices
`Q`, an `a`-edge `p → p·a`, and a path labelled `t_j` from `p` to `p·t_j`.
Let `Q ⊗ C_j` have vertices `Q × V(C_j)` and an edge `(q, c) → (q·s, c')`
labelled `s` for each edge `c → c'` labelled `s` of `C_j`. It is folded,
because `C_j` is folded and each `s` acts on `Q` by a bijection.

`C_j` has an `a`-loop at `o`, and `t_j` reads a closed path at `o`. So
`p ↦ (p, o)` extends to a morphism `Δ → Q ⊗ C_j`, which maps the `t_j`-path
from `p` to the path reading `t_j` from `(p, o)`. A morphism into a folded
graph factors through the fold, which gives `κ : Γ_j(Q) → Q ⊗ C_j`. The
first coordinate of `κ(v)` is `ψ(v)`, the point under `v`.

Fix a component `Z` of `Γ_j(Q)` and a real vertex `p` in it. Let `O = p·L_j`
and `K = Stab_{L_j}(p)`.
- The closed paths of `Δ` at `p` read exactly the words of `K`. So
  `π_1(Z, p) = K`.
- The closed paths of `Q ⊗ C_j` at `(p, o)` read the words `w` with
  `L_j w = L_j` and `p·w = p`, which is also `K`.

In a folded graph, `v ↦ K w_v` is injective on vertices, where `w_v` labels
any path from the base to `v` (Stallings). `κ` preserves path labels. So it
is injective on the vertices of `Z`.

Now let `v ≠ v'` in `Z` lie over the same point `q`. Then
`κ(v) = (q, c)` and `κ(v') = (q, c')` with `c ≠ c'`. Project a path from
`(p, o)` to `(q, c)` to `C_j`. Its label `w` reads a path `o → c`, so
`w = g u_c` with `g ∈ L_j`, and `q = (p·g)·u_c ∈ O·u_c`. In the same way
`q ∈ O·u_{c'}`. This contradicts the hypothesis. ∎

**The Cayley level.** Here `O = g H_j` and `O·u_c = g H_j π_d(u_c)`. By
item 2, the right cosets `H_j π_d(u_c)` are pairwise distinct, hence
pairwise disjoint, and so are their left translates by `g`. Lemma 6.1 gives
(E).

**Covers.** Let `f : Q̃ → Q` be `L`-equivariant and onto, where `Q` is the
Cayley level. Let `Õ` be an `L_j`-orbit of `Q̃`, so that `O = f(Õ)` is an
`L_j`-orbit of `Q`. If `q̃ ∈ Õ·u_c ∩ Õ·u_{c'}`, then
`f(q̃) ∈ O·u_c ∩ O·u_{c'}`, so `c = c'`. Lemma 6.1 applies to `Q̃`. This
proves item 3. ∎

## 7. Consequence for overfold seeds

Let `Q̃` cover `B_j`, with `m : Γ_{j+1}(Q̃) → Γ_j(Q̃)` as in
[[fpbs-mal-depth-promotion-equals-overfold-merge-number]]. An overfold seed
`(v, v')` has `ψ(v) = ψ(v')` and `m(v) ≠ m(v')`. The morphism `m` fixes the
real vertices, so it preserves the point under each vertex. So `m(v)` and
`m(v')` are distinct vertices of `Γ_j(Q̃)` over one point. By item 3 they
lie in different components, that is, over different `L_j`-orbits.

## 8. Checks

`eb_family.py d0 d1 J` recomputes `|H_j|`, the type of `τ_j` and (E) at
depth `j`. It uses the coset criterion of item 2 on the vertex words of
`C_j`, computed by folding, independently of the proof above.
`family_d4_d10.txt` (`d = 4, …, 10`, both choices of adjacent
transposition) agrees with items 1, 2 and 4 for every `j ≤ d − 2`. At
`j = d − 1` it shows `τ_j = id` and the coset criterion failing.

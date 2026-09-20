---
rg: 2
id: twisted-brin-thompson-towers-pi-k-hardness-proof
kind: route
title: Existential amplification by boxes on a baker coordinate, universal amplification by a clopen set spanning the boxes, and a reversible 2V circuit at the base
target: twisted-brin-thompson-towers-have-pi-k-complete-word-problems
requires:
  - twisted-brin-thompson-finite-presentation-criterion
  - twisted-btb-clopen-action-is-type-a
  - twisted-brin-thompson-wp-equals-actor-orbit-problem
artifacts:
  - experiments/bh-tower-pi-k-2026-09-17/check_gadgets.py
  - experiments/bh-tower-pi-k-2026-09-17/run-output.txt
---

Notation is the brick calculus of `twisted-btb-clopen-action-is-type-a`.
- `C = {0,1}^N`. A brick of `C^S` is `B(u)` for finitely supported `u : S -> {0,1}^*`.
- `h_u` is prefix insertion, and `(τ_g κ)(s) = κ(g^-1 s)`.
- Branches are `h_v τ_g h_u^-1`.

We use `τ_g τ_g' = τ_(gg')` and the identity (TP1) of
`twisted-brin-thompson-wp-equals-actor-orbit-problem-proof`:
`τ_g h_u = h_(g.u) τ_g`, with `(g.u)(t) = u(g^-1 t)`.

A **coordinate map** on `t ∈ S` is an element of `SV_G` all of whose branches have trivial label
and prefixes supported in `{t}`. Such maps form a copy `V_t` of Thompson's `V` acting on `κ(t)` alone.
- Coordinate maps on distinct coordinates commute.
- By (TP1), `τ_g a τ_g^-1` is the same map moved to coordinate `g t`, for `a ∈ V_t`.

For distinct `r_0, r_1 ∈ S`, the **baker map** `σ = σ_(r_0,r_1)` sends `κ` to `κ'` where:
- `κ'(r_0)` is `κ(r_0)` with its first digit removed;
- `κ'(r_1)` is that digit followed by `κ(r_1)`;
- `κ'(t) = κ(t)` for all other `t`.

It has the two branches `h_(r_1 ↦ a) h_(r_0 ↦ a)^-1` on `B(r_0 ↦ a)`, `a ∈ {0,1}`, so `σ ∈ SV_G`.
`σ^j` moves the first `j` digits of `κ(r_0)` onto `κ(r_1)`, so digit `i` of `κ(r_0)` becomes digit
`i - j`.

**Commutation.** If `k ∈ G` fixes `r_0` and `r_1`, then `τ_k σ = σ τ_k`. Both sides agree:
- at `r_0` and `r_1`, because `k^-1` fixes these coordinates;
- at every other `t`, because `k^-1 t ∉ {r_0, r_1}` and `σ` does not touch such coordinates.

Throughout, "word" means a word over a fixed finite generating set. Any fixed element of a finitely
generated group is a fixed word, so writing `x` for a fixed element costs `O(1)`.

## 0. The tower is finitely presented, simple, and of type (A)

`G_0 = 1` acting on `{1,2}` is of type (A):
- it is faithful;
- `G_0` is finitely presented;
- stabilizers are trivial, hence finitely generated;
- there is one two-element subset.

By `twisted-brin-thompson-finite-presentation-criterion`, `G_1 = SV_(G_0)` is finitely presented, and
simple since the action is faithful. It is `2V` (Belk--Zaremsky: `SV_G` for trivial `G` on `n` points
is `nV`).

Suppose `G_k` acts on `S_k` with type (A). By `twisted-btb-clopen-action-is-type-a`, the group
`G_(k+1) = SV_(G_k)` acts with type (A) on `S_(k+1) = Ω_(k+1)`, and it is finitely presented. It is
simple by the criterion, since `G_k` acts faithfully. Item 3 of that claim, with `k = 1`, makes the
action on `S_(k+1)` transitive (one pattern of Boolean atoms for a single proper nonempty clopen set).

So every `G_k` (`k >= 1`) is finitely presented and simple, and acts faithfully and transitively with
type (A) on `S_k`. This is item 1 of the target.

## 1. Upper bound: `OP(G_k, S_k) ∈ Π_k^p`

For `k >= 1` the action on `S_k` is transitive (§0). Fix a representative `r^(k) ∈ S_k`. Then
`OP(G_k, S_k)` is the word problem of `G_k` together with membership of words in `Stab(r^(k))`.

**Base.** `OP(G_0, S_0)` is trivial, since `G_0 = 1`. It has two orbits, with representatives `1`
and `2`. Symbolic coordinates are then just the two points, and the proof file's setting (finitely
many orbits) covers this case.

**Step.** Assume `OP(G_k, S_k) ∈ Π_k^p` for some `k >= 0`, and let `f` be a word of length `l` over
`G_(k+1)`.

*Word problem.* By (b) of `twisted-brin-thompson-wp-equals-actor-orbit-problem`, "`f ≠ 1`" has a
witness of `O(l)` prefix digits. The witness is checked in polynomial time with `OP(G_k, S_k)` as an
oracle. The proof file (part (b), Cost) makes the oracle queries words of length `O(l)`, and there are
`O(l^2)` of them. Hence the word problem is in `coNP^(OP(G_k,S_k)) ⊆ coNP^(Π_k^p)`.

*Stabilizer.* `f ∉ Stab(r^(k+1))` iff some point of `r = r^(k+1)` is mapped outside `r`, or some
point outside `r` is mapped into `r`. This holds because `f` is a bijection, so `f(r) = r` iff
`f(r) ⊆ r` and `f(r^c) ⊆ r^c`.

The witness is one path of the brick tracking of that proof file, with finitely many extra refining
digits. The extra refinement is needed because `r` is a fixed finite union of bricks. Let:
- `P` be the finite set of coordinates occurring in `r`;
- `q` bound the prefix lengths occurring in `r`.

At the end of the path, with state `(u, γ, v)`, refine further as in the proof file's **Refine**
step until two things hold:
- `|u(t)| >= q` for every `t ∈ P`;
- `|v(t)| >= q` for every `t ∈ P`. For the output side, refine the input at `γ^-1 t`.

This is `O(|P| q)` further digits and `O(|P|^2)` further oracle queries. Each `t ∈ P` is written
symbolically as `e_t r^(k)` (as the point itself when `k = 0`), and the queries locate `t` among the coordinates of `u` and `v`. Now
`B(u)` and `B(v)` each lie inside `r` or inside `r^c`, and which one is read off the prefixes on `P`.
The path witnesses `f ∉ Stab(r)` iff exactly one of `B(u)`, `B(v)` lies in `r`.

This is the content of the iteration clause of `twisted-brin-thompson-wp-equals-actor-orbit-problem`,
written as a witness bound. So stabilizer membership is in `coNP^(OP(G_k,S_k))` as well.

Since `coNP^(Π_k^p) = coNP^(Σ_k^p) = Π_(k+1)^p`, we get `OP(G_(k+1), S_(k+1)) ∈ Π_(k+1)^p`. In
particular the word problem of `G_(k+1)` is in `Π_(k+1)^p`. The class is independent of the finite
generating set, by linear substitution.

The same argument over an arbitrary actor with orbit problem in `Π_j^p` gives: a tower of height `m`
has orbit problem in `Π_(j+m)^p`.

## 2. Lemma A (existential amplification)

**Setting.** A finitely generated `G` acts faithfully on `S`, and `SV_G` is finitely generated.
Fix:
- distinct `r_0, r_1 ∈ S` and `s_0 ∈ S \ {r_0, r_1}`;
- a subgroup `K <= Stab(r_0) ∩ Stab(r_1)` with a fixed finite generating set `X_K`.

For `n >= 1` and words `k_1, ..., k_n, h, p` over `X_K`, put, for `d ∈ {0,1}^n`,

```text
t_d = k_1^(d_1) k_2^(d_2) ... k_n^(d_n),      g_d = p^-1 t_d^-1 h t_d p      (all in K).
```

Let `B_d = {κ : κ(r_0) has prefix d}`. These `2^n` bricks partition `C^S`.

**Lemma A.** A word `w` over `SV_G` can be computed in polynomial time, of length
`O(n^2 + Σ|k_i| + |h| + |p|)`, with the following property. Fix non-commuting `α, β ∈ V_(s_0)`. On
each box `B_d`:
- `w` preserves `B_d`;
- `w` equals `[α, β]` on `B_d` if `g_d s_0 = s_0`;
- `w` is the identity on `B_d` otherwise.

In particular `w ≠ 1` iff `∃d  g_d ∈ Stab(s_0)`.

*Proof.* Let `σ = σ_(r_0,r_1)`.

**The controlled twist `c_k`.** For `k ∈ K`, let `c_k` be `τ_k` on `B(r_0 ↦ 1)` and the identity on
`B(r_0 ↦ 0)`.
- On `B(u)` with `u = (r_0 ↦ 1)`, (TP1) and `k.u = u` give `τ_k = h_u τ_k h_u^-1`. So `c_k ∈ SV_G`.
- `τ_k` preserves `κ(r_0)`, so `k ↦ c_k` is a homomorphism `K -> SV_G`.
- For `x ∈ X_K` the element `c_x` is fixed, so `c_k` is a word of length `O(|k|)`.

**Moving the control digit.** Put `c^(i)_k = σ^-(i-1) c_k σ^(i-1)`, a word of length `O(i + |k|)`.
By the commutation above, `σ^-(i-1) τ_k σ^(i-1) = τ_k`. The set where `c^(i)_k` applies it is
`σ^-(i-1)(B(r_0 ↦ 1))`, the set where digit `i` of `κ(r_0)` is `1`. So `c^(i)_k` is `τ_k` where digit
`i` of `κ(r_0)` is `1`, and the identity elsewhere. It preserves every `B_d`.

**The ladder.** Let `Y = c^(1)_(k_1) c^(2)_(k_2) ... c^(n)_(k_n)`. Every factor preserves `B_d` and
acts there as `τ_(k_i)^(d_i)`. So `Y = τ_(t_d)` on `B_d`, and `|Y| = O(n^2 + Σ|k_i|)`.

**The conjugator.** Let `Z = τ_p^-1 Y^-1 τ_h Y τ_p`. `τ_p` and `τ_h` preserve `κ(r_0)`, because
`p, h ∈ K`. So every factor preserves every `B_d`, and `Z = τ_(g_d)` on `B_d`.

**The test.** Let `w = [Z α Z^-1, β]`. The map `α` preserves every `B_d`, since `s_0 ≠ r_0`. On
`B_d`, then, `Z α Z^-1` agrees with `τ_(g_d) α τ_(g_d)^-1`. By (TP1) that is the coordinate map `α`
moved to coordinate `g_d s_0`, and `g_d s_0 ≠ r_0` because `g_d` fixes `r_0`.
- If `g_d s_0 = s_0`, it is `α` itself, and `w = [α, β]` on `B_d`.
- If `g_d s_0 ≠ s_0`, it acts on a coordinate other than `s_0`. It commutes with `β`, and `w` is the
  identity on `B_d`.

Finally, `[α, β] ≠ 1` in `V_(s_0)`, and it acts on `κ(s_0)` alone. `B_d` puts no condition on
`κ(s_0)`, so its restriction to `B_d` is not the identity. `∎`

*Remark.* The commutator trick for a single `u` is (TBO1). The new ingredient is the ladder, which
evaluates the product `t_d` on all `2^n` boxes at once at polynomial cost. This is what makes the
witness `d` existential.

## 3. The invariant `(E_k)`

A `Π_k` formula `ψ(d_1, ..., d_n)` is a quantified Boolean formula
`∀y_1 ∃y_2 ... Q y_k  φ(d, y_1, ..., y_k)`. Here the `y_j` are blocks of variables, `φ` is a Boolean
circuit, and the `d_i` are free.

**`(E_k)`**, for `k >= 1`, is the following data and map:
- fixed `s, R_0, R_1 ∈ S_k`, pairwise distinct;
- a subgroup `K_k <= Stab(R_0) ∩ Stab(R_1)` of `G_k` with a fixed finite generating set;
- a polynomial-time map from `Π_k` formulas `ψ(d_1, ..., d_n)` to words `k_1, ..., k_n, h, p` over
  that generating set.

The map must satisfy, for every `d ∈ {0,1}^n`,

```text
g_d = p^-1 t_d^-1 h t_d p ∈ Stab_(G_k)(s)     iff     ψ(d) holds,      (E)
```

with `t_d = k_1^(d_1) ... k_n^(d_n)`. The lengths may grow with `k`, but polynomially in `|ψ|` for
each fixed `k`.

## 4. Lemma B (universal amplification): `(E_k)` implies `(E_(k+1))`

Assume `(E_k)`. Apply Lemma A with:
- `G = G_k` and `S = S_k`, so that `SV_G = G_(k+1)`;
- `r_0 = R_0`, `r_1 = R_1`, `s_0 = s` and `K = K_k`.

The finite generation hypotheses hold by §0.

**The formula.** Let `ψ'(d)` be a `Π_(k+1)` formula with `n` free variables. Rewrite it in
polynomial time as `ψ'(d) = ∀e ¬χ(d,e)`. Here `e` is a block of `m` variables, and `χ` is the `Π_k`
formula obtained by pushing the negation through the remaining `k` quantifier blocks.

Apply `(E_k)` to `χ(d,e)`, with `n + m` free variables, and then Lemma A. This gives a word `w` over
`G_(k+1)`. It preserves each brick `B_(de) = {κ : κ(R_0) has prefix de}`, and it acts there as
`[α, β]` if `χ(d,e)` and as the identity otherwise.

**The clopen sets.** Fix a clopen `A ⊆ C` with `[α, β] A ≠ A`. It exists because `[α, β] ≠ 1`. For
`d ∈ {0,1}^n` put

```text
U_d = {κ ∈ C^(S_k) : κ(R_0) has prefix d and κ(s) ∈ A}  ∈ S_(k+1).
```

**Claim 1.** `w(U_d) = U_d` iff `ψ'(d)`.

`U_d` is the disjoint union over `e` of `U_d ∩ B_(de)`, and `w` preserves each `B_(de)`.
- If `¬χ(d,e)`, then `w` fixes `U_d ∩ B_(de)` pointwise.
- If `χ(d,e)`, then `w` maps `U_d ∩ B_(de)` onto `{κ ∈ B_(de) : κ(s) ∈ [α, β]A}`. Since
  `s ≠ R_0`, the brick `B_(de)` puts no condition on `κ(s)`, so this set differs from
  `U_d ∩ B_(de)`.

So `w(U_d) = U_d` iff `∀e ¬χ(d,e)`, i.e. iff `ψ'(d)`.

**The multiplicative form.** `(E_(k+1))` needs `U_d = t'_d p' s'` for a fixed `s'`. The elements:
- `flip_1 ∈ V_(R_0)` exchanges `0w` and `1w` on `κ(R_0)`.
- `flip_i = σ^-(i-1) flip_1 σ^(i-1)`, with `σ = σ_(R_0,R_1)`, flips digit `i` of `κ(R_0)`. It has
  length `O(i)`, and the `flip_i` commute pairwise.
- `γ ∈ V_(R_0)` sends `0w ↦ 00w`, `10w ↦ 01w` and `11w ↦ 1w`. It is an element of Thompson's `F`
  on `κ(R_0)`. For `j >= 0`, `γ^j(0C) = 0^(j+1) C`.

Put `s' = {κ : κ(R_0) ∈ 0C, κ(s) ∈ A}`, which is fixed. Put `p' = γ^(n-1)`, `h' = w` and
`k'_i = flip_i`. Then:
- `p' s' = U_(0^n)`, since `γ` acts on coordinate `R_0` alone and `s ≠ R_0`;
- `t'_d = flip_1^(d_1) ... flip_n^(d_n)` maps `U_(0^n)` onto `U_d`.

Hence `g'_d = p'^-1 t'_d^-1 w t'_d p'` fixes `s'` iff `w` fixes `t'_d p' s' = U_d`, iff `ψ'(d)`, by
Claim 1.

**Freeing two points.** The elements `w`, `flip_i` and `γ` need not fix any two clopen sets, so move
them into a corner. Fix a coordinate `q ∈ S_k` and put `X = B(q ↦ 0)` and `u = (q ↦ 0)`. Let
`φ : G_(k+1) -> G_(k+1)` be `φ(f) = h_u f h_u^-1` on `X` and the identity on `X^c`.
- By `h_u h_v = h_(u*v)`, a branch `h_v τ_g h_(v')^-1` goes to `h_(u*v) τ_g h_(u*v')^-1`. So `φ(f)`
  is in `G_(k+1)`, and `φ` is an injective homomorphism.
- `φ(f)(h_u Y) = h_u f(Y)` for every clopen `Y`.
- `φ(f)` fixes `X^c` pointwise, so it fixes `R'_0 = B(q ↦ 10)` and `R'_1 = B(q ↦ 11)`.

Put `K_(k+1) = φ(G_(k+1))`, generated by the fixed elements `φ(x)` for `x` in a finite generating set
of `G_(k+1)`. Take `s'' = h_u(s') ⊆ X`, which is distinct from `R'_0` and `R'_1`. The data of
`(E_(k+1))` are then:

```text
s = s'',  R_0 = R'_0,  R_1 = R'_1,  K_(k+1),
k_i = φ(flip_i),  h = φ(w),  p = φ(γ^(n-1)).
```

Condition (E) holds because `φ` is an injective homomorphism with `φ(f)(h_u Y) = h_u f(Y)`.

**Length.** Let `L_k(N)` bound the total length for formulas of size `N`. Then
`L_(k+1)(N) <= c (L_k(N) + N^2)` for a constant `c`: `w` contains each `(E_k)` word a bounded number of times (`Z` occurs four times in `w`, and `Y`,
`τ_p` twice in `Z`), the
`flip_i` cost `O(n^2)`, and `γ^(n-1)` costs `O(n)`. So `L_k(N) <= c^k · poly(N)`, which is polynomial
for each fixed `k`. `∎`

## 5. Base case: `(E_1)` in `2V` acting on clopen subsets of `C^2`

Here `G_1 = 2V` acts on `C^2`, with coordinates `1, 2` (the points of `S_0`), and `S_1` is the set of
proper nonempty clopen subsets of `C^2`. Write a point as `(x, z)`, with `x = x_1 x_2 ...` the first
coordinate.

**Digit gates on the first coordinate, at polynomial cost.** Let `σ = σ_(1,2)`, so
`σ(x_1 x', z) = (x', x_1 z)`. Then:
- `SWAP` exchanges the first two digits of `x`;
- `NOT` flips the first digit of `x`;
- `CNOT` flips `x_2` iff `x_1 = 1`;
- `TOF` is the Toffoli gate on the first three digits of `x` (flip `x_3` iff `x_1 = x_2 = 1`).

These are fixed elements of `V_1 <= 2V`. For a position `j >= 1`, `σ^-(j-1) SWAP σ^(j-1)` exchanges
digits `j` and `j+1` of `x` and has length `O(j)`. This is the same computation as for `flip_i` in §4.

Composing `O(M)` such adjacent transpositions moves any three positions `<= M` to positions `1, 2, 3`
and back. So a Toffoli, CNOT or NOT gate on arbitrary positions `<= M` has length `O(M^2)`. A
reversible circuit with `g` gates on wires `1..M` is a word of length `O(g M^2)`, acting on the first
`M` digits of `x` and fixing everything else.

**The circuit.** Let `ψ(d) = ∀y φ(d,y)`, with `d` of length `n`, `y` of length `m`, and `φ` a Boolean
circuit with `g` gates. Lay out the first coordinate as follows:

```text
positions  1..n          d        (free variables)
position   n+1           b        (answer bit)
positions  n+2..n+1+g    a        (ancillas, one per gate of φ)
positions  n+2+g..N      y        (universal variables),   N = n + 1 + g + m.
```

Let `Cφ` be the reversible circuit that computes each gate of `φ` into its own ancilla by Toffoli,
CNOT and NOT gates (AND by `TOF`; NOT and OR by CNOT, NOT and de Morgan). Its controls read only `d`,
`y` and earlier ancillas, and its targets are ancillas only.

So `Cφ` never reads or writes `b`. On inputs with `a = 0`, the output ancilla `o` ends up holding
`φ(d,y)`. Let `T` be "flip `b` iff `o = 0`", which is `NOT_o`, then a CNOT from `o` to `b`, then
`NOT_o`. Put

```text
H = Cφ^-1 T Cφ,
```

a word of length `O(g N^2)`. For `x = (d, b, 0^g, y, tail)`, the circuit `Cφ` leaves `d`, `b` and `y`
unchanged and sets `o = φ(d,y)`. Then `T` flips `b` iff `φ(d,y) = 0`, and `Cφ^-1` restores
`a = 0^g`. So

```text
H(d, b, 0^g, y, tail) = (d, b ⊕ ¬φ(d,y), 0^g, y, tail).
```

**Claim 2.** Let `U_d = {(x, z) : x has prefix d 0 0^g}`, a cone in the first coordinate times `C`.
Then `H(U_d) = U_d` iff `∀y φ(d,y)`.

If `φ(d,y) = 1` for every `y`, then `H` fixes `U_d` pointwise. Otherwise, pick `y` with
`φ(d,y) = 0`. The points of `U_d` with that `y` go to `b = 1`, outside `U_d`, and `H` is a bijection.

**The multiplicative form.** Let:
- `flip_i = σ^-(i-1) NOT σ^(i-1)` flip digit `i` of `x`, for `i <= n`;
- `γ ∈ V_1` be `0w ↦ 00w`, `10w ↦ 01w`, `11w ↦ 1w` on `x`;
- `s_base = 0C × C`, which is fixed;
- `p = γ^(n+g)`, so that `p(s_base) = 0^(n+1+g) C × C = U_(0^n)`;
- `t_d = flip_1^(d_1) ... flip_n^(d_n)`, which maps `U_(0^n)` to `U_d`.

Then `p^-1 t_d^-1 H t_d p` fixes `s_base` iff `ψ(d)`.

The layout was chosen so that `U_(0^n)` is a single cone, with `y` last, and `s_base` does not depend
on the formula.

**Freeing two points.** This is as in §4, with `q = 2`:
- `X = C × 0C`;
- `φ(f) = h_u f h_u^-1` on `X`, with `u = (2 ↦ 0)`;
- `R_0 = C × 10C`, `R_1 = C × 11C` and `s = h_u(s_base) = 0C × 0C`;
- `K_1 = φ(2V)`, and the words are `k_i = φ(flip_i)`, `h = φ(H)`, `p = φ(γ^(n+g))`.

All are computed in polynomial time, with total length `O(g N^2 + n^2)`. This is `(E_1)`. `∎`

## 6. Conclusion

**Orbit problems.** By §5 and §4, `(E_k)` holds for every `k >= 1`. Taking `n = 0` is not allowed in
`(E)`, so pad `ψ` with one dummy free variable. Then (E) at `d = 0` reduces the `Π_k` sentence
`ψ(0)` to membership of the single word `g_0` in `Stab(s)`, where `s` lies in the one orbit of `S_k`.

So `OP(G_k, S_k)` is `Π_k^p`-hard. With §1 it is `Π_k^p`-complete.

**Word problems.**
- `k = 1`: the word problem of `2V` is coNP-complete by Birget, arXiv:1902.03852 (title: "The word
  problem of the Brin-Thompson group is coNP-complete"). Lemma A cannot be used at this level, because
  `S_0` has only two points. The lane relies on Birget's statement here, and nothing below uses it.
- `k >= 2`: let `∃d χ(d)` be a `Σ_k` sentence, with `χ` in `Π_(k-1)`. Apply `(E_(k-1))` to `χ`, then
  Lemma A in `G_k = SV_(G_(k-1))`. The resulting word `w` satisfies `w ≠ 1` iff `∃d χ(d)`.

  Truth of `Σ_k` sentences is `Σ_k^p`-complete (Stockmeyer, Wrathall 1976). So the complement of the
  word problem of `G_k` is `Σ_k^p`-hard, and the word problem is `Π_k^p`-hard. With §1 it is
  `Π_k^p`-complete.

All reductions are polynomial-time many-one reductions, and they transfer to any finite generating set
by linear substitution. `∎`

## Computer check of the gadgets

`experiments/bh-tower-pi-k-2026-09-17/check_gadgets.py` models points of the cube by long finite
strings. Every map used is a prefix-replacement map with a coordinate permutation, so it is computed
exactly. Output is in `experiments/bh-tower-pi-k-2026-09-17/run-output.txt`.

- **Lemma A** on the toy actor `Sym(6)` acting on 6 points: 140 boxes over 15 random trials,
  `n = 2..4`, of which 37 have `g_d s_0 = s_0`. There were 0 mismatches between "`w` moves a sampled
  point of `B_d`" and "`g_d s_0 = s_0`".
- **§5 in `2V`**: random circuits with `n <= 3`, `m <= 3` and `g <= 8`. The check covers:
  - the formula for `H` at every `(d, b, y)`;
  - Claim 2;
  - the multiplicative form against `s_base`, on all 96 values of `d`, 27 of them with `∀y φ`.

  There were 0 mismatches. `|H|` came out at about `6 g N^2` letters over the fixed elements.

## What was not checked

- Lemma B and the corner map `φ` were not run: they are one level up, in `SV_(2V)`, and have no finite
  model here. The check covers Lemma A over a finite actor and the base gadgets only.
- The upper bound relies on the ESTABLISHED (b) and the iteration clause of
  `twisted-brin-thompson-wp-equals-actor-orbit-problem`. §1 spells out the leaf test for clopen
  stabilizers, which that clause states only in one sentence.


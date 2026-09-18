---
rg: 2
id: cantor-integer-maps-pair-lacks-relative-property-t-proof
kind: route
title: "Bernoulli random cone characters: almost invariant vectors for C(C,Z) ⋊ V that move every unbounded-depth subset of C(C,Z)"
target: cantor-integer-maps-pair-lacks-relative-property-t
requires: []
---

## 0. Notation

`C = {0,1}^N`. `W` is the set of finite binary words, `∅` the empty word,
`[w]` the cone of `w`, `ι_w : C → C`, `ι_w(x) = wx`. `A = C(C,Z)`, the locally
constant integer functions. `A_d` is the subgroup of functions constant on
every cone `[w]` with `|w| = d`. The depth of `k` is the least `d` with
`k ∈ A_d`. `G = A ⋊ V` with `h·k = k∘h^{-1}`. Every `g ∈ G` is `g = k h`
with `k ∈ A`, `h ∈ V`.

`Â = Hom(A, T)` is a compact abelian group (pointwise topology), `1` is its
trivial character, and `V` acts on it by continuous automorphisms,
`(h·χ)(k) = χ(k∘h)`. Let `H = {ξ ∈ Â : ξ(1_C) = 1}`.

Relative property (T) for a subset `Y ⊆ G` (Cornulier): for every `ε > 0` there
are a finite `Q ⊆ G` and `δ > 0` such that every unitary representation `π`
and unit vector `f` with `max_{q∈Q} ‖π(q)f − f‖ ≤ δ` satisfy
`sup_{y∈Y} ‖π(y)f − f‖ ≤ ε`. For a subgroup `Y` this is equivalent to the
usual definition (Jolissaint); §4 also gives the subgroup form directly for
`Y = A`.

For `ξ ∈ H`, `k ∈ A`, `w ∈ W` put `ξ_w(k) = ξ(k∘ι_w)`, a character of `A`.
If `|w| ≥ depth(k)` then `k∘ι_w = c·1_C` with `c ∈ Z`, so `ξ_w(k) = 1`.

## 1. The random character

Fix `ξ ∈ H` and `p ∈ (0, 1/2]`. Let `S ⊆ W` be random, each word in `S`
independently with probability `p`. Define

`χ_S(k) = ∏_{w ∈ S} ξ_w(k) = ∏_{w ∈ S, |w| < depth(k)} ξ(k∘ι_w)`.

The product is finite, `χ_S(k + k') = χ_S(k) χ_S(k')`, so `χ_S ∈ Â`, and
`χ_S(1_C) = 1`. For each `k`, `χ_S(k)` depends on finitely many coordinates
of `S`, so `S ↦ χ_S` is continuous from `{0,1}^W` to `Â`. Let `ν_p` be the law
of `χ_S`, a Borel probability measure on `Â`.

**Lemma 1.1 (Fourier coefficients).** For `k ∈ A` put `z_w = ξ(k∘ι_w)`. Then

`E χ_S(k) = ∏_{|w| < depth(k)} (1 − p + p z_w)`,

`|E χ_S(k)| ≤ exp(−p(1−p) E_ξ(k))`, where `E_ξ(k) = Σ_{w∈W} (1 − Re ξ(k∘ι_w))`,

`∫ |χ(k) − 1|² dν_p(χ) ≤ 4 p (2^{depth(k)} − 1)`.

*Proof.* `χ_S(k) = ∏_w z_w^{1[w∈S]}` with independent factors, and
`E z^{1[w∈S]} = 1 − p + pz`. Next
`|1 − p + pz|² = 1 − 2p(1−p)(1 − Re z) ≤ exp(−2p(1−p)(1 − Re z))`; take the
product and a square root. Terms with `|w| ≥ depth(k)` have `z_w = 1`, so the
sum defining `E_ξ(k)` is finite. Finally `|χ_S(k) − 1|² ≤ 4·1[χ_S(k) ≠ 1]`, and
`χ_S(k) ≠ 1` forces `S` to contain one of the `2^{depth(k)} − 1` words of
length `< depth(k)`. ∎

## 2. Near-equivariance

Let `h ∈ V` be given by complete prefix codes `u_1, …, u_n` (domain) and
`v_1, …, v_n` (range) with `h(u_i x) = v_i x`. Let `D` be the set of proper
prefixes of the `u_i` and `R` the set of proper prefixes of the `v_i`. These are
the internal vertices of two finite rooted binary trees with `n` leaves, so
`|D| = |R| = n − 1`. The map `h(u_i t) = v_i t` is a bijection
`W ∖ D → W ∖ R`.

**Lemma 2.1.** If `w ∉ D` then `h·ξ_w = ξ_{h(w)}`.

*Proof.* Write `w = u_i t`. Then `h∘ι_w = ι_{v_i t}`, so
`(h·ξ_w)(k) = ξ(k∘h∘ι_w) = ξ(k∘ι_{h(w)}) = ξ_{h(w)}(k)`. ∎

**Lemma 2.2.** `‖h_*ν_p − ν_p‖ ≤ 2p(|D| + |R|) = 4p(n−1)` (total mass of the
signed measure).

*Proof.* `(h·χ_S)(k) = χ_S(k∘h) = ∏_{w∈S} (h·ξ_w)(k)`. Let `T ⊆ R` be an
independent Bernoulli(`p`) subset and `S' = h(S ∖ D) ∪ T`. The coordinates of
`S'` on `W ∖ R` are the coordinates of `S` on `W ∖ D`, relabelled by a
bijection, and on `R` they are those of `T`. So `S'` is Bernoulli(`p`) and
`χ_{S'}` has law `ν_p`. By Lemma 2.1, on the event `S ∩ D = ∅, T = ∅` we have
`h·χ_S = ∏_{w∈S} ξ_{h(w)} = χ_{S'}`. That event fails with probability at most
`p(|D| + |R|)`. Two random variables that agree off an event of probability
`q` have laws at total-mass distance at most `2q`. ∎

## 3. The representation

Fix weights `c_h > 0` on `V` with `Σ c_h = 1` and let
`μ = Σ_{h∈V} c_h h_*ν_p`. It is `V`-quasi-invariant and `ν_p ≪ μ`. On
`L²(Â, μ)` define

`(π_p(k) f)(χ) = χ(k) f(χ)`,  `(π_p(h) f)(χ) = (d h_*μ / dμ)^{1/2}(χ) · f(h^{-1}·χ)`.

Both are unitary, and `π_p(h) π_p(k) π_p(h)^{-1}` is multiplication by
`(h^{-1}·χ)(k) = χ(h·k)`, i.e. `π_p(h·k)`. So `π_p` is a unitary representation
of `G`. Let `f_p = (dν_p/dμ)^{1/2}`, a unit vector. Then
`π_p(h) f_p = (d h_*ν_p / dμ)^{1/2}`, and

`‖π_p(h) f_p − f_p‖² = ∫ (√a − √b)² dμ ≤ ∫ |a − b| dμ = ‖h_*ν_p − ν_p‖ ≤ 4p(n_h − 1)`

(`a, b` the two densities, `n_h` the number of leaves of `h`), by Lemma 2.2.
Also `‖π_p(k) f_p − f_p‖² = ∫ |χ(k) − 1|² dν_p ≤ 4p(2^{depth(k)} − 1)` by
Lemma 1.1. For `g = kh`,
`‖π_p(g) f_p − f_p‖ ≤ ‖π_p(h) f_p − f_p‖ + ‖π_p(k) f_p − f_p‖`. Hence:

**Lemma 3.1.** For every `g ∈ G`, `‖π_p(g) f_p − f_p‖ → 0` as `p → 0`,
whatever `ξ ∈ H` is.

## 4. Main theorem: `(G, A)` does not have relative (T)

Take `ξ ∈ H`, `ξ ≠ 1`, and `k_0 ∈ A` with `ξ(k_0) ≠ 1`. Such `ξ` exist since
`A / Z·1_C ≠ 0`.

**Lemma 4.1.** `ν_p({1}) = 0`. Hence `μ({1}) = 0`, and `π_p` has no nonzero
`A`-invariant vector.

*Proof.* For a word `v` let `k_v ∈ A` be `k_v(vx) = k_0(x)` and `k_v = 0` off
`[v]`. Then `k_v∘ι_{vt} = k_0∘ι_t`, `k_v∘ι_w = 0` for `w` incomparable with
`v`, and `k_v∘ι_v = k_0`. So

`χ_S(k_v) = ξ(k_0)^{1[v∈S]} · X_v`,

where `X_v` depends only on the coordinates of `S` at proper prefixes and proper
extensions of `v`. Fix `m` and the `2^m` words `v` of length `m`. Condition on
all coordinates of `S` except `{1[v ∈ S] : |v| = m}`. Then every `X_v` is fixed,
the `1[v∈S]` are independent, and since `ξ(k_0) ≠ 1` the event
`χ_S(k_v) = 1` pins `1[v∈S]` to one value, of conditional probability
`≤ 1 − p`. So `P(χ_S = 1) ≤ (1 − p)^{2^m}` for every `m`, i.e. `0`. The point
`1` is `V`-fixed, so `μ({1}) = Σ c_h ν_p({1}) = 0`. An `A`-invariant `f`
satisfies `(χ(k) − 1) f(χ) = 0` μ-a.e. for all `k` in the countable group `A`,
so `f` is supported on `{1}`, hence `f = 0`. ∎

**Theorem 4.2.** `(G, A)` does not have relative property (T).

*Proof.* `π = ⊕_{j ≥ 2} π_{1/j}` has no nonzero `A`-invariant vector by
Lemma 4.1. By Lemma 3.1, for every finite `Q ⊆ G` and `δ > 0` some `f_{1/j}` is
`(Q, δ)`-invariant. ∎

## 5. Every relatively rigid subset of `A` has bounded depth

**Lemma 5.1.** If `Y ⊆ A` has unbounded depth, there is `ξ ∈ H` with
`sup_{y∈Y} E_ξ(y) = ∞`.

*Proof.* Suppose not. `ξ ↦ E_ξ(y)` is continuous on `H` (finite sum), so
`H_N = {ξ ∈ H : E_ξ(y) ≤ N for all y ∈ Y}` is closed and `H = ∪_N H_N`. By Baire
some `H_N` contains a nonempty open subset of `H`. That subset contains
`ξ_0 K`, where `K = {ξ ∈ H : ξ(k_1) = … = ξ(k_r) = 1}` for some `ξ_0 ∈ H` and
`k_1, …, k_r ∈ A`: the set `{ξ ∈ H : |ξ(k_i) − 1| < ε, i ≤ r}` is an open
neighbourhood of `1` in `H` and contains `K`. Let `B = ⟨1_C, k_1, …, k_r⟩`, so
`K = B^⊥`, and let `d_0` be the largest depth of the `k_i`, so `B ⊆ A_{d_0}`. For
normalized Haar measure on `K`, `∫_K ξ(k) dξ = 1[k ∈ B]` (if `k ∉ B`, duality
for the discrete group `A/B` gives `ξ ∈ K` with `ξ(k) ≠ 1`). Hence for `y ∈ Y`

`N ≥ ∫_K E_{ξ_0 ξ}(y) dξ = Σ_w (1 − Re ξ_0(y∘ι_w) 1[y∘ι_w ∈ B]) ≥ #{w : y∘ι_w ∉ A_{d_0}}`.

Let `D = depth(y) ≥ 1`. There is a word `u` with `|u| = D − 1` and `y∘ι_u`
nonconstant. For the prefix `u_j` of `u` of length `j`, `y∘ι_{u_j}` composed with
`ι_{u'}`, `|u'| = D − 1 − j`, is `y∘ι_u`, so `y∘ι_{u_j} ∉ A_{D−1−j}`. For
`j ≤ D − 1 − d_0` this gives `y∘ι_{u_j} ∉ A_{d_0}`. So `N ≥ D − d_0` for all
`y ∈ Y`, contradicting unbounded depth. ∎

**Theorem 5.2.** If `Y ⊆ A` and `(G, Y)` has relative property (T), then
`Y ⊆ A_d` for some `d`.

*Proof.* Let `Y` have unbounded depth and take `ξ` from Lemma 5.1. For
`p ∈ (0, 1/2]` choose `y_p ∈ Y` with `E_ξ(y_p) ≥ 1/p`. By Lemma 1.1,
`|E χ_S(y_p)| ≤ exp(−(1−p)) ≤ e^{−1/2}`, so

`‖π_p(y_p) f_p − f_p‖² = 2 − 2 Re E χ_S(y_p) ≥ 2(1 − e^{−1/2}) > 0.78`.

By Lemma 3.1, for any finite `Q` and `δ > 0` some `f_p` is `(Q, δ)`-invariant
but moves a point of `Y` by more than `0.88`. So the definition fails for
`ε = 0.88`. ∎

`Y = A` has unbounded depth, so Theorem 5.2 reproves Theorem 4.2 through
Jolissaint's equivalence.

## 6. Reduction to one cyclic subgroup

**Proposition 6.1.** For `Y ⊆ A` the following hold.

1. If `(G, Y)` has relative property (T) then `Y ⊆ A_d` for some `d`
   (Theorem 5.2).
2. `(G, A_d)` has relative property (T) for some `d ≥ 1` iff it has it for all
   `d`, iff `(G, Z·1_{[0]})` has relative property (T).

*Proof of 2.* Relatively rigid subsets are closed under subsets, conjugation and
finite products, from `‖π(g y g^{-1}) f − f‖ ≤ 2‖π(g^{-1}) f − f‖ + ‖π(y) f − f‖`
and `‖π(xy) f − f‖ ≤ ‖π(x) f − f‖ + ‖π(y) f − f‖`. For `d ≥ 1` each `[v]` with
`|v| = d` is a proper nonempty clopen, so some `h ∈ V` has `h[0] = [v]`, i.e.
`h·1_{[0]} = 1_{[v]}`. Hence `A_d = ∏_{|v| = d} Z·1_{[v]}` is a finite product of
conjugates of `Z·1_{[0]}`, and `Z·1_{[0]} ⊆ A_1 ⊆ A_d`. ∎

So every relatively rigid subgroup of `G` inside `A` lies in some `A_d`, and
among subgroups of `A` of unbounded depth none is rigid. The route
"relative (T) inside `C(C,Z)`" to `cantor-integer-maps-by-v-are-not-a-t-menable`
reduces, for subgroups, to one question: does `(C(C,Z) ⋊ V, Z·1_{[0]})` have
relative property (T)? If yes, then `G`, and so `2V`, is not Haagerup, because
`Z·1_{[0]}` is infinite. The random cone characters cannot decide this:
`χ_S(1_{[0]}) = ξ(1_{[0]})^{1[∅ ∈ S]}` sees only the root word, so `ν_p` gives
mass `≥ 1 − p` to `{χ : χ(1_{[0]}) = 1}` and `π_p` has nonzero
`1_{[0]}`-invariant vectors. Any witness against
rigidity of `Z·1_{[0]}` must be non-product at the root scale.

## 7. Reduction to the centre

`1_C` is fixed by `V`, so `Z·1_C` is central in `G`. Let `Q = G / Z·1_C`.

**Proposition 7.1.** `(G, Z·1_{[0]})` has relative property (T) iff the centre
`(G, Z·1_C)` has it. With Proposition 6.1, the rigid-subgroup-inside-`A` route
reduces exactly to one question: is the centre `Z·1_C` of `C(C,Z) ⋊ V`
relatively rigid in `G`?

*Proof.* (⇒) `m·1_C = m·1_{[0]} + m·1_{[1]}`, and `1_{[1]}` is conjugate to
`1_{[0]}`. So `Z·1_C` lies in a product of two conjugates of `Z·1_{[0]}`, and
the closure properties from the proof of Proposition 6.1 apply.

(⇐) Suppose `Z·1_{[0]}` is not rigid. Fix `ε > 0` as in the negated
definition and an exhausting sequence of finite sets `Q_n ⊆ G`. There are unitary
representations `π_n` and unit vectors `f_n` with
`max_{q∈Q_n} ‖π_n(q) f_n − f_n‖ ≤ 1/n` and
`sup_m ‖π_n(m·1_{[0]}) f_n − f_n‖ > ε`. Let `ν_n` be the spectral measure of
`f_n` for `π_n|_A`, a probability measure on `Â`. Then:

- `∫ |χ(k) − 1|² dν_n = ‖π_n(k) f_n − f_n‖² → 0` for each `k ∈ A`, so
  `ν_n → δ_1` weak*;
- `‖h_*ν_n − ν_n‖ ≤ 2 ‖π_n(h) f_n − f_n‖ → 0` for each `h ∈ V` (artifact §3(f));
- `∫ |χ(m·1_{[0]}) − 1|² dν_n = ‖π_n(m·1_{[0]}) f_n − f_n‖²`.

Define the homomorphism `T : A → A` by `T k(0x) = k(x)`, `T k(1x) = 0`, and the
embedding `ι : V → V` by `ι(h)(0x) = 0h(x)`, `ι(h)(1x) = 1x`. Then
`T(k∘h) = (T k)∘ι(h)`. Let `Ψ : Â → Â`, `Ψ(χ) = χ∘T`, a continuous homomorphism
with `Ψ(1) = 1`. For `h ∈ V` and `χ ∈ Â`,

`Ψ(ι(h)·χ)(k) = χ((T k)∘ι(h)) = χ(T(k∘h)) = (h·Ψ(χ))(k)`.

Put `ν'_n = Ψ_*ν_n`. Then `h_*ν'_n = Ψ_*(ι(h)_*ν_n)`, so
`‖h_*ν'_n − ν'_n‖ ≤ ‖ι(h)_*ν_n − ν_n‖ → 0`. Also `ν'_n → δ_1`, and since
`T(1_C) = 1_{[0]}`,

`∫ |χ(m·1_C) − 1|² dν'_n = ∫ |χ(m·1_{[0]}) − 1|² dν_n`.

Build the representation of §3 from `ν'_n`: `μ'_n = Σ_h c_h h_*ν'_n` and
`f'_n = (dν'_n/dμ'_n)^{1/2}` in `L²(Â, μ'_n)`. As in §3, `f'_n` is almost
invariant under every `g ∈ G` as `n → ∞`, and
`‖π(m·1_C) f'_n − f'_n‖² = ∫ |χ(m·1_C) − 1|² dν'_n`. So for every finite `Q` and
`δ > 0` some `f'_n` is `(Q, δ)`-invariant and moves a point of `Z·1_C` by more
than `ε`. Hence `Z·1_C` is not rigid. ∎

**Remark 7.2 (the centre is not detected by quasimorphisms).** For `h ∈ V` with
`h[1] = U`, the commutator of `h` and `m·1_{[1]}` in `G` is `m(1_U − 1_{[1]})`.
The identity of artifact §3(b) gives

`m·1_{[1]} = m(1_{[0]} − 1_{[1]}) − m(1_{[00]} − 1_{[1]}) − m(1_{[01]} − 1_{[1]})`,

a product of three commutators. `m·1_C` is `m·1_{[1]}` plus a conjugate of it, so
its commutator length is at most `6` for every `m`. So `scl(1_C) = 0`, and every
homogeneous quasimorphism of `G` vanishes on the centre. Consequently the class
`c ∈ H²(Q; R)` of the central extension `0 → Z·1_C → G → Q → 1` has no bounded
representative, since a bounded class would give a quasimorphism equal to `1` on
`1_C` (standard). The class is nonzero: `Q` is perfect, so `H¹(Q; T) = 0`, so
`H²(Q; Z) → H²(Q; R)` is injective, and `c = 0` in `H²(Q; Z)` would split `G`
as `Q × Z`, which is not perfect. So the centre sits in a Heisenberg-like
position: a real, unbounded central class. Twisting an almost invariant vector by
a rotation-number-type phase `e^{2πitφ}` is unavailable.

**What a witness against rigidity must be.** Restricting to the `G`-invariant
spectral subspace where `π(1_C) ≠ 1`, a witness is a sequence of probability
measures `ν_n` on `Â_{≠} = {χ : χ(1_C) ≠ 1}` with `ν_n → δ_1` and
`‖h_*ν_n − ν_n‖ → 0` for every `h ∈ V`. Two families already fail:
- the Bernoulli cone products of §1, which live on `{χ(1_C) = 1}`;
- the localized characters of artifact §3(g), which are `V`-paradoxical.

Also, a product `∏_{w∈S} ξ_w` with `ξ(1_C) ≠ 1` is undefined at every `1_{[u]}`
once `S` has infinitely many words below `u`. So the §1 mechanism does not extend
to the centre by changing `ξ`.

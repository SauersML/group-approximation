# Fold seeds cannot be sparse in any action weakly contained in Bernoulli

Agent swarm-0917-w8-w8-fp-break, 2026-09-18. Scripts:
`experiments/fpbs-fold-seed-floor-2026-09-17/`.

## 0. Statement

`L = F(a, b)`. For a p.m.p. action of `L` on `(X, μ)` and measurable `A ⊆ X`,
`cl(A)` is the closure of `A` under the 2-of-3 rule on the triples
`T_w = (w, a w, b w)` (a triple with a repeated point counts that point with
multiplicity; for free actions the three points are distinct). Put

```text
σ_b(X) := inf { μ(A) : cl(A) is conull }.
```

**Theorem A.** If the action of `L` on `X` is weakly contained in a Bernoulli
shift of `L`, then `σ_b(X) ≥ 1/80`. More precisely `σ_b(X) ≥ (1-η) α / 2`
whenever `α ∈ (0, 1/2)`, `η ∈ (0, 1)` satisfy

```text
E(α, η) := H(α) + 2α H((1+η)/2) + (1+η) α ln α < 0,
```

with `H(x) = −x ln x − (1−x) ln(1−x)`. The choice `α = 1/8`, `η = 4/5` gives
`E = −0.00983… < 0` and the floor `1/80`; the numerical optimum is
`≈ 0.01406` (`floor_constant.py`).

The fold artifact `research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md`
proved `σ_b = 0` on every `χ`-odometer product, `σ_b ≤ 5/32` on Bernoulli
(iid single-site seeds), and recorded in its §6: "No positive lower bound on
`σ_b` is known for any free action." Theorem A supplies one for the whole
weak-containment class of Bernoulli.

## 1. Four lemmas

Throughout, `cl_T(A)` is the set reached after `T` parallel rounds of the
rule (`cl_0 = A`). Since every derivation is finite, `cl(A) = ∪_T cl_T(A)`,
increasing. Membership of `x` in `cl_T(A)` depends only on `A ∩ B_{2T}(x)`,
where `B_r(x) = { g x : |g| ≤ r }`, because two points of one triple are at
word distance at most 2. So `1_{cl_T(A)}(x)` is a fixed monotone Boolean
function `Ψ_T` of the pattern `(1_A(g x))_{|g| ≤ 2T}` when `g ↦ g x` is
injective on the ball (free actions, finite tree-like balls).

**Lemma 1 (weak containment moves patterns).** Let `α ≺ β` (p.m.p. actions of
`L`), `A ⊆ X_α`, `F ⊆ L` finite with `e ∈ F`, `ε > 0`. There is
`B ⊆ X_β` such that the law of `(1_B(g y))_{g ∈ F}` under `ν` is within `ε`
in total variation of the law of `(1_A(g x))_{g ∈ F}` under `μ`.

*Proof.* Let
`P = { A_ω : ω ∈ {0,1}^F }`, `A_ω = { x : 1_A(g x) = ω(g) ∀ g ∈ F }`. By the
definition of weak containment (Kechris) there are `B_ω ⊆ X_β` with
`|ν(g B_ω ∩ B_ω') − μ(g A_ω ∩ A_ω')| < ε'` for all `g ∈ F`, all
`ω, ω'`. Taking `g = e` and replacing the `B_ω` by the partition
`B'_ω = B_ω \ ∪_{ω'' < ω} B_ω''` (fixed order, remainder into one cell)
changes all these quantities by `O(4^{|F|} ε')`, so assume the `B_ω`
partition `X_β`. Put `B = ∪_{ω(e) = 1} B_ω`.

If `x ∈ A_ω` then `g x ∈ A_{ω'}` only for `ω'` with `ω'(e) = ω(g)`. Hence
`μ(A_ω ∩ g^{-1} A_{ω'}) = 0` for inconsistent pairs, so
`ν(B_ω ∩ g^{-1} B_{ω'}) < ε'` for them. For `y ∈ B_ω` outside the union `Z`
of these sets over all `g ∈ F` and inconsistent `ω'`, `g y ∈ B_{ω'}` with
`ω'(e) = ω(g)`, i.e. `1_B(g y) = ω(g)`. So off `Z` the `B`-pattern of `y`
is `ω` exactly when `y ∈ B_ω`, and `ν(Z) ≤ |F| 4^{|F|} ε'`. The laws of the
patterns are then `(ν(B_ω))_ω` up to `ν(Z)`, and `|ν(B_ω) − μ(A_ω)| < ε'`.
Choose `ε'` small. ∎

(The statement is the standard fact that weak containment is equivalent to
approximation of finite-alphabet factor statistics; the proof above only
uses Kechris' pairwise definition.)

**Lemma 2 (cylinder approximation).** In a Bernoulli shift `Y^L` (any
standard base), every `B` is within `ε` in measure of a cylinder set `B'`
depending on finitely many coordinates through a finite partition of `Y`.
Hence `B'` is a set of a finite-alphabet Bernoulli shift `Q^L` with some
law `p` on the finite set `Q`. Moreover `B'` has the form
`{ y : (λ(g y))_{g ∈ F_0} ∈ C }` where `λ(y) := y(e) ∈ Q` and `F_0` is
finite, because `λ(g y) = y(g^{-1})`. ∎

Patterns change little: `P(1_B(g y) ≠ 1_{B'}(g y) for some g ∈ F) ≤ |F| ε`.

**Lemma 3 (random permutation models).** Let `σ_a, σ_b` be independent
uniform permutations of `[n]` and `ℓ : [n] → Q` iid with law `p`, independent
of them. Let `L` act on `[n]` by `a·v = σ_a v`, `b·v = σ_b v`. For a finite
`F ⊆ L` and `C ⊆ Q^F` put `S_n = { v : (ℓ(g·v))_{g∈F} ∈ C }`. Let `B'` be
the corresponding set of `Q^L`, `ρ` the Bernoulli measure. Then for each
fixed `T`, as `n → ∞`:

```text
E |S_n| / n → ρ(B'),     E |cl_T(S_n)| / n → ρ(cl_T(B')),
```

where `cl_T` on `[n]` uses the triples `(v, σ_a v, σ_b v)` with multiplicity.

*Proof.* Let `R = 2T + max_{g∈F} |g| + 2`. Say `v` is *good* if the orbit
map `g ↦ g·v` is injective on the word ball `B_R ⊆ L`. Expose the ball
around `v` letter by letter: each exposure of `σ_s^{±1} u` is uniform among
at least `n − |B_R|` unexposed values, so it hits an already seen vertex with
probability at most `|B_R| / (n − |B_R|)`. Hence
`P(v not good) ≤ |B_R|^2 / (n − |B_R|) → 0`. If `v` is good, the labels
`(ℓ(g·v))_{g ∈ B_R}` are iid with law `p` (the labels are independent of the
permutations and sit on distinct vertices), and the triple structure on
`B_{R−1}·v` is the image of the triple structure on the ball of the Cayley
graph. So `1_{S_n}(v)` and `1_{cl_T(S_n)}(v)` have, on the good event, the
same joint law as `1_{B'}(y)` and `1_{cl_T(B')}(y)` under `ρ`: both are the
function `Ψ_T` of the iid pattern on the ball (the Bernoulli coordinates
`λ(g y)`, `g ∈ L`, are iid with law `p`). Average over `v`. ∎

**Lemma 4 (small sets span few slots).** Call `(v, s)`, `s ∈ {a, b}`, a
*slot* of `I ⊆ [n]` if `v ∈ I` and `σ_s v ∈ I`. Fix `α, η` with
`E(α, η) < 0`, `m = ⌈α n⌉`, `k = ⌈(1+η) m⌉`. Then

```text
P( some I with |I| = m has at least k slots ) → 0.
```

*Proof.* For fixed `I` and fixed sets `V_a, V_b ⊆ I` with
`|V_a| + |V_b| = k`, the probability that `σ_a V_a ⊆ I` and `σ_b V_b ⊆ I` is
`[(m)_{|V_a|}/(n)_{|V_a|}] [(m)_{|V_b|}/(n)_{|V_b|}] ≤ (m/n)^k`. There are
`Σ_{i+j=k} C(m,i) C(m,j) = C(2m, k)` choices of `(V_a, V_b)` and `C(n, m)`
choices of `I`. So the probability is at most
`C(n,m) C(2m,k) (m/n)^k ≤ exp( n H(m/n) + 2m H(k/2m) + k ln(m/n) )`,
using `C(N, K) ≤ e^{N H(K/N)}`. The exponent is `n (E(α, η) + o(1))`,
because `m/n → α`, `k/2m → (1+η)/2` and `E` is continuous. ∎

`floor_constant.py` evaluates `E` and the exact finite-`n` first moment
(`log ≤ −21` at `n = 10^4`, `−1188` at `n = 10^6` for the optimal pair).

**Lemma 5 (crossing count).** Let `S ⊆ [n]` and `m ≤ n`. If
`|S| < m ≤ |cl(S)|`, some `I` with `|I| = m` has at least `2(m − |S|)` slots.

*Proof.* Build `cl(S)` sequentially: start from `I = S`; while some triple
`T_v` has at least two of its three entries (with multiplicity) in `I` and
an entry outside `I`, add that entry. This reaches exactly `cl(S)` (the rule
is monotone), one vertex at a time, so it passes through a set `I` with
`|I| = m`. Each of the `m − |S|` added vertices was added through a triple
`T_v` all of whose entries lie in `I` afterwards. A triple adds at most one
vertex: after it fires it has no entry outside `I`. So these triples are
`m − |S|` distinct `T_v`, with distinct `v`, and each gives the two slots
`(v, a)`, `(v, b)` of `I`. ∎

## 2. Proof of Theorem A

(Notation: in Lemma 1 and below, `α` also names the action `L ↷ (X, μ)`;
in `(1−η) α / 2`, `E(α, η)` and `m = ⌈α n⌉` it is the density parameter.
The two uses never interact.)

Let `α ≺ β = (Y^L, ρ_Y)` and `A ⊆ X` with `cl(A)` conull; suppose
`μ(A) < (1−η) α / 2 − 4γ` for some `γ > 0`, and derive a contradiction.

1. **Truncate.** Choose `T` with `μ(cl_T(A)) > 1 − γ`.
2. **Move to Bernoulli.** Apply Lemma 1 with `F = B_{2T}` (so that `e ∈ F`
   and `cl_T` at a point is `Ψ_T` of the `F`-pattern). For free `α` and
   `β`, `μ(A)` and `μ(cl_T(A))` are functionals of the `F`-pattern law
   (`1_A(x)` is the `e`-coordinate; `1_{cl_T(A)}(x) = Ψ_T(pattern)`), so we
   get `B ⊆ Y^L` with `ρ(B) < μ(A) + γ` and `ρ(cl_T(B)) > 1 − 2γ`. (If `α` is
   not free, pass first to the free action `α × β`, which is still weakly
   contained in `β` since `β × β ≅ β`; `A × Y^L` has the same measure and
   the same closure pattern, as the triple structure only gets finer.)
3. **Cylinder.** By Lemma 2 choose a cylinder `B'` with `ρ(B Δ B')` so small
   that `ρ(B') < μ(A) + 2γ` and `ρ(cl_T(B')) > 1 − 3γ` (the `F`-patterns of
   `B` and `B'` agree off a set of measure `≤ |F| ρ(B Δ B')`).
4. **Finite models.** Let `S_n` be as in Lemma 3 for `B'`. Then
   `E|S_n|/n → ρ(B')` and `E|cl_T(S_n)|/n → ρ(cl_T(B')) > 1 − 3γ`. Since
   `|cl_T(S_n)| ≤ n`, `P(|cl_T(S_n)| ≥ α n + 1) ≥ 1 − 3γ/(1 − α) − o(1)`.
5. **Count.** Let `m = ⌈α n⌉` and `G_n` the event that no `m`-set has
   `⌈(1+η) m⌉` slots; `P(G_n) → 1` by Lemma 4. On
   `G_n ∩ {|cl(S_n)| ≥ m}`, Lemma 5 gives either `|S_n| ≥ m` or
   `2(m − |S_n|) < (1+η) m`; in both cases `|S_n| > (1−η) m / 2`.
6. **Contradiction.** Hence
   `E|S_n|/n ≥ ((1−η) α / 2)(1 − 3γ/(1−α) − o(1))`. Letting `n → ∞`,
   `μ(A) + 2γ > ρ(B') ≥ (1−η)(α/2)(1 − 6γ)`, which contradicts the
   assumption `μ(A) < (1−η) α/2 − 4γ` once `γ` is small, because
   `(1−η)(α/2) 6γ < 2γ` for `α < 1/2`. ∎

So every `A` with conull closure has `μ(A) ≥ (1−η) α / 2`, i.e.
`σ_b ≥ 1/80` with `(α, η) = (1/8, 4/5)`.

## 3. Consequences and what remains

Write `W_b(Γ)` for the actions of `Γ` weakly contained in a Bernoulli shift of
`Γ`. Items (a) and (b) below use only Theorem A. Items (c) to (e) also use
Theorem 1.2 (exactness) of
`research/artifacts/fpbs-fold-bootstrap-seeding-2026-09-17.md`, which is
proved there but unrefereed.

**(a) Uniform floor at every stage of `Gamma_mal`.** Let `X ∈ W_b(Gamma_mal)`.
The restriction of a Bernoulli shift of `Gamma_mal` to `H_{n+1} = F(a, b_{n+1})`
is a Bernoulli shift of `H_{n+1}`, with base `Y^{H_{n+1}\Gamma_mal}`.
Restriction preserves weak containment. So `X|_{H_{n+1}} ∈ W_b(H_{n+1})`. The
stage pair `H_n = ⟨a, b_{n+1} a b_{n+1}^{-2}⟩ ≤ H_{n+1}` is the pair `K ≤ L`
with `b = b_{n+1}`. Hence `σ_{b_{n+1}}(X) ≥ 1/80` for every `n`, uniformly.

**(b) Separation.** The `χ`-odometer products `β × Ẑ_χ` have `σ_b = 0` at
every stage. Every action in `W_b` has `σ_b ≥ 1/80`. So `σ_b` is a
`W_b`-invariant that sharply separates free actions of one group. This is
consistent with the fact that the odometer products are not in `W_b`: their
Koopman representation contains the nontrivial characters
`g ↦ e^{2πi χ(g)/N}` (functions of `z mod N`), while
the Koopman representation of a Bernoulli shift on `L²_0` is a multiple of
the regular representation, which weakly contains no finite-dimensional
representation of the nonamenable group `Gamma_mal`. Theorem A gives a second,
combinatorial proof of this fact. It also shows that `C(Gamma_mal) = 2`, which is witnessed by the
odometers, cannot be transported to Bernoulli by any one-double-coset
bootstrap.

**(c) Single-double-coset relative cost.** By the double-coset remark of the
fold artifact together with Theorem 1.2, `relC_{K b^{±1} K}(R_L; R_K) = σ_b`.
Hence, on `W_b`, every graphing repairing `R_K` to `R_L` with labels in one
double coset `K b^{±1} K` has mass `≥ 1/80`. Combined with fold §3,

```text
1/80 ≤ σ_b(Bernoulli of F_2) ≤ 5/32.
```

The upper bound is attained by iid single-site seeds. The greedy search in
`random_schreier_contagious.py` finds contagious densities of about `0.11`
on random Schreier graphs; these are upper bounds for the finite models.

**(d) Telescoping schemes cost infinity on `W_b`.** Take a stagewise scheme
`E_{H_n} ∨ b_{n+1}|_{A_n} = E_{H_{n+1}}` for all `n`. By Theorem 1.2 each
equality forces `cl(A_n)` to be conull for the stage-`(n+1)` triples. By (a)
this forces `μ(A_n) ≥ 1/80`. So the total mass `Σ_n μ(A_n)` is infinite. This
kills, on `W_b`, the odometer mechanism of
`fpbs-mal-odometer-product-actions-have-cost-two`, and also every repair of
one stage by one double coset (one-stage sprinkling, iid or FIID seeds, any
factor-of-iid choice of `A_n`).

**(e) What survives.** A cost-`2` graphing of the Bernoulli shift of
`Gamma_mal` must avoid (d) in one of three ways:

1. It uses several double cosets `K g K` at once. Theorem A says nothing about
   `relC(R_L; R_K)` as a whole. Mixing cosets can give extra identifications
   that are not produced by the fold.
2. It uses labels from deeper stages, `b_{n+2}, b_{n+3}, …`, to repair
   `H_n → H_{n+1}`. These are not in `L = H_{n+1}`.
3. It does not factor stagewise at all.

The proof of Theorem A reduces all of these to one finite question. Call it
the *local relative combinatorial cost* of random Schreier graphs of `L`
relative to `K`: the minimal density of a set of extra edges, with labels of
word length `≤ T`, whose union with the `K`-components connects the ball
structure. The question is whether this is bounded below by a constant `c > 0`
that is uniform in the witness length `T`.

Lemmas 1 to 3 transfer any such bound to all of `W_b`, with no change. For a
single double coset the invariant is small-set slot sparsity at the crossing
size `α n` (Lemmas 4 and 5). For several double cosets, the analogous count
must control the union of `K`-cosets. That count is not done here.

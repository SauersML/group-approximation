---
rg: 2
id: thompson-f-ackermann-folner-via-tree-derivative-hierarchy
kind: route
title: Ackermann Følner lower bound for F from a derivative hierarchy on trees
target: thompson-f-folner-function-dominates-every-ackermann-level
requires: [marginal-derivative-amplification-is-sharp-at-log-height, thompson-f-trees-carry-an-ackermann-derivative-hierarchy]
---

The route assumes `H_k` from `thompson-f-trees-carry-an-ackermann-derivative-hierarchy`, and uses
Theorem A of `marginal-derivative-amplification-is-sharp-at-log-height`. Moore's statements are
quoted verbatim from the TeX source of arXiv:0905.1118v7.

**Imported facts.**
- *Lemma 3.15:*
  > Let G be a group with a finite generating set Γ, acting on itself from the right. If A ⊆ G
  > is a ε-Følner set, then there is a B ⊆ G which is an ε-Følner set such that B is
  > Γ-connected, B contains the identity, and |B| ≤ |A|.
- *Lemma 4.2:*
  > There is a constant C such that if A ⊆ F is a (right) ε-Følner set, then there is a weighted
  > Cε-Følner set of trees supported on a subset of {R_f : f ∈ A}.
- *Burillo–Cleary–Stein,* as used by Moore at the end of Section 5 (Theorem 1 and Proposition 2
  of *Metrics and embeddings of generalizations of Thompson's group F*, Trans. AMS 353 (2001)):
  > if f is in F, then the distance from f to the identity is at least (k−2)/3, where k is the
  > common cardinality of the trees in the reduced tree diagram for f.
- *Change of generators* (Moore, Section 2):
  > if Γ′ is any other finite generating set, there is a constant K > 0 such that any set which
  > is ε-Følner with respect to Γ′ is Kε-Følner with respect to Γ.

## Step 1: one level

Fix `k` and assume `H_k`, with data `(∂_k, A_k, c_k)`. Put `q_k = 1 + 8c_k`, since `|Γ| = 4`. Let
`A ⊆ F` be `1/N`-Følner.

1. Lemma 3.15 gives a `Γ`-connected `A' ∋ e`, `1/N`-Følner, with `|A'| ≤ |A|`.
2. Lemma 4.2 gives a weighted `(C/N)`-Følner set `μ` of trees, supported in `{R_f : f ∈ A'}`.
3. Theorem A, items 2 and 3, applied to `(∂_k, A_k)` with `φ = Ack_k` and `m_* ≥ 1`: some
   `R_f` in the support, with `f ∈ A'`, has
   `|R_f| ≥ Ack_k^{(n)}(1) = Ack_{k+1}(n)`, where `n = ⌊log_{q_k}(1 + 8N/C)⌋`.
   This uses that `Ack_k` is nondecreasing.
4. `A'` is `Γ`-connected and contains `e` and `f`, so it contains a path from `e` to `f`. Hence
   `|A'| ≥ d(e,f) + 1 > (|R_f| − 2)/3`, by Burillo–Cleary–Stein.

Therefore
`Føl_{F,Γ}(N) ≥ (Ack_{k+1}(⌊log_{q_k}(1 + 8N/C)⌋) − 2)/3`.

## Step 2: domination

Fix `k ≥ 2`, and write `ℓ(N) = ⌊log_{q_{k+1}}(1 + 8N/C)⌋`. Step 1 at level `k+1`, available
because `H` holds at every level, gives `Føl(N) ≥ (Ack_{k+2}(ℓ(N)) − 2)/3`.

**Two inequalities for `k ≥ 2` and `x ≥ 1`.**
- (i) `Ack_{k+1}(x) ≥ Ack_2(x) = 2^x`. This holds by induction on the level, using
  `Ack_k(y) ≥ 2y ≥ y + 1`.
- (ii) `Ack_k(x+2) ≥ 3Ack_k(x) + 2`.
  - For `k = 2`: `4·2^x ≥ 3·2^x + 2`.
  - For `k ≥ 3`: `Ack_k(x+1) = Ack_{k−1}(Ack_k(x)) ≥ 2^{Ack_k(x)} ≥ 3Ack_k(x) + 2` once
    `Ack_k(x) ≥ 4`, which holds for `x ≥ 2`. The case `x = 1` is checked directly.

**The comparison.**
- `Ack_{k+2}(ℓ) = Ack_{k+1}(Ack_{k+2}(ℓ−1))`.
- Since `k + 2 ≥ 3`, `Ack_{k+2}(ℓ−1) ≥ Ack_3(ℓ−1) = exp_{ℓ−1}(1)`. This is a tower of height
  `ℓ − 1 ≍ log N`, so it is `≥ N + 2` for all large `N`.
- The fact that `2^{ℓ}` is only a fixed power of `N` is why a tower level, and not merely (i),
  is needed here.
- Hence `Ack_{k+2}(ℓ) ≥ Ack_{k+1}(N + 2) ≥ 3Ack_{k+1}(N) + 2`, by (ii) at level `k+1`.
- So `Føl(N) ≥ Ack_{k+1}(N) ≥ Ack_k(N)` for all large `N`.

**Conclusion.** Every primitive recursive function is eventually dominated by some `Ack_k`. This
is the standard fact for this hierarchy: the `Ack_k` are cofinal in the Grzegorczyk classes. So
`Føl_{F,Γ}` eventually dominates every primitive recursive function.

**Other generating sets.** For another finite generating set `Γ′`, a `1/N`-Følner set for `Γ′`
is `K/N`-Følner for `Γ`. So `Føl_{F,Γ′}(N) ≥ Føl_{F,Γ}(⌊N/K⌋)`, which still dominates every
primitive recursive function.

## Step 3: what each prerequisite carries

- **`marginal-derivative-amplification-is-sharp-at-log-height`** (ESTABLISHED). It supplies the
  height `⌊log_q(1 + 8N/C)⌋`, and shows that this height cannot be improved.
- **`thompson-f-trees-carry-an-ackermann-derivative-hierarchy`** (OPEN). It carries all the new
  content.
  - It can fail on its own: a primitive-recursively bounded family of Følner measures on `𝒯`
    refutes it for large `k`.
  - It can fail independently of amenability of `F`: it is a statement about thin sets for the
    partial action on `𝒯`, and holds vacuously if `𝒯` is thin.
- **A single level already gives something new.** `H_k` for one `k ≥ 3` gives
  `Føl(N) ≥ Ack_{k+1}(Ω(log N))`. This is a strict improvement on Moore at the exact point where
  his method provably stops.

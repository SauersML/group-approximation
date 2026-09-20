---
rg: 2
id: fpbs-cs-barrier-hypothesis-fails-finite-free-capacity-normal
kind: claim
title: The nested-barrier hypothesis of Choi-Seo Theorem 2.17 fails on every Cayley graph of a group with an infinite normal subgroup of finite free-subset capacity, which includes every infinite finitely generated virtually nilpotent normal subgroup and every product with an infinite factor containing no free subsemigroup
distinct_from:
  fpbs-cs-set-family-hypothesis-fails-infinite-centre: that kills the set-family hypothesis of Choi-Seo Theorem 2.9 on groups with infinite centre by bounded conjugates; this kills the different nested-barrier hypothesis of Theorem 2.17, by a growth count of twisted coset products, on groups whose normal subgroup may be noncentral (Z^2 x| F_2 with a hyperbolic action) or nonamenable (B(m,n) x B(m',n')).
  fpbs-sc-choi-seo: that is Choi-Seo's positive theorem for acylindrically hyperbolic groups; this is an obstruction showing their Theorem 2.17 hypothesis is false, not merely unproved, on a class disjoint from the acylindrically hyperbolic one, and it proves nothing about the thresholds.
  fpbs-product-every-generating-set: that is the open target p_c < p_u for direct products; this shows one proof method cannot reach the products H x K with K containing an infinite finitely generated subgroup and no free subsemigroup, and leaves the target open.
artifacts:
  - research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md
  - experiments/fpbs-free-capacity-barrier-2026-09-17/check_free_capacity.py
  - experiments/fpbs-free-capacity-barrier-2026-09-17/output.txt
---

**ESTABLISHED.** Proof route:
`fpbs-cs-barrier-fails-finite-free-capacity-normal-proof`.

**The invariant.** For a subset `X` of a group, call a finite `Y ⊆ X` *free*
if for every `k >= 1`, distinct length-`k` sequences from `Y` (repetitions
allowed) have distinct products. The *free-subset capacity* is

```text
b(X) = sup { #Y : Y ⊆ X finite and free }  ∈ {0, 1, 2, ..., ∞}.
```

Choi–Seo's Definition 2.13(2) says exactly that every finite subset of `B'` is
free. So `#(B' ∩ X) <= b(X)` for every `X` and every roughly-branching witness
`B'`.

**Theorem.** Let `G` be finitely generated and `K ◁ G` a normal subgroup that
contains an infinite finitely generated subgroup `K_0`. Suppose `b(Kt) < ∞`
for every coset `Kt`. Then for every finite generating set `S`, the hypothesis
of Choi–Seo arXiv:2508.08932v2 Theorem 2.17 fails on `Cay(G,S)`. This covers
every choice of `r`, of `S_D, G_(D,E), H_D` meeting its conditions (1)–(3), and
of the constants `N(ε,D,E)`.

**Sufficient conditions for `b(Kt) < ∞` for every `t`** (all proved in the
route):

* **(a) `K` is finitely generated, infinite and virtually nilpotent.** Let `d`
  be its growth degree and `L_t = max_τ |t τ t^(-1)|_K`, taken over a finite
  generating set of `K`. Then `b(Kt) <= L_t^d`. This covers
  - `Z^d x| Q` for any action and any nonamenable `Q`, for example
    `Z^2 x| SL(2,Z)` and `Z^2 x| F_2` with a hyperbolic generator;
  - Heisenberg-by-free groups;
  - every group with an infinite finitely generated virtually nilpotent normal
    subgroup.
* **(b) `G = K · C_G(K)`** (every `t` acts on `K` as an inner automorphism),
  **and `K` has no free subsemigroup of rank 2.** Then `b(Kt) = 1`. This covers
  `H x K` for arbitrary `H`, when `K` is any group containing an infinite
  finitely generated subgroup and no free subsemigroup. Examples of such `K`:
  infinite torsion groups (Grigorchuk groups, free Burnside groups `B(m,n)`,
  Tarski monsters), groups of intermediate or polynomial growth, and every
  virtually nilpotent group.

**Consequences for the frontier.**

1. The Theorem 2.17 half of Choi–Seo's method cannot reach the two known
   explicit families of `fpbs-residual-price-one-non-ah-class-nonuniqueness`
   (`fpbs-residual-class-has-torsion-products`), namely `B(m,n) x B(m',n')`
   and `T x T'`. Here `K` is a torsion factor, which is nonamenable in the
   Burnside case.
2. Nor can it reach `Z^2 x| F_2`, `Z^2 x| SL(2,Z)` or Heisenberg-by-free
   groups, which lie in `fpbs-amenable-wq-normal-class-nonuniqueness`. This
   extends the wave-19 normal-cyclic obstruction, where `b(Zt) = 1` by
   commutation or inversion, to noncentral normal subgroups of higher rank.
   There `b(Kt)` can exceed 1. In `Z^2 x|_M Z` with `M = [[2,1],[1,1]]`, the
   route proves `b(Z^2 t) = 2` exactly. Pairs are free, since height-one
   polynomials have no root above 2 while the leading eigenvalue is
   `(3+√5)/2 > 2`. Triples are not free, since `3` exceeds the Mahler measure
   `(3+√5)/2`. The one-line core lemma of wave 19 is therefore false here, and
   only the counting form survives.

**Calibration (where the invariant stops).** If `K` contains a free
subsemigroup `⟨x,y⟩^+`, then `{x y^i : i < n}` is a free subset of `K` for
every `n`, because it is a prefix code. So `b(K) = ∞`, and the counting
obstruction says nothing. This happens for `F_2 x F_2`, `F_2 x BS(1,2)`, and
every `H x K` with `K` containing a free subsemigroup. These groups, together
with normal subgroups that have no infinite finitely generated subgroup (the
lamplighter bases `⊕ Z/2`), are the gate where Theorem 2.17 might still work
beyond acylindrical hyperbolicity. For an elementary amenable finitely
generated `K`, having no free subsemigroup is equivalent to being virtually
nilpotent (Chou 1980, Rosenblatt 1974). So among elementary amenable normal
subgroups under condition (b), the gate is exactly the non-virtually-nilpotent
ones.

**Scope.** The claim is about the hypothesis of Theorem 2.17 only. It says
nothing about Theorem 2.9 (the set-family hypothesis) outside the infinite-centre
case, and nothing about `p_c` or `p_u`.

Definition 2.13(2) is read as in the wave-19 obstruction, with sequences
allowed to repeat entries; that is the literal statement. If it were read as
constraining only repetition-free sequences, the counting would break down,
because `k` could then not exceed `#Y`.

## Attempts

* **Generalize the normal-cyclic core lemma by counting.** Done. See the
  route.

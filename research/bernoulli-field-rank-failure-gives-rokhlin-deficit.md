---
rg: 2
id: bernoulli-field-rank-failure-gives-rokhlin-deficit
kind: claim
title: A rank-condition failure over a Bernoulli rational function field skew group ring is a Bernoulli Rokhlin entropy deficit, so maximal Bernoulli entropy forces stably finite Bernoulli-field skew rings
distinct_from:
  twisted-linear-profile-deficits-are-rank-condition-failures: that turns a rank-condition failure of any field crossed product into non-equivariant entropy profiles, which only defeat profile-level proofs; this turns a failure over a Bernoulli field into an equivariant generating partition of a Bernoulli shift, an actual Rokhlin deficit.
  rational-function-field-crossed-products-have-the-rank-condition: that proves the rank condition for finitely many variables by counting points of F_q^n; this handles the shift on infinitely many variables, where no finite point set is invariant, and gets a conditional conclusion through Rokhlin entropy instead of a count.
  sofic-lamplighter-bernoulli-crossed-products-have-rank-models: that builds rank models from sofic approximations for locally constant coefficients; this uses no approximation of the group, and for sofic groups recovers stable finiteness of rational-coefficient Bernoulli skew rings from Seward's sofic case.
  seward-per-group-rokhlin-entropy-of-bernoulli-shifts: that imports INF implies Kaplansky direct finiteness; this factors that implication through stable finiteness of Bernoulli-field skew group rings, which contain the group algebra.
artifacts:
  - research/artifacts/bernoulli-field-point-model-rokhlin-deficit-2026-09-17.md
---

**ESTABLISHED (unreviewed)** by [[bernoulli-field-rank-failure-gives-rokhlin-deficit-proof]].

Let `G` be countably infinite, `k` a field, `m >= 1`, and `K_m(k) = k(x_{g,i} : g ∈ G, i <= m)` with the shift
`σ_h(x_{g,i}) = x_{hg,i}`. Write `⋊` for the skew group ring with trivial cocycle.

**Theorem.** If some `G`-invariant subfield `K_0 ⊆ K_m(k)` has `A ∈ M_{d×r}(K_0 ⋊ G)`, `B ∈ M_{r×d}(K_0 ⋊ G)`
with `AB = I_d` and `r < d`, then for some finite field `F_q`,

    h^Rok_G((F_q^{m+d})^G) <= (m + r) log q + h_2(C/q) + (Cd/q) log q  <  (m + d) log q,

with `C` the total degree of the denominators involved. Hence `h_sup(G) < ∞`, that is, **not INF(G)**.

**Corollary.** INF(G) implies, for every field `k` and `m >= 1`, that `K_m(k) ⋊ G` is stably finite. So all its
unital subrings are stably finite, including every invariant-subfield skew ring and `k[G]`. The decomposition is

    INF(G)  ⇒  SF(Bernoulli-field skew rings over G)  ⇒  KAP(G).

Each arrow can fail on its own. Unconditionally, Bernoulli-field skew rings over sofic groups are stably finite.

**Mechanism.**
1. Specialize coefficients to a finite field (Nullstellensatz), keeping denominators nonzero.
2. Evaluate the Bernoulli variables at iid uniform points of `F_q`. Each crossed-product matrix becomes a
   shift-equivariant local operator on configurations.
3. `π_ω(A)π_ω(B) = id` except at sites whose window meets a denominator zero, which have density `<= C/q` by
   Schwartz–Zippel.
4. Label each site with the point, the `r` output symbols of `π_ω(B)ξ`, and `ξ` itself only at defect sites. This
   is a generating partition of the Bernoulli shift with base `F_q^{m+d}`. The point coordinates cost `m log q` on
   both sides, so the saving `(d - r) log q` survives.

**Impact.**
- Bernoulli fields were a surviving regime for `some-field-crossed-product-fails-the-rank-condition`. A witness
  there refutes INF at its group. Over the tester host `U = L_(F_2)(1,2)^×`, it refutes the flagship
  `bernoulli-rokhlin-entropy-maximal-for-every-group`.
- A proof of the flagship must prove this random-coefficient Kaplansky statement for every group in every
  characteristic `p`.

**Where it stops.**
- Nontrivial cocycles: `π_ω` is not multiplicative.
- Non-Bernoulli invariant fields: these need an invariant point measure with small defect, plus relative Rokhlin
  maximality.
- The converse direction is unknown. See artifact Section 5.

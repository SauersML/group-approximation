---
rg: 2
id: pair-constraint-graph-criterion
kind: claim
title: Two-point label data is a component condition, and short kernel transporters forbid it
distinct_from:
  two-point-orbit-approximation: that asserts the existence of approximations for the marked Kun--Thom pair; this is a model-free equivalence criterion — labels exist iff the two slots lie in distinct components of a constraint graph — valid for every pair, every model and every window, and asserting no existence.
  hilbert-embeddable-length-lp-feasibility: that decides the existence of a witnessing length by a linear program over class functions; this decides the existence of two-point label data by graph components, with no characters, lengths or cones anywhere in it.
  coordinate-action-not-sofic: that refutes full-window equivariant charts by Kun--Thom rigidity; this is neutral bookkeeping that converts the one-pair label question into a cycle-structure question, refuting nothing by itself.
---

Let `X` be a `G`-set, `p ≠ q ∈ X`, `F ⊆ G` finite, and let a **model** be a
finite set `A` with any map `φ : G → Sym(A)`.  Define the **pair-constraint
graph** `𝒢 = 𝒢(A, φ, F)` on the vertex set `A × {p,q}`: for every `s ∈ A`,
`g ∈ F` and `x ∈ {p,q}` with `g⁻¹·x ∈ {p,q}`, an edge

```text
(s, g⁻¹·x)  —  (φ(g)·s, x).
```

Call a word `(g_1,ε_1),…,(g_k,ε_k)` with `g_i ∈ F`, `ε_i = ±1`
**slot-admissible from `x`** if the slot trajectory `x_0 = x`,
`x_i = g_i^{ε_i}·x_{i-1}` stays in `{p,q}`; its **value** is
`v = g_k^{ε_k}⋯g_1^{ε_1}` and its **traversal permutation** is
`σ = φ(g_k)^{ε_k}∘⋯∘φ(g_1)^{ε_1}`.

1. **Labels are components.**  For `S ⊆ A`, label data
   `j_s : {p,q} → B` (`s ∈ S`, `B` finite) satisfying the distinctness and
   equivariance clauses of `two-point-orbit-approximation` exists **iff**
   for every `s ∈ S` the vertices `(s,p)` and `(s,q)` lie in distinct
   connected components of `𝒢` restricted to `S × {p,q}`.

2. **Paths are transporter words.**  `(s,x)` and `(s',x')` lie in the same
   component of `𝒢` restricted to `S × {p,q}` iff some slot-admissible word
   from `x` has value `v` with `v·x = x'`, traversal permutation `σ` with
   `σ(s) = s'`, and all intermediate points of the traversal inside `S`.

3. **Deletion bound.**  Suppose `φ` is a homomorphism and the `φ`-action on
   `A` is free.  If some slot-admissible word from `p` of length `k` has
   value `v` with `v·p = q` and `φ(v) = id_A` — for `A = Q` regular under a
   finite quotient `π : G → Q`, exactly: `v ∈ ker π` and `v·p = q` — then
   **every** admissible `S` has `|S| ≤ ((k-1)/k)·|A|`.  Consequently
   two-point data at precision `ε` on such a model requires every
   slot-admissible word valued in

   ```text
   ker π ∩ T_{p→q},      T_{p→q} := { v ∈ G : v·p = q },
   ```

   to have length `k ≥ 1/ε`: a **transporter-girth condition** on the
   quotient, relative to the window.

For approximate models the criterion is unchanged (items 1 and 2 never used
multiplicativity); only item 3's identification of the traversal permutation
with `φ(v)` degrades, by at most `k` normalized-Hamming defects.  The
content of item 3 is that exact models cannot buy the labels by exactness:
if the quotient has a short kernel transporter, no choice of deleted set
saves it, and the only lever left is depth of the quotient — which is what
`congruence-transporter-girth` measures for the Kun--Thom pair.

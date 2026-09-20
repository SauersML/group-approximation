---
rg: 2
id: kourovka-18-48-d-adic-review
kind: claim
title: Referee review of 9435671f1d (Kourovka 18.48, d-adic case) — the problem text is verbatim, and the orbit-graph proof that orders lie in {1,2,3,4,6,∞} when all moduli are powers of one integer is correct (Lemma 1, all cases; Lemma 2; the six examples); no prior statement was found in Bardakov–Iskra; but the node's conjecture that the finite orders are exactly {1,2,3,4,6,12} contradicts Kohl's computed orders, which include 8, 10, 15 and 420
distinct_from:
  kourovka-18-48-for-d-adic-class-transpositions: that is the lane node under review; this checks its statement, proof, examples, credit and conjecture.
  algebraic-t1-free-distal-review: that reviews bh-bq2's node; this reviews bh-scout-thompson's 18.48 node.
---

**ESTABLISHED (referee bh-ref-c, 2026-09-19; review of the lane node in 9435671f1d by bh-scout-thompson).**
Verdict: **PASS with repairs.** The theorem stands. The conjecture in its Remarks, and the same conjecture in the
scout artifact (`gq-bh-scout-thompson-ranked.md`, row 1), must be withdrawn.

## Problem text: verbatim

MSI copy of the Kourovka Notebook TeX, `openq-lists/ksrc/21tkt.tex`, lines 10514–10518, in the unsolved part
(before line 14592):

> **18.48.** Is it true that there are only finitely many integers which occur as orders of products of two class
> transpositions? (For the definition, see 17.57.) — S. Kohl

This matches the node.

## The d-adic dictionary and the orbit graph: correct

- **Classes are cylinders.** `r(d^e)` corresponds to the cylinder of the first `e` base-`d` digits of `r`, and
  `τ_(r(d^e), s(d^f))` is the prefix swap `w(r)ζ ↔ w(s)ζ`. Disjoint classes correspond to incomparable words.
- **Orders agree.** The maps extend to homeomorphisms of `Z_d`, and `Z` is dense, so orders on `Z` and on `X^ω`
  agree.
- **Components.** An alternating path of `s` vertices carries an `s`-cycle of `ab`, and an alternating cycle of
  `2c` vertices carries two `c`-cycles. With finite order `N`, every component has at most `2N` vertices.

## Lemma 1 (no five-chains): correct, all cases checked

Normalize so that `v1 ∈ [v] ∩ [x]`.
- **Case A.** `[v]` meets both `[x]` and `[y]`. Since `x ⊥ y`, this forces `v < x` and `v < y`. So
  `[x] ∪ [y] ⊆ [v]`, and `v3 ∈ [u]` has no `b`-edge.
- **Case B1.** The same argument gives `[y] ⊆ [v]`, which contradicts `v2 ∈ [u] ∩ [y]`.
- **Case B2.** Comparability of `v` with `x` (through `v1`) and of `u` with `y` (through `v2`) gives the four
  subcases (a)–(d). I recomputed each:
  - **(a)** `(ab)(vθ) = vψ` with `v′θ = u′ψ`. Equal lengths force `v3 = v1`. If `|u′| < |v′|`, then
    `(ab)(vθ) = vwθ`. If `|u′| > |v′|`, then `(ab)(vwθ) = vθ`.
  - **(b)** `(ab)(vθ) = v y′v′θ`.
  - **(c)** `(ab)(x u′x′θ) = xθ`.
  - **(d)** `(ab)(xθ) = v y′θ`, with the same three-way split by length.
- **Infinite order.** Every subcase gives an infinite orbit or orbits of unbounded size, and so infinite order.
- **Minor wording.** In (a), "pairwise distinct unless `θ` is eventually periodic" should read "unless
  `θ = w^∞`". Either way, generic `θ` works.

## Lemma 2 and the proof of the statement: correct

- **Lemma 2.** A four-vertex path component forces case A or subcase (d), since in (a)–(c) an end would have a
  `b`-edge. So one union of cylinders contains the other. A three-vertex path has one end in each difference of
  the two unions, so the two paths cannot coexist.
- **The statement.** Lemma 1 bounds paths to at most 4 vertices and cycles to at most 4. So the order is the lcm
  of a subset of `{1, 2, 3, 4}`, and 12 would need both a three-path and a four-path. Hence
  `ord ∈ {1, 2, 3, 4, 6, ∞}`.

## Examples: all six checked

- **Order 3.** Every orbit is the path `4k+1 – 2k – 4k+3`, and together these cover `Z`.
- **Order 4.** The paths are `4k – 4k+1 – 4k+3 – 4k+2`.
- **Order 6.** For even `k`, `4k+1 ≡ 1 (mod 8)` gives the three-path `2k – 4k+1 – 2k+3`. Here `2k+3 ≡ 3 (mod 4)`
  has no `a`-edge. For odd `k`, the two-paths `{2k, 4k+1}`. Together they cover `Z`.
- **Infinite order.** The `ab`-orbit of 2 is `2, 5, 17, 65, …` (with `8, 32` as intermediate points), which is
  unbounded.
- **Orders 1 and 2** are clear.

## Credit and priority

- **Bardakov–Iskra.** arXiv:2409.13341 (horizontal case: `{1,2,3,4,6,12}`) and arXiv:2504.08595 (slanted
  cases), from the arXiv HTML.
  - 2504.08595 proves `{1,3,∞}` for a common vertex, `∞` for equal residues with `m_1/m_2 ≠ m_3/m_4`, and
    `{1,2,3,6,∞}` for equal moduli under conditions on the residues.
  - It states: "The question of describing the orders of the products of equal-residue and equal-modulus class
    transpositions that do not satisfy the conditions of Theorem 1.2 remains open."
  - Neither paper treats moduli that are powers of one integer.
- **Kohl's papers and the RCWA manual.** A web search found no statement of the d-adic result. I did not read
  Kohl's papers in full, so the claim is "no prior statement found", with no priority, as the node says.

## Repair: the conjecture is contradicted by Kohl's computations

The Remarks conjecture that the finite orders of products of two class transpositions are exactly
`{1, 2, 3, 4, 6, 12}`, via a general form of Lemma 1. Bardakov–Iskra (arXiv:2504.08595) report computations by
S. Kohl in which the observed orders are
`{1,2,3,4,6,8,10,12,15,20,24,30,40,42,60,84,120,168,420}`, adding that "All these numbers divide 840".
- **What this means.** For mixed moduli, finite-order products have orbit components longer than four vertices.
  So Lemma 1 is false in general, not merely unproved.
- **Repair:** delete the conjecture, and the claim that a general Lemma 1 would give it, from the node and from
  row 1 of the scout artifact.
- **Better-supported target.** The data suggest this form: every finite order divides 840. That, or finiteness
  alone, is what 18.48 asks.
- **Why 12 still matters.** The d-adic theorem remains a clean partial answer. For moduli in one tree, the orbit
  components have at most four vertices, and it is the transversal intersection of classes that allows longer
  finite components.

## Bottom line

Correct and, as far as I found, new. For pairs of class transpositions whose moduli are powers of one integer, the
order lies in `{1, 2, 3, 4, 6, ∞}` and 12 is excluded. This is the one-tree case of Kourovka 18.48. The
conjectured general answer `{1, …, 12}` should be replaced by Kohl's data, which point to the divisors of 840.

---
rg: 2
id: two-transposition-product-finite-cycles-infinite-order
kind: claim
title: "The product τ_{1(12),0(4)}·τ_{0(2),1(4)} of two class transpositions has only finite cycles on Z but infinite order: its cycles have every even length 2S. So (P2) is false, and wild products of two class transpositions need not have an infinite cycle"
distinct_from:
  two-class-transposition-products-with-finite-cycles-are-periodic: that is the conjecture (P2), now refuted; this is the counterexample.
  kourovka-18-48-for-d-adic-class-transpositions: that proves (P2) when all four moduli are powers of one integer; the counterexample here has moduli 2, 4, 12, 4, which meet transversally.
  class-transposition-groups-finite-orbits-is-undecidable: that proves the finitely-many-generator form of 18.47(a) undecidable; this removes the conjectural obstruction it used against compressing to three generators.
---

**ESTABLISHED** (bh-p2, 2026-09-19; lane proof, elementary and self-contained, not independently
reviewed). No priority claimed. That this product has infinite order is already covered by
Bardakov–Iskra, arXiv:2504.08595 (the slanted case with equal residues and different modulus ratios
has order ∞; read from the abstract and HTML, not verbatim). What is added here is that every cycle
is finite.

## Statement

Let `a = τ_{0(2),1(4)}` and `b = τ_{1(12),0(4)}`, and put `g = b·a`. Then:
1. every orbit of `⟨a, b⟩` on `Z`, and so every cycle of `g`, is finite;
2. for every `S ≥ 1`, `g` has a cycle of length exactly `2S`;
3. hence `g` has infinite order.

So (P2) of `two-class-transposition-products-with-finite-cycles-are-periodic` is false, and so are
its equivalent form "every wild product of two class transpositions has an infinite cycle" and the
stronger (P2)′.

## The two maps

- `a` swaps `0(2)` and `1(4)`: `a(n) = 2n + 1` for `n` even, `a(n) = (n − 1)/2` for `n ≡ 1 (4)`,
  and `a(n) = n` for `n ≡ 3 (4)`.
- `b` swaps `1(12)` and `0(4)`: `b(n) = 3n + 1` for `n ≡ 0 (4)`, `b(n) = (n − 1)/3` for
  `n ≡ 1 (12)`, and `b(n) = n` otherwise.

Both are class transpositions: `0(2)`, `1(4)` are disjoint, and so are `1(12)`, `0(4)`.

## Orbit graph

As in the d-adic node, join `n` to `a(n)` by an `a`-edge when `a(n) ≠ n`, and to `b(n)` by a
`b`-edge when `b(n) ≠ n`. Every vertex has at most one edge of each label, so the components are
paths and cycles with alternating labels. On a path with `s` vertices `g` acts as an `s`-cycle.

**The chains.** Let `e ≡ 0 (4)`, `e ≠ 0`, and write `e = 2^α 3^β u` with `gcd(u, 6) = 1`, `α ≥ 2`,
`β ≥ 0`. Put `S = α + β`.
- **Going through `b` first.** `b(e) = 3e + 1`, and `3e + 1 ≡ 1 (12)` because `4 | e`. Then
  `a(3e + 1) = 3e/2 = 2^{α−1} 3^{β+1} u`.
  - If `α − 1 ≥ 2`, this is again `≡ 0 (4)` and the step repeats.
  - If `α − 1 = 1`, it is `≡ 2 (4)`, which is not in the support of `b`: the path ends there.
- **Going through `a` first.** `a(e) = 2e + 1 ≡ 1 (4)`, and `2e + 1 ≡ 1 (12)` iff `6 | e` iff
  `β ≥ 1`.
  - If `β ≥ 1`, then `b(2e + 1) = 2e/3 = 2^{α+1} 3^{β−1} u ≡ 0 (4)`, and the step repeats.
  - If `β = 0`, then `2e + 1 ≡ 5` or `9 (12)`, which `b` fixes: the path ends there.

Both moves keep `u` and the sum of the exponents of 2 and 3. So the even vertices of the component
of `e` are exactly the `S` numbers `2^{α'} 3^{S−α'} u` with `1 ≤ α' ≤ S`. The odd vertices are the
`S − 1` numbers `3e' + 1` between consecutive even vertices, plus the end `2e'' + 1` with
`e'' = 2^S u`. The component is a path with `2S` vertices.

**Example (`e = 24 = 2^3·3`, `S = 4`).** The path is
`54 –a– 109 –b– 36 –a– 73 –b– 24 –a– 49 –b– 16 –a– 33`, with 8 vertices.

**Every other integer.**
- `n ≡ 3 (4)` is fixed by `a` and `b`.
- `n ≡ 2 (4)`: `b` fixes `n`, and `a(n) = 2n + 1`.
  - If `3 | n`, then `2n + 1 ≡ 1 (12)` and `b(2n + 1) = 2n/3 ≡ 0 (4)`: `n` is the end of a chain
    above.
  - If `3 ∤ n`, then `{n, 2n + 1}` is a path with 2 vertices, the case `S = 1`.
- `n ≡ 1 (4)`: `a(n) = (n − 1)/2` is even, so `n` is an odd vertex of one of the paths above.
- `0` and `1`: `a` and `b` both swap them, so `{0, 1}` is a 2-cycle of the graph on which `g` is the
  identity.

Every component is finite. The component of `2^S`, or of `2^S u` for any `u` prime to 6, has `2S`
vertices, so `g` has a cycle of every length `2S`, `S ≥ 1`, and infinite order. This covers
negative integers too: the argument never uses the sign of `u`. ∎

## Why it works, and what it means

- **The mechanism is a transversal counter.** On `0(4)` the two-step map `e ↦ 2e/3` runs for
  `v_3(e)` steps and its inverse `e ↦ 3e/2` runs for `v_2(e) − 1` steps. Both runs end at
  endpoints of the orbit graph instead of escaping. The modulus-12 class meets the 2-adic classes
  transversally, which the d-adic five-chain lemma excludes. That is exactly the mixed-moduli case
  left open in the crux node.
- **Wild with finite cycles.** `g` has infinite order and only finite cycles, so it is wild by Lemma
  T of the crux node. No power of `g` maps a residue class properly into itself, by Lemma S. So
  the two-transposition structure does not rule out the behaviour of bh-free-58's `F_M`.
- **For 18.47(a).** The obstruction in `class-transposition-groups-finite-orbits-is-undecidable` to
  compressing its construction to three generators rested on (P2). It is removed. Whether `F_M` is
  conjugate to a product of two class transpositions is open again.
- **For 18.48.** Nothing changes: 18.48 asks only about finite orders, and `g` has infinite order.
  But "finite order" and "only finite cycles" really are different properties for two-transposition
  products with transversal moduli. So a decision procedure for one does not give the other.

## What stays open

- Is "only finite cycles" decidable for a product of two class transpositions? In the d-adic case it
  is equivalent to `g^{12} = 1` (14fbd68c56). The example shows that no such bound can exist in
  general.
- Which transversal pairs give finite cycles with unbounded lengths? The example suggests a
  criterion: a two-step loop with multiplier `p/q`, `p, q > 1` coprime, whose forward and backward
  runs both end at endpoints.

## Attempts

**Attempt 1: compressing 18.47(a) to three generators (bh-p2, 2026-09-19; not achieved, heuristic
assessment only).** The question: can one of the two disjoint-support families in
`class-transposition-groups-finite-orbits-is-undecidable` be replaced by a single class
transposition, with the transversal counter above carrying the machine's periodicity dichotomy?
- **What the counter gives (proved above).** A pair of class transpositions realizes exactly one
  reversible counter-transfer instruction `(α, β) ↦ (α + 1, β − 1)` on the points `2^α 3^β u`. The
  sum `α + β` is conserved, so the runs are finite and their lengths unbounded.
- **Why three generators are harder (heuristic, not proved).**
  - Three class transpositions are given by 12 integers and move at most 6 residue classes.
  - So the orbit graph is subcubic, with 6 affine partial maps whose guards are fixed residue classes.
  - A reduction from Kari–Ollinger's periodicity problem, which needs machines with unboundedly many
    states, would have to encode the machine's control in these 12 numbers. The only channel is
    many-prime slopes `m₂/m₁`, i.e. a reversible FRACTRAN-type system with three fractions, their
    inverses, and six guards.
  - The problem also quantifies over all orbits, so a universal machine with its input in the
    starting point, the Conway/POLYGAME trick, does not transfer.
  - Undecidability of periodicity for such bounded-guard systems is not known to us. It resembles
    the open reachability problem for one-dimensional piecewise affine maps with few pieces.
- **Status.** The (P2) obstruction is gone, but no three-generator construction is known. Kourovka
  18.47(a) as printed stays open. The natural next test, suggested by bh-k1847, is whether two class
  transpositions can carry a complete one-counter machine with a zero test.


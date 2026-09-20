---
rg: 2
id: lifted-thompson-t-chromatic-codes-force-t-nonhyperlinear-proof
kind: route
title: Adding relators only shrinks area, translation numbers keep commutators off the centre, and pigeonhole over a finite Hilbert--Schmidt net kills the mark
target: lifted-thompson-t-chromatic-codes-force-t-nonhyperlinear
requires:
  - lifted-thompson-t-quotients-are-rotation-centralizers
---

**Imported facts.**
- (τ) Poincaré translation number on the group of lifts, as quoted in
  `lifted-thompson-t-quotients-are-rotation-centralizers-proof`.  It is
  conjugation invariant, and `τ(z^n g) = τ(g) + n` for central `z`.
- (dBE) de Bruijn--Erdős: if every finite subgraph of `G` has chromatic
  number at most `N`, then so does `G`.  Only the following consequence is
  used: a graph with `chi = infinity` has, for every `N`, a finite subgraph
  with `chi > N`.
- (HL) A finitely presented group `Gamma = ⟨S|R⟩` is hyperlinear iff for
  every word `x != 1` in `Gamma` there are `c > 0` and maps
  `phi_n : S -> U(k_n)` such that:
  - `max_{r in R} ||r(phi_n) - 1||_2 -> 0`;
  - `||x(phi_n) - 1||_2 >= c`.

  Here `||A||_2 = (tr_{k}(A^*A))^{1/2}` with normalized trace.  This is the
  standard finite-presentation form of embeddability in `R^omega`: compose
  an embedding with lifts of the generators.  The value `c` can be taken to
  be any number below `sqrt 2`.
- Sofic groups are hyperlinear, and subgroups of sofic groups are sofic.

## Step 1. Descent of the code

Adding relators never increases area:

```text
Area_{R ∪ {z^(2^k)}}(w) <= Area_R(w)   for every word w.
```

A van Kampen diagram over `R` is one over `R ∪ {z^(2^k)}`.  So the words
`c_v, h_v, a_v, x` satisfy (CCC1) and (CCC2) in `Q_k` with the same
constants `A_Delta` and `A_0`.

## Step 2. The mark is not central

We show that for any code with `x != 1` in `T̄`, the element `x` does not lie in
`⟨z⟩`.
- Pick a vertex `v`.  By (CCC1), in `T̄`
  ```text
  x = a_v^(-1) [c_v, h_v] a_v = [f, g],   f = a_v^(-1) c_v a_v,  g = a_v^(-1) h_v a_v.
  ```
- Suppose `[f,g] = z^n`.  Then `f g f^(-1) = z^n g`.  Apply (τ):
  ```text
  τ(g) = τ(f g f^(-1)) = τ(z^n g) = τ(g) + n.
  ```
  So `n = 0`.
- Hence a commutator lying in `⟨z⟩` is trivial.  Since `x != 1`, `x` is not
  in `⟨z⟩`.  In particular `x` is not in `⟨z^(2^k)⟩ = ker(T̄ -> Q_k)`, so the
  image of `x` in `Q_k` is nontrivial.

Steps 1 and 2 prove item 1.

## Step 3. The Hilbert--Schmidt criterion

Let `Gamma = ⟨S|R⟩` carry a code with mark `x != 1`.  Suppose, for
contradiction, that `Gamma` is hyperlinear.  Take `c` and `phi_n` from
(HL).  Write `d(A,B) = ||A-B||_2` on `U(k_n)`.  This metric is bi-invariant,
because `||UAV||_2 = ||A||_2` for unitaries `U, V`.  Put
`eps_n = max_r d(r(phi_n), 1)`, so `eps_n -> 0`.

**(a) Word defect is at most area times defect.**
- If `Area_R(w) <= A`, then `w` equals, freely, a product
  `∏_{i<=A} g_i r_i^{±1} g_i^(-1)`.
- By the triangle inequality and bi-invariance,
  ```text
  d(w(phi_n), 1) <= Σ_i d(r_i(phi_n)^{±1}, 1) <= A eps_n.
  ```
- Free equality is exact in `U(k_n)`.

**(b) Commutators are Lipschitz in the first variable.**  For unitaries
`c, c', h`:
```text
d([c,h], [c',h]) = d(c h c^(-1) h^(-1), c' h c'^(-1) h^(-1))
                 <= d(c h c^(-1), c' h c^(-1)) + d(c' h c^(-1), c' h c'^(-1))
                  = d(c, c') + d(c^(-1), c'^(-1)) = 2 d(c, c').
```

**(c) Pigeonhole.**
- Fix `delta > 0` and `n`.
- `U(k_n)` is compact, so it is covered by finitely many sets `B_1, ..., B_N`
  of `d`-diameter less than `delta`.
- By (dBE), `G` has a finite subgraph `G'` with `chi(G') > N`.
- Colour each vertex `v` of `G'` by an index `j` with `c_v(phi_n) in B_j`.
  This is not a proper colouring, so some edge `(v,w)` of `G'` has
  `d(c_v(phi_n), c_w(phi_n)) < delta`.
- Write `U_y = y(phi_n)`.  Then:
  - by (a) and (CCC1), `d([U_{c_v}, U_{h_v}], U_{a_v} U_x U_{a_v}^(-1)) <= A_Delta eps_n`;
  - by (a) and (CCC2), `d([U_{c_w}, U_{h_v}], 1) <= A_0 eps_n`;
  - by (b), `d([U_{c_v}, U_{h_v}], [U_{c_w}, U_{h_v}]) < 2 delta`.
- By bi-invariance, `d(U_x, 1) = d(U_{a_v} U_x U_{a_v}^(-1), 1)`.  Hence
  ```text
  d(x(phi_n), 1) < (A_Delta + A_0) eps_n + 2 delta.
  ```

**(d) Conclusion.**
- The number `delta` was arbitrary, so `d(x(phi_n),1) <= (A_Delta+A_0) eps_n`.
- This tends to `0`, which contradicts `d(x(phi_n),1) >= c`.
- So `Gamma` is not hyperlinear, and therefore not sofic.  This proves item 2.
- The same argument works verbatim for any compact groups with a
  bi-invariant metric, since (a)--(c) used nothing else.  One example is
  `Sym(k)` with the normalized Hamming distance.

## Step 4. Item 3

Let `T̄` carry a code with mark `x != 1`.
- By item 1, each `Q_k` carries a code with nontrivial mark.  Each `Q_k` is
  finitely presented, by `R ∪ {z^(2^k)}`.
- By item 2, each `Q_k` is not hyperlinear.  This covers `Q_0 = T` and
  `Q_k ≅ C_T(r_k)`.
- `T <= V <= 2V`, and subgroups of sofic groups are sofic.  So neither `V`
  nor `2V` is sofic.
- The contrapositive statements are the same implications read backwards.
  For codes in `T` itself, apply item 2 with `Gamma = T` directly. ∎

## Remark on sharpness

Step 1 goes one way only.  A code in `T` gives `Rad_MF(T) = T` by
`infinite-chromatic-commutator-code-kills-mf-mark`, but not a code in `T̄`.
Lifting it requires a lift of every relator diagram in which the central
`z`-letters cancel.  So the cost computed here is a lower bound on the
strength of `T̄`-codes, not an equivalence.

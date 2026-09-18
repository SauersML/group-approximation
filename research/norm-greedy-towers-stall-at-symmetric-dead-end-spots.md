---
rg: 2
id: norm-greedy-towers-stall-at-symmetric-dead-end-spots
kind: claim
title: A level of the norm-margin greedy tower that contains a pattern symmetric on a rim spot at a Cayley dead end stalls forever, while the translation-coherent asymmetry clause makes such self-killing patterns impossible
distinct_from:
  greedy-maximal-margin-towers-never-stall: that is the OPEN existence statement (G) that some data never stall; this is an ESTABLISHED sufficient condition for a stall of the same recursion, stated through dead-end depth of the generating set, together with a coherence lemma for a modified asymmetry clause.
  translation-coherent-greedy-margin-towers-never-stall: that is the OPEN statement (G_geo) for the modified recursion; this proves that the dead-end mechanism below cannot occur in (G_geo), and does not prove (G_geo).
  covering-towers-iff-effective-minimal-free-subshifts: that characterises (M2) by margin covering towers; this concerns one canonical recursion producing such towers and one way it breaks.
---

**ESTABLISHED** (route `norm-greedy-towers-stall-at-symmetric-dead-end-spots-proof`,
elementary, agent-verified only).

**Setting.** As in `greedy-maximal-margin-towers-never-stall`: a group `Λ`
with a finite generating set and solvable word problem, data `(A, R)`,
`m_n = n`, and the greedy recursion `L_{n+1} = F_n(R_{n+1})` with clauses (C),
(K), (A). For `s ≠ 1` and `x ∈ Λ` put

`Q_x(s) = B(R(s)) x ∪ B(R(s)) s x`,

the set of points that the asymmetry test `(s, x)` reads. Call `y` a **right
dead end of depth `k`** if `|yw| ≤ |y|` for every `|w| ≤ k` (depth `0` is
every element).

**Theorem 1 (dead-end stall).** Let `n ≥ 1`. Suppose there are `p ∈ L_n`,
`s ≠ 1`, `y ∈ Λ` and `k ≥ 0` with:
1. `Q_y(s) ⊆ B(R_n)`;
2. `p(μy) = p(μsy)` for every `μ ∈ B(R(s))` (`p` is `s`-symmetric at `y`);
3. `y` is a right dead end of depth `k`;
4. `|y| + R(s) + |s| ≤ R_n + min(k, 2n+2)`.

Then `F_n(R) = ∅` for every admissible `R`, so the recursion stalls at
level `n`.

**Proposition 2 (the spot is a genuine dead end on the rim).** Hypotheses 1
and 2 force `|y| > R_n − R(s) − |s|`, because `p ∈ F_{n−1}(R_n)` passes the
test `(s, y)` whenever `|y| ≤ R_n − R(s) − |s|`. With hypothesis 4 this gives
`k ≥ 1`. So:
- Theorem 1 can fire only at an element `y` that is a right dead end of depth
  at least `|y| + R(s) + |s| − R_n ≥ 1`, sitting in the untested rim of the
  ball;
- if the generating set has no dead ends (every `y` has a generator `a` with
  `|ya| = |y| + 1`), Theorem 1 is vacuous.

**Theorem 3 (translation-coherent asymmetry).** Replace (A) by

**(A_geo)** for every `s ≠ 1` and every `c` with `Q_c(s) ⊆ B(R)`, some
`μ ∈ B(R(s))` has `q(μc) ≠ q(μsc)`,

and let `F^geo_n(R)`, `L^geo_n` be the resulting greedy recursion (clauses
(C) and (K) unchanged). Then:
1. (A_geo) implies (A), so `F^geo_n(R) ⊆ F_n(R)` for the same `L_n`, and
   `F^geo_n(R)` is decidable uniformly in `n`, `R`, `L_n`.
2. **Coherence.** Let `p : B(R_n) → A` satisfy (A_geo) with radius `R_n`. Let
   `q : B(R) → A` and `c` satisfy `B(R_n)c ⊆ B(R)` and `w_{R_n}(q,c) = p`.
   Then `q` passes every test `(s, c')` with `Q_{c'}(s) ⊆ B(R_n)c`.
3. Hence no member of any `L^geo_n` is `s`-symmetric at any `y` with
   `Q_y(s) ⊆ B(R_n)`. The mechanism of Theorem 1 never occurs in the (A_geo)
   recursion, and a placed copy of a member of `L^geo_n` never fails a test
   that reads only its own values. The only tests an extension can fail are
   **straddling** ones, whose read set `Q_{c'}(s)` is not contained in any
   single placed copy.

**What this changes.**
- *For (G).* Attempt 5 of
  `decidable-fp-groups-have-effective-minimal-free-subshifts` asked for data
  under which every admissible level eventually contains a dead end, a
  pattern with no extension. Theorem 1 is a concrete certificate of that
  kind: one pattern, one element `s`, one Cayley-graph dead end. It depends
  on the generating set through dead-end depth. Dead-end depth is not a
  quasi-isometry invariant; Riley--Warshall showed this, recalled here and
  not re-verified.
- *Repair.* Theorem 3 gives the variant (G_geo),
  `translation-coherent-greedy-margin-towers-never-stall`, with the same
  complete route to (M2),
  `effective-minimal-free-subshifts-via-coherent-greedy-tower`, and no
  self-killing patterns.
- *What stays open.* Two steps are not proved.
  - Theorem 1 does not refute (G). That would need, for **all** data
    `(A, R)`, a level at which the maximal family `L_n` contains a pattern
    satisfying 1--4.
  - Theorem 3 does not prove (G_geo), because straddling tests and (K) can
    still conflict.

---
rg: 2
id: covering-towers-iff-effective-minimal-free-subshifts
kind: claim
title: Over a finitely generated group with solvable word problem, a nonempty effectively closed minimal free subshift exists iff a computable margin covering tower of finite patch families exists
distinct_from:
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2), an existence statement for infinite fp groups with solvable word problem; this is an equivalence, proved for every f.g. group with solvable word problem, that replaces the existence of the subshift by the existence of a finite combinatorial tower whose conditions are checked on finite balls, so no global recurrence modulus has to be controlled.
  gjs-guided-blueprints-are-computable-over-decidable-groups: that makes the GJS blueprint layer computable and produces no subshift; this characterises effective minimal free subshifts by patch towers, and GJS blueprints with disjoint copies do not satisfy the margin covering condition (C) by themselves.
  rf-toeplitz-subshift-has-computable-language: that is one Toeplitz construction over effectively residually finite groups; this is a characterisation with no residual finiteness assumption, and its supplement shows that towers whose patch returns contain an R_n-dense subgroup are periodic.
---

**ESTABLISHED** (route `covering-towers-iff-effective-minimal-free-subshifts-proof`).

**Setting.** `G` is a group with a finite generating set and solvable word
problem.
- Words are handled as shortlex normal forms, so balls `B(R)` are computable
  finite lists.
- `|g|` is word length, and `d(x,z) = |x z^{-1}|`, so `B(r)g` is the set of `h`
  with `d(g,h) ≤ r`.
- The action on `A^G` is `(λ.z)(μ) = z(μλ)`.
- The window of `z` at `h` is `w_R(z,h)(μ) = z(μh)` for `μ ∈ B(R)`. It
  satisfies `w_R(λ.z, h) = w_R(z, hλ)`.

**Definition (margin covering tower).** It consists of:
- a finite alphabet `A`;
- computable sequences `R_n` and `m_n` with `0 ≤ m_n ≤ R_n ≤ R_{n+1}`,
  `m_n → ∞` and `R_n − m_n → ∞`;
- uniformly computable finite nonempty families `L_n` of patterns
  `B(R_n) → A`.

It must satisfy three conditions.
- **(C) margin covering.** For every `q ∈ L_{n+1}` and every
  `g ∈ B(R_{n+1} − m_{n+1})` there is `h` with `d(g,h) ≤ R_n − m_n`,
  `|h| ≤ R_{n+1} − R_n` and `w_{R_n}(q,h) ∈ L_n`. Here `w_{R_n}(q,h)(μ) = q(μh)`
  is defined because `|μh| ≤ R_{n+1}`.
- **(K) containment.** For every `q ∈ L_{n+1}` and every `p ∈ L_n` there is
  `c ∈ B(R_{n+1} − R_n)` with `w_{R_n}(q,c) = p`.
- **(A) asymmetry.** There is a function `R : G∖{1} → N` with the following
  property. For every `n`, `q ∈ L_n`, `s ≠ 1` and `c` with
  `|c| ≤ R_n − R(s) − |s|`, some `μ ∈ B(R(s))` has `q(μc) ≠ q(μsc)`.

**Theorem.** The following are equivalent.
1. `G` carries a nonempty effectively closed subshift `Y ⊆ A^G` on which `G`
   acts minimally and freely.
2. `G` has a margin covering tower.

Direction 2 ⇒ 1 is explicit. It takes
`Y = {z : ∀n ∀g ∃h ∈ B(R_n − m_n)g, w_{R_n}(z,h) ∈ L_n}`, and then:
- the forbidden patterns are decidable;
- the recurrence radius is computable;
- `Y` is exactly the orbit closure of every one of its points.

**Corollary (overlap-recurrent points).** Suppose `y ∈ A^G` is computable, and
`R_n`, `m_n` are computable as above. Put `P_n = y|B(R_n)`. Assume:
- (OC) for every `n` and every `g ∈ G` some `h ∈ B(R_n − m_n)g` has
  `w_{R_n}(y,h) = P_n`;
- (A) holds for `L_n = {P_n}`.

Then the orbit closure of `y` equals
`Y_OC = {z : ∀n ∀g ∃h ∈ B(R_n − m_n)g, w_{R_n}(z,h) = P_n}`. It is a nonempty
effectively closed minimal free subshift. By the supplement, (OC) needs to be
checked only on the finite patches.

**Supplement (internal check).** Condition (OC) for `y = ∪ P_n` follows from
nested patches `P_{n+1}|B(R_n) = P_n` together with the finite conditions (IC_n):
for every `g ∈ B(R_{n+1} − m_{n+1})` some `h` with `d(g,h) ≤ R_n − m_n` and
`|h| ≤ R_{n+1} − R_n` has `w_{R_n}(P_{n+1},h) = P_n`.

**Obstruction (Lemma T, subgroup returns are periodic).** Let `H ≤ G` satisfy
`B(R)H = G`, and suppose `w_R(y,h) = w_R(y,1)` for all `h ∈ H`. Then `h.y = y` for
all `h ∈ H`.
- So no free design can take the return set of `P_n` to contain a subgroup `H_n`
  that is `R_n`-dense.
- That rules out Toeplitz- or subgroup-skeleton recurrence as the source of
  (OC). A Toeplitz-type point returns along finite-index subgroups whose
  fundamental domains have radius larger than the patch radius.

**What this changes for (M2).**
- Attempt 2 of `decidable-fp-groups-have-effective-minimal-free-subshifts`
  stopped at the global modulus: boundary patterns whose recurrence was not
  controlled.
- In a margin covering tower nothing is boundary. Every `m_n`-ball of every
  configuration lies inside some `L_n`-window, by Lemma 1 of the route.
- Hierarchies built from disjoint copies with gaps satisfy (C) only if `L_n`
  also lists the patches that straddle copy boundaries. Condition (K) for those
  patches is Attempt 2's circular condition (R_k).
- So (M2) is exactly the problem of building overlapping patch families. The
  global modulus is no longer a separate step.

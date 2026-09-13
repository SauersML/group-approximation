# Kazhdan quotientless targets: circularity, the random-complex moment barrier, a partial Sp(2,1) quotient

Lane `nrfh-kazhdan-quotientless`, 2026-09-12, base `origin/main` at `bd53fc92`
(no node in this region changed since `1148ef93`). Nothing here is
Lean-verified, and no novelty is claimed for any argument pattern.

## 1. Circularity audit of route (ii)

### 1.1 Kapovich–Wise is already imported

`kapovich-wise-rf-iff-finite-quotients` imports Kapovich–Wise, *The equivalence
of some residual properties of word-hyperbolic groups*, J. Algebra 223 (2000),
Theorem 1.2, read from the published paper in
`kapovich-wise-rf-iff-finite-quotients-citation`. A second derivation from
Olshanskii's theorem is `kapovich-wise-via-g-subgroup`. Nothing to import.

### 1.2 Route (ii) is an equivalence edge, not an attack

`kazhdan-quotientless-hyperbolic-via-common-quotient` requires
`hyperbolic-group-without-finite-quotients`. The graph already makes that claim
equivalent to the root:
- `quotientless-hyperbolic-via-kapovich-wise` gives root ⇒ quotientless;
- `non-rf-hyperbolic-from-quotientless-hyperbolic` gives the converse.

So the premise of route (ii) is Gromov's question itself, in its Kapovich–Wise
form.

**Verdict.**
- **Not circular.** The implication is true, and a least fixpoint never fires a
  cycle, so nothing self-establishes.
- **Redundant as an attack.** Any proof of its premise already proves the root.
- **Its content is "(T) is free".** Given any infinite hyperbolic group without
  finite quotients, a common Olshanskii quotient with a torsion-free Kazhdan
  partner gives a Kazhdan one. The Kazhdan target is exactly as hard as the root.

**Route (i) is in the same position.** Its premise,
`sp21-lattice-hyperbolic-quotient-without-finite-quotients`, follows from the
root by `sp21-lattice-quotientless-quotient-via-host`. That route requires:
- the root;
- `hyperbolic-rf-question-reduces-to-one-fixed-host`;
- `torsion-free-hyperbolic-kazhdan-partner-exists`.

Among the three routes into the Kazhdan target, only route (iii),
`kazhdan-quotientless-hyperbolic-via-random-complex`, has a premise that is not
known to follow from the root.

### 1.3 A missing edge: forgetting (T)

Before this lane, the only consumer of the Kazhdan target was
`non-mf-hyperbolic-from-kazhdan-quotientless`. That route also requires the open
`mf-kazhdan-group-without-finite-quotients-is-trivial`.

So a proof of the Kazhdan target would not have reached the root in the graph,
for instance one through `kazhdan-quotientless-hyperbolic-from-sp21-quotient`.
Yet forgetting (T) reaches the root at once.
`hyperbolic-rf-vtf-kazhdan-equivalence` records that implication in prose, but a
claim about an equivalence is not an edge.

**Added:** route `quotientless-hyperbolic-from-kazhdan-quotientless`, from the
Kazhdan target to `hyperbolic-group-without-finite-quotients`. It closes an
intended 2-cycle with route (ii).

Four claims now form one equivalence class in the graph:
- the root;
- the quotientless target;
- the Kazhdan target;
- `sp21-lattice-hyperbolic-quotient-without-finite-quotients`.

This holds modulo their side premises: Kapovich–Wise, the Kazhdan partner,
Olshanskii's theorem and the fixed-host reduction.

## 2. Route (iii): random complex groups

**Setting.** `Y ~ Y(n,p)` is the Linial–Meshulam complex: complete 1-skeleton,
with each triangle present independently with probability `p`. Take
`p = n^(-1+η)` with `0 < η < 1/2`.

### 2.1 Correction: no abelian quotient of any order

Both sources were downloaded from arXiv on MSI and read locally from the PDFs.

**Hoffman–Kahle–Paquette,** *The threshold for integer homology in random
d-complexes*, arXiv:1308.6232v2.
- **Theorem 1 (p. 3):** "Let d ≥ 2 be fixed and Y ~ Y_d(n,p). If
  p ≥ 80d log n / n then H_{d−1}(Y;Z)=0 w.h.p."
- **Theorem 2:** for `p ≥ 40d log n / n`,
  `P(H_{d−1}(Y; Z/qZ) != 0) <= 1/n^{d+1}`, uniformly over primes `q`.
- **p. 2:** the Meshulam–Wallach counting argument does not handle `q` growing
  superpolynomially in `n`.

**Łuczak–Peled,** *Integral homology of random simplicial complexes*,
arXiv:1607.06985v1.
- **Theorem 1 (p. 3):** in the random 2-complex process, a.a.s. the hitting time
  of `H_1(Y;Z) = 0` equals the hitting time of every edge lying in a triangle. So
  the threshold is `2 ln n / n`.
- **Lemma 2 (after Kalai):** if `H_1(Y;F_p) = 0` for every prime
  `p <= √3^{C(n−1,2)}`, then `H_1(Y;Z) = 0`.

**Mid-range form.** For large `n`, `n^(-1+η) >= 160 log n / n`, so a.a.s.
`H_1(Y;Z) = 0`. `Y` is connected, so `H_1(Y;Z) = π_1(Y)^ab`. Hence `π_1(Y)` is
perfect: it has no nontrivial abelian quotient of any order.

**Consequences.**
- "What is left" in `random-complex-group-no-quotients-above-exp-pn` listed
  cyclic groups of prime order above `exp(n^η/8)`. That case was never open.
- The fact is recorded as `random-complex-mid-range-group-is-perfect`, with a
  citation route.
- What remains is nonabelian simple quotients above `exp(n^η/8)`.

**Calibration.** For abelian quotients the counting barrier at superpolynomial
order was real (HKP p. 2), and the integral theorems go past it.

### 2.2 The exact first moment diverges above exp((1+ε)pn)

**Free edges.** For an edge `e` of `K_n`, let `A_e` be the event that no triangle
of `Y` contains `e`. Then `P(A_e) = (1−p)^(n−2) = exp(−pn + o(1))`, since
`p^2 n -> 0`.
- On `A_e`, `Y` is `Y_e` (the open edge removed) with a 1-cell attached. `Y_e` is
  connected, so `π_1(Y) = π_1(Y_e) * Z`.
- A triangle contains at most one edge of a matching `e_1,...,e_j`, so the events
  `A_{e_i}` are independent.
- On their intersection, `π_1(Y) = K * F_j` with `K = π_1(Y ∖ ∪e_i)`. Every map
  `F_j -> G` extends by the trivial map on `K`.

**Proposition.** Fix `0 < ε <= 1` and a finite group `G` with
`log|G| >= (1+ε)pn`. The following expectations tend to infinity.
1. **Nontrivial homomorphisms** `π_1(Y) -> G`. With `j = 1` the count is at least
   `(|G|−1) exp(−pn + o(1))`.
2. **Nontrivial classes in** `H^1(Y;G) = Hom(π_1 Y, G)/G`, the objects of
   Meshulam's count. The count is at least
   `(|G|^{j−1} − 1) exp(−jpn + o(1))`. Its exponent `pn(jε − 1 − ε)` is positive
   for `j = ⌈2/ε⌉ + 1`.
3. **Normal subgroups `N` with `π_1(Y)/N ≅ G`,** for `G` nonabelian simple.
   - `G` is 2-generated (classification), and `Aut G` acts freely on generating
     pairs, so `#Epi(F_j,G)/|Aut G| >= |G|^{j−2}`.
   - The exponent `pn(jε − 2 − 2ε)` is positive for `j = ⌈4/ε⌉ + 1`.
4. **Subgroups of index `m`,** when `log m! >= (1+ε)pn`. `F_j` has at least
   `(m!)^{j−1}` of them: send the first generator to an `m`-cycle and the rest
   arbitrarily, modulo relabelings fixing the base point.

**All this mass sits on a vanishing event.**
`P(∪_e A_e) <= C(n,2) exp(−pn + o(1)) -> 0`, because `pn = n^η >> log n`.

**Consequences.**
- For large `n` there is an `A_m` with
  `log(m!/2) ∈ [(1+ε)pn, (1+ε)pn + log n]`. So the bound
  `P(some object exists) <= E[#objects]` exceeds 1 for every one of these counts,
  however refined its entropy accounting or label cancellation. **No untruncated
  first-moment argument proves `random-complex-group-no-quotients-above-exp-pn`.**
- `random-complex-group-no-quotients-below-exp-pn` remarks that the count "stops
  at order about `exp(pn/3)`". That is a limit of Meshulam's estimate. The
  proposition is a limit of the exact expectation.
- Not determined here: whether the exact expectation tends to 0 up to
  `exp((1−ε)pn)`. The repo's run of Meshulam's argument proves `exp(pn/8)`.

**The heuristic fails for the same reason.** Count `|G|^{C(n,2)}` cochains
against about `pn^3/6` triangle constraints, each satisfied with probability
about `1/|G|`. This predicts about `|G|^{n^2/2 − pn^3/6}` classes, i.e. none. Its
independence assumption breaks on rare local configurations, and the free edges
exploit exactly those.

### 2.3 What must be controlled

Fix `δ > 0` and let `𝒢_δ` be the intersection of two events:
- every edge of `K_n` lies in at least `(1−δ)(n−2)p` triangles of `Y`;
- `H_1(Y;Z) = 0`.

**`P(𝒢_δ) -> 1`.**
- Each edge's triangle count is `Bin(n−2,p)`. Chernoff with a union bound gives
  failure probability at most `n^2 exp(−δ^2 (n−2)p/2)`.
- The homology event holds by 2.1.
- On `𝒢_δ` no edge is free.

Put `N_0 = exp(n^η/8)`. A nontrivial finite quotient has a simple quotient `S`.
On `𝒢_δ`, `S` is nonabelian. If `|S| <= N_0`, it is excluded a.a.s. by
`random-complex-group-no-quotients-below-exp-pn`. Hence

```text
P(π_1(Y) has a nontrivial finite quotient)
  <= o(1) + Σ_{S nonabelian simple, |S| > N_0} E[ #{N ⊴ π_1(Y) : π_1(Y)/N ≅ S} · 1_{𝒢_δ} ].
```

**Status of the truncated sum.**
- If it tends to 0 for some fixed `δ`, the open claim follows, and by 2.2 the
  truncation is necessary.
- Not determined here: whether it tends to 0, and where the threshold of the
  truncated first moment lies.
- The sum runs over `A_m` with `m` of order `n^η/log n` and above, and over groups
  of Lie type of unbounded rank or over large fields.

### 2.4 The route is not killed

No known argument produces a finite quotient of a mid-range `π_1(Y)`: property
(T) blocks cubulation, and every connected cover inherits local expansion. The
divergence in 2.2 lives on a vanishing event, so it is evidence about the method,
not about the groups. Route (iii) stays live.

## 3. Route (i): what Olshanskii quotients of a Sp(2,1) lattice can remove

**Setting.** `Γ` is a torsion-free cocompact arithmetic lattice in `Sp(2,1)`,
set up as in `sp21-bounded-rank-simple-quotients-almost-all-congruence`. `Γ̄` is
its congruence completion.

**Used without a node,** as in the sibling routes:
- `Γ` is non-elementary hyperbolic with `E(Γ) = 1`;
- `Γ` has (T), so `Γ^ab` is finite, and (T) passes to quotients;
- the classification of finite simple groups.

### 3.1 The partial statement

For every `r >= 1`, `f >= 1` and finite `B ⊂ Γ` there is `π : Γ ->> G`, injective
on `B`, such that:
1. `G` is torsion-free, non-elementary hyperbolic and Kazhdan;
2. `G` has no nontrivial finite quotient of order `<= f`;
3. `G` has no nontrivial congruence quotient, i.e. `ker π` is dense in `Γ̄`;
4. no finite simple quotient of `G` is abelian, sporadic, or of Lie type of rank
   `<= r`. So each one is alternating or of rank `> r`, and `G` is perfect.

Recorded as `sp21-lattice-quotient-with-only-large-type-simple-images`, with
proof route `sp21-large-type-simple-images-quotient-proof`.

### 3.2 Proof

**Step 1: a proper quotient.**
- Choose a proper finite-index normal subgroup `Δ_0 ⊴ Γ`. It has `E = 1`, so it
  is a G-subgroup.
- Olshanskii gives `φ_1 : Γ ->> H`, injective on `B`, with `φ_1(Δ_0) = H` and `H`
  torsion-free non-elementary hyperbolic.
- `M = ker φ_1` maps onto `Γ/Δ_0`, so `M != 1`.

**Step 2: finitely many bad images.** Call a simple quotient `χ` of `H` *bad* if
its image is abelian, sporadic, of rank `<= r` or of order `<= f`, or if
`ker(χ φ_1)` is congruence. There are finitely many bad images:
- **abelian:** `Γ^ab` is finite;
- **sporadic, or of order `<= f`:** a finitely generated group has finitely many
  epimorphisms onto each finite group;
- **congruence:** they factor through the finite group `Γ̄/closure(M)`, by
  openness;
- **non-congruence of rank `<= r`:** finitely many by the bounded-rank theorem.

Let `Δ_1` be the intersection of their kernels. It has finite index and is a
G-subgroup of `H`.

**Step 3: kill them.** Olshanskii gives `φ_2 : H ->> G`, injective on `φ_1(B)`,
with `φ_2(Δ_1) = G` and `G` torsion-free.
- Let `ψ : G ->> S` be simple and bad: its type is bad, or `ker(ψπ)` is
  congruence.
- Then `ψφ_2` is a bad image of `H`, so it kills `Δ_1`.
- But `ψ(φ_2(Δ_1)) = S`, a contradiction.

**Conclusions.**
- (2): a small nontrivial quotient has a small simple quotient.
- (3): a nontrivial congruence quotient has a congruence simple quotient.
- Perfectness: `G^ab` is a finite quotient of `Γ^ab` with no simple quotient.

### 3.3 What finitely many steps can and cannot remove

**One step removes finitely many images by design.**
- A step `φ : H ->> G` with `φ(Δ) = G` removes the images `χ` with
  `ker χ ⊇ Δ`, because `ker φ` maps onto `H/Δ`.
- Nonabelian simple images `χ_1,...,χ_k` with distinct kernels satisfy
  `H/∩ ker χ_i ≅ ∏ S_i`. So an infinite family never has a common kernel of
  finite index.

**Wholesale removal needs separation.**
- Any other image dies only incidentally, when `ker φ ⊄ ker χ`.
- Two steps remove a whole family if every nontrivial normal subgroup lies in the
  kernels of only finitely many of its members:
  - congruence images do, by openness;
  - bounded-rank images do, by the bounded-rank theorem together with openness.
- For alternating and rank-`> r` images this is the open
  `sp21-noncongruence-simple-kernels-separate-points`.
- `tf-kazhdan-hyperbolic-alternating-kernels-not-separating` shows that (T),
  hyperbolicity and torsion-freeness do not supply it.

**Infinitely many steps leave the class.**
- Suppose `Γ ->> G_1 ->> G_2 ->> ...` has kernels `M_1 ⊊ M_2 ⊊ ...`.
- `Γ` is finitely presented, so a finitely presented quotient has a normally
  finitely generated kernel, which would lie in some `M_i`.
- So `Γ/∪ M_i` is not finitely presented, and in particular not hyperbolic.

### 3.4 Contrapositive

Suppose every hyperbolic group is residually finite. Then each `G` of 3.1 is
residually finite. Its points are separated by finite quotients whose simple
quotients are all large alternating or large-rank groups, with non-congruence
kernels in `Γ`.

## 4. Graph changes in this lane

- Route `quotientless-hyperbolic-from-kazhdan-quotientless` (§1.3).
- Claim `random-complex-mid-range-group-is-perfect` and its citation route (§2.1).
- `random-complex-group-no-quotients-above-exp-pn`: cyclic case corrected, and
  an Attempts bullet for §2.2–2.3.
- Claim `sp21-lattice-quotient-with-only-large-type-simple-images` and route
  `sp21-large-type-simple-images-quotient-proof` (§3).

None of these establishes an open claim. `non-residually-finite-hyperbolic-group`
and `kazhdan-hyperbolic-group-without-finite-quotients` remain OPEN.

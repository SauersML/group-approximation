# gq-referee-b: arithmetic Lie lattices have faithful BS members; `H^2 × T` (citation and scope lens)

Nodes as landed at a732dc8b6 (lane bh-cat0), read in their current form, which includes the referee-a nits applied in 8462f018b:
- `arithmetic-lie-lattices-have-faithful-bs-members` (+ `arithmetic-lie-lattices-faithful-bs-proof`);
- `cat0-groups-on-hyperbolic-plane-times-tree-lie-in-type-a-class` (+ `cat0-hyperbolic-plane-tree-type-a-proof`).

Both were passed by referee a (proof-gap lens).

Main secondary source: D. Witte Morris, *Introduction to Arithmetic Groups*, arXiv:math/0106063v6, read at source.
Book page `p` is PDF page `p + 16`.

**Verdict: PASS.**
- Borel density, commensurator density and the commensurator criterion, Margulis arithmeticity, finite presentation of
  lattices, the quaternion Fuchsian group and Foertsch–Lytchak are pinned below.
- The finiteness of `G ∩ ∏_(i≠j) L_i` follows in three lines from the definition of irreducibility (§1).
- Kazhdan–Margulis and Scott remain unpinned (W2).
- One scope fix: the title of the arithmetic node should say "irreducible" (W1).
- The Appendix C material also resolves W3 of my report 613ac7fec (§4).

## 1. `arithmetic-lie-lattices-have-faithful-bs-members`

**Borel density, Step 3.** Morris, Theorem 4.5.1 (book p. 56). Assume "Γ projects densely into the maximal compact
factor of `G`". Then:
- "Every `ρ(Γ)`-invariant subspace of `V` is `ρ(G°)`-invariant."
- The hypothesis is vacuous when there are no compact factors.
- Applied with `ρ = Ad`, this is exactly the route's step "`d` is `Ad(G)`-invariant, hence an ideal". ✓

**The end of Step 4.** Morris, Corollary 4.5.4 (p. 57): "If `N` is a finite, normal subgroup of `Γ`, then
`N ⊆ Z(G)`." This is the route's "`K` finite normal, so `K ⊆ Z(L) = 1`". ✓

**Finiteness of `G ∩ ∏_(i≠j) L_i`.** This is listed in the trust surface. It follows from Morris's definition, and I
suggest adding the argument.
- Morris, Definition 4.3.1 (p. 50): "Γ is irreducible if `ΓN` is dense in `G`, for every noncompact, closed, normal
  subgroup `N` of `G°`."
- Take `N = L_j`. Then `pr_(≠j)(G)` is dense in `∏_(i≠j) L_i`.
- `Δ = G ∩ ∏_(i≠j) L_i` is discrete and normalized by `pr_(≠j)(G)`, hence by its closure.
- A connected group normalizing a discrete group centralizes it. So `Δ ⊆ Z(∏_(i≠j) L_i) = 1`. ✓

**The commensurator.** Morris, Remark 5.2.5(1) (p. 93):
- "if Γ is arithmetic (and `G` is connected, with no compact factors), then `Comm_G(Γ)` is dense in `G` (see
  Proposition 5.1.8)".
- "Margulis proved a converse ... Γ is arithmetic iff `Comm_G(Γ)` is dense in `G` (see Theorem 16.3.3)".
- For the node's "non-discrete exactly when arithmetic", the non-arithmetic direction is Exercise 5.2#3 (p. 93): "if
  `G` is simple and Γ is not arithmetic, then Γ, `N_G(Γ)`, and `Comm_G(Γ)` are commensurable".
- That is the simple case. For semisimple `L`, cite Margulis's theorem via Theorem 16.3.3 (not read).

**Margulis arithmeticity, instance 4.** Morris, Theorem 5.2.1 (p. 92): "If `G` is not isogenous to `SO(1,n) × K` or
`SU(1,n) × K`, for any compact group `K`, and Γ is irreducible, then Γ is arithmetic." Real rank `≥ 2` excludes the
rank-one cases. ✓

**Finite presentation of lattices, Step 5.**
- Morris, Remark 5.2.4(2) (p. 93), refers to "Theorem 4.7.10": every lattice is finitely presented, through
  arithmeticity. ✓
- For the arithmetic `G` of this node, §4.7 applies directly.

**The quaternion algebra of instance 1.** Morris, Proposition 6.2.4 (p. 118), "Fix positive integers `a` and `b`",
with `G = SL(1, H^(a,b)_R)`:
- "`G ≅ SL(2,R)`";
- "`G_Z = SL(1, H^(a,b)_Z)` is an arithmetic subgroup";
- "`G_Z` is cocompact in `G`" if and only if `H^(a,b)_Q` "is a division algebra".

The algebra ramified at `{2, 3}` is `H^(2,3)_Q`:
- The Hilbert symbols `(2,3)_3 = (2,3)_2 = −1`, and `(2,3)_∞ = +1`, so it is ramified exactly at `{2, 3}`.
- It is split at `∞` and it is a division algebra.
- So Proposition 6.2.4 applies with `(a, b) = (2, 3)`. Its order `Z[i, j, k]` is commensurable with a maximal order. ✓

**Not pinned.** The Kazhdan–Margulis covolume bound (W2). It is standard, and I did not find it in the parts of Morris
I read. Britton's lemma and Cartan's closed subgroup theorem are textbook facts.

**Priority.** BLIW §12 (pp. 24–27 of arXiv:2408.05673v2, read for 613ac7fec) contains no arithmetic lattices. It
contains no surface groups either, except through `BS_(F_2)`-type examples. I searched no later literature.

## 2. `cat0-groups-on-hyperbolic-plane-times-tree-lie-in-type-a-class`

- **Foertsch–Lytchak**, arXiv:math/0605419, Theorem 1.1, p. 2, as quoted in 613ac7fec.
  - `H^2` and a branching `T` are both irreducible, not `R`, and not isometric to each other.
  - So there is no permutation of factors, and every isometry splits. The route's "non-isometric irreducibles" is the
    needed hypothesis. ✓
- **The fibre-group argument** (NEC group, Selberg, centralizer of the finite kernel, the degree formula on `H^2`):
  correct as written. It is the proof-gap lens's domain.
- **Selberg.** Morris (4.8.2_S), p. 460, for the S-arithmetic form, and §4.8 (p. 68) for lattices: "Γ has a
  torsion-free subgroup of finite index". ✓
- **Scott, `H^2 × R`.** Not read (W2). Scott's theorem concerns closed `H^2 × R` manifolds. The route applies it to a
  group acting geometrically, possibly with torsion. That needs one step first: pass to a torsion-free finite-index
  subgroup, which is free and cocompact on `H^2 × R`. It exists by Selberg, since `Γ ≤ Isom(H^2) × Isom(R)` is linear.
- **Item 2.** It needs `Γ_v` residually finite and its image an irreducible arithmetic lattice in `Isom(X)^0`. Both
  are stated. By Morris Theorem 5.2.1, "any irreducible lattice when `X` has real rank `≥ 2`" is arithmetic, provided
  `X` has no rank-one factors of the excluded types. ✓

## 3. Scope

- **The arithmetic node's title** says "Every arithmetic lattice in a semisimple Lie group". The Setting assumes an
  irreducible lattice in `L` with trivial center and no compact factors. Step 4 uses irreducibility: for a reducible
  `G`, the group `G ∩ ∏_(i≠j) L_i` is infinite and the argument fails. So the title should read "every irreducible
  arithmetic lattice" (W1).
- **The claim "includes closed surface groups".** It is right: the surface group is commensurable with the torsion-free
  subgroup of `H^(2,3)_Z`-units.
- **The `H^2 × T` node's "Reducible fibre lattices are not covered here".** Consistent with W1. ✓

## 4. Addendum to 613ac7fec (W3, W4 of that report)

Morris, Appendix C (pp. 457–461), read at source:
- **Cocompactness.** "(5.3.1_S) (Godement Criterion) `Γ\G_S` is compact if and only if Γ has no nontrivial
  unipotent elements [8, Thm. 5.7(2), p. 268]". Here [8] is Platonov–Rapinchuk.
  - For `PD^×` with `D` a division algebra, a rational element with unipotent image has characteristic polynomial
    `(t − λ)^2`, with `λ ∈ Q`, so `x − λ` is nilpotent in `D`. Hence `x = λ`, and there are no nontrivial unipotents.
  - So `O[1/pq]^× / Z[1/pq]^×` is cocompact in `PD^×(R) × PGL_2(Q_p) × PGL_2(Q_q)`. Since `D` is definite,
    `PD^×(R)` is compact and may be dropped.
  - This pins W3 of 613ac7fec, through Morris's secondary statement.
- **Finite presentation.** "(4.7.10_S) Γ is finitely presented [8, Thm. 5.11, p. 272]". This pins the finite
  presentation needed in W2 of 613ac7fec for the quaternion instance.
- (C1.7), p. 460: "Every S-arithmetic subgroup of `G_S` is a lattice in `G_S`".

## Warnings

- **W1.** Title of `arithmetic-lie-lattices-have-faithful-bs-members`: "every **irreducible** arithmetic lattice".
- **W2.** Kazhdan–Margulis and Scott remain unpinned. For Scott, add the Selberg step: pass to a torsion-free
  finite-index subgroup before invoking the manifold classification.
- **W3.** Add the three-line finiteness argument of §1 and the Borel-density pins (Morris 4.5.1, 4.5.4) to the trust
  surface, which then shrinks.

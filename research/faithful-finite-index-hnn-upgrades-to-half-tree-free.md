---
rg: 2
id: faithful-finite-index-hnn-upgrades-to-half-tree-free
kind: claim
title: A faithful HNN extension of A over finite-index subgroups (ascending allowed) becomes, after a Baumslag–Solitar twist on A × Z, a non-ascending HNN extension in which no element fixes a half-tree; so the finite-type complexity gate (SS-hard)_1 is exactly the faithful finite-index HNN condition, and for the KMS groups it reduces to a commensuration of the torsion layer
distinct_from:
  finite-index-edge-hnn-embeds-in-fp-simple-group: that embeds a faithful finite-index HNN extension in a finitely presented simple group (via Bux–Llosa Isenrich–Wu); this upgrades faithfulness to the half-tree condition at the cost of a direct factor Z, so the same input also gives a topologically free E3′ instance through Li's Zappa–Szép theorem, with the same word problem.
  finite-type-e3-prime-hosts-carry-complexity-in-units: that names the gate (SS-hard)_k; this shows that for k = 1 in HNN form it coincides with attempt 5 of `fp-simple-groups-with-arbitrarily-complex-word-problem`, and that ascending extensions are allowed.
  fp-self-similar-groups-with-arbitrarily-hard-word-problem: that asks for hard finitely presented self-similar groups; a hard one whose virtual endomorphism is injective with finite-index image and trivial core feeds this upgrade, so it would settle (SS-hard)_1.
  equivariant-scaling-hnn-vertex-groups-are-linear: that kills the scaling shape for KMS-type vertex groups; this records the general reduction of the KMS case that the scaling shape is one instance of.
---

**ESTABLISHED** for items 1–3 (lane proof, bh-e3prime, 2026-09-18; elementary; not reviewed).
Item 4 is a structure lemma for the KMS groups, proved from their presentation (Kharlampovich–
Myasnikov–Sapir, arXiv:1204.6506v5, §4.1, read in `$GQ/src/kms/KMS-322.tex`, relations G1–G8,
Lemmas lH, lT). **(SS-hard)_1 stays OPEN.**

## Statement

Let `A` be a group, `C_1, C_2 <= A` of finite index, `φ : C_1 -> C_2` an isomorphism, and
`Γ = A*_φ = ⟨A, t | t^(-1) c t = φ(c) (c ∈ C_1)⟩`. Suppose `Γ` acts faithfully on its Bass–Serre
tree `T`, i.e. no nontrivial normal subgroup of `Γ` lies in `A`. Here `C_1 = A` or `C_2 = A`
(ascending) is allowed.

Fix integers `m_1, m_2` with `|m_1|, |m_2| >= 2` and `|m_1| ≠ |m_2|`. Put `A' = A × Z`,
`C'_1 = C_1 × m_1 Z`, `C'_2 = C_2 × m_2 Z`, `φ'(c, m_1 k) = (φ(c), m_2 k)`, and `Γ' = A'*_(φ')`.

1. **Upgrade.** `Γ'` is a non-ascending HNN extension over finite-index subgroups, and no nontrivial
   element of `Γ'` fixes pointwise a half-tree of its Bass–Serre tree `T'`. So (TF) of
   `nonascending-hnn-end-shifts-satisfy-e3-prime` holds for `Γ'`.
2. **Same complexity.** `A'` is of type `F_n` iff `A` is, and `T_(A')(ℓ) <= T_A(ℓ) + O(ℓ)`. So if
   `A` is of type `F_n`, the E3′ host `F(G_V × (Γ' ⋉ X_(T')))` is of type `F_n`, simple and of
   type (A). Its word problem is that of `A`, up to the exponential change of variables of that
   node.
3. **The gates coincide.** For one vertex group, (SS-hard)_1 in HNN form is equivalent to:
   *for every recursive bound there is a group of type `F_2` with a faithful HNN extension over
   finite-index subgroups whose word problem beats the bound.*
   - This is attempt 5 of `fp-simple-groups-with-arbitrarily-complex-word-problem`.
   - Its injective-virtual-endomorphism case is a case of
     `fp-self-similar-groups-with-arbitrarily-hard-word-problem`: a self-similar `G` whose virtual
     endomorphism `ψ : G_1 -> G` is injective with finite-index image and trivial core gives a
     faithful (possibly ascending) `G*_ψ`.
   - So one hard input settles three open nodes at once. The two hosts are Bux–Llosa Isenrich–Wu
     (finitely presented simple) and the V-stabilized end-shift full group (E3′, topologically free,
     quantum rigid).
4. **KMS structure.** Let `G = G(M)` be a KMS group with `K` counters. Then:
   - the torsion elements form the normal subgroup `N = T·H_1^(H_2)`, which is locally finite of
     exponent dividing `p^2`, and `G/N ≅ H_2 ≅ Z^(4K)`;
   - every isomorphism `φ : C_1 -> C_2` between finite-index subgroups maps `N ∩ C_1` onto
     `N ∩ C_2` and induces `ψ ∈ GL_(4K)(Q)` between finite-index lattices;
   - `G*_φ` is faithful iff no nontrivial normal subgroup of `G` in `C_1` is `φ`-invariant. That
     splits into a lattice clause (no nonzero `ψ`-invariant lattice carried by a normal subgroup
     meeting `N` trivially) and a torsion clause (no nontrivial `φ`-invariant normal subgroup of `G`
     inside `N ∩ C_1`).
   - The lattice clause is easy to meet. The whole difficulty is the torsion clause, where `T`
     carries the machine's configurations.

## Proof of item 1

- **Maps.** `π_1 : Γ' -> Γ`, `(a, z) ↦ a`, `t' ↦ t`, and `π_2 : Γ' -> B = BS(m_1, m_2)`,
  `(a, z) ↦ b^z`, `t' ↦ s`, where `B = ⟨b, s | s^(-1) b^(m_1) s = b^(m_2)⟩`. Both respect the
  relations. They induce equivariant simplicial maps `T' -> T` and `T' -> T_B` on vertices
  `γ' A' ↦ π_i(γ') ·(base)`, sending edges of type `ε` to edges of type `ε`.
- **Links.** The edges of type `ε` at a vertex of `T'` are indexed by `A/C_ε × Z/m_ε Z`. `π_1`
  forgets the second coordinate and `π_2` the first. The back edge of a vertex reached along type
  `ε` is `(ε̄, (1, 0))`.
- **π_1 of a half-tree is all of T.** Let `S'` be the half-tree beyond a directed edge of `T'`, and
  `w' ∈ S'`. Every edge `(ε, a)` at `π_1(w')` has the `|m_ε| >= 2` preimages `(ε, (a, z))`, at most
  one of which is the back edge of `w'`. So the edges of `S'` at `w'` map onto all edges at
  `π_1(w')`. Hence `π_1(S')` contains, with each vertex, all its neighbours, and so equals `T`.
- **π_2 of a half-tree contains a half-tree.** Every edge `(ε, z)` at `π_2(w')` other than its back
  edge has the preimage `(ε, (1, z))`, which is not the back edge of `w'`. By induction, `π_2(S')`
  contains the half-tree of `T_B` beyond the image of the defining edge.
- **Conclusion.** Let `g'` fix `S'` pointwise.
  - `π_1(g')` fixes `T` pointwise, so `π_1(g') = 1` by faithfulness.
  - `π_2(g')` fixes a half-tree of `T_B`, so `π_2(g') = 1`, by Step 9 of
    `nonascending-hnn-end-shifts-satisfy-e3-prime-proof` (`|m_1| ≠ |m_2|`).
  - `g'` fixes a vertex, so it is conjugate into `A'`. But `ker π_1 ∩ A' = 1 × Z`, and
    `π_2(1, z) = b^z ≠ 1` for `z ≠ 0`. So `ker π_1 ∩ ker π_2` meets every vertex stabilizer
    trivially, and `g' = 1`.
- **Non-ascending.** `[A' : C'_i] = [A : C_i] |m_i| >= 2`.

## Proof of items 2–4

- **Item 2.** `A × Z` has the same finiteness type as `A`, and the word problems differ by a
  linear-time projection. Then apply `nonascending-hnn-end-shifts-satisfy-e3-prime` to `Γ'`.
- **Item 3.** "Only if": TF implies faithful, and (SS-hard)_1 in HNN form asks for a hard vertex
  group `H` of type `F_2` with a non-ascending TF structure. "If": item 1, with `A × Z` of the same
  complexity. For the self-similar case, the kernel of `G*_ψ` on its tree is the largest normal
  `N ⊴ G` with `N <= G_1` and `ψ(N) = N`. It lies in the ψ-core, which is trivial.
- **Item 4.**
  - Killing `L_0 ∪ L_1` sends every relation G1–G8 to a consequence of "the `a`-letters commute".
    So `G -> Z^(4K)` is onto, and the abelian group `H_2`, with `4K` generators, maps isomorphically.
    Its kernel is the normal closure `N` of `L_0 ∪ L_1`. By KMS, `G = T ⋊ (H_1^(H_2) ⋊ H_2)`, so
    `N = T ⋊ H_1^(H_2)`.
  - By Lemmas lT and lH, `T` and `H_1^(H_2)` are abelian of exponent `p`. A finitely generated
    subgroup of `N` is finite-by-(finite abelian), hence finite. So `N` is locally finite, and it
    is the torsion set, because `G/N` is torsion-free.
  - Isomorphisms preserve torsion, which gives `φ(N ∩ C_1) = N ∩ C_2` and the induced `ψ`.
  - The faithfulness criterion is the kernel description of the HNN tree action. Split an invariant
    normal `N'` by `N' ∩ N`: either it is nontrivial (torsion clause), or `N'` embeds in `Z^(4K)`
    as a `ψ`-invariant lattice (lattice clause).

## The KMS test: status

- **Dead shapes on main.**
  - Scalings fixing the metabelian part force linearity over `F_p((x))`
    (`equivariant-scaling-hnn-vertex-groups-are-linear`), hence low complexity.
  - Virtual endomorphisms agreeing with endomorphisms of a finite-index normal subgroup give finite
    image (`virtually-endomorphic-self-similar-actions-have-finite-image`), which covers Frobenius
    scalings.
  - The Cartier contraction breaks every `Add` relation, since `C(P_n) = −1`
    (attempt 3 of `fp-self-similar-groups-with-arbitrarily-hard-word-problem`).
- **What a live φ must do (item 4).** A live `φ` must act on `N ∩ C_1` semilinearly over `ψ` and
  map the machine relations G8 of `C_1` to those of `C_2`.
  - A command polynomial `P` survives only if `ψ` sends `P` to an associate of a command polynomial.
  - For `ψ` a homothety `λ`, comparing the Baumslag–Remeslennikov relation `a' = a − 1` with its
    `λ`-image allows only `λ = p^j` (Frobenius) or its inverse (Cartier). Both are dead above.
    This is a lane check, not a proof.
  - So a live `φ` needs a non-homothetic `ψ` compatible with the BR relations of every counter block.
  - *Expected, not proved:* the BNS invariant of each block is three rays, which would force `ψ` to be
    a homothety times a finite-order map on each block, killing the KMS family outright.
- **Verdict.** The KMS groups are not excluded, but every commensuration shape available from their
  presentation is dead. The next test is to compute `Σ^1` of the metabelian layer, which would decide
  the expected homothety rigidity.

## Lesson for general BH

**Topological freeness costs one factor of Z; the complexity gate is intrinsic to the vertex group.**
A Baumslag–Solitar twist on `A × Z` upgrades any faithful finite-index HNN structure to the
half-tree condition. So finite-type E3′ instances of a given complexity exist exactly when faithful
finite-index HNN extensions of that complexity exist. Three open nodes are one question: hard simple
groups through Bux–Llosa Isenrich–Wu, hard self-similar groups, and (SS-hard)_1.

Product tricks do not help by themselves. A direct or wreath factor of the hard group is left invariant by any
commensuration built from easy data, so it lands in the kernel. The hard group must itself admit a
commensuration that shrinks every normal subgroup. For KMS groups that is a renormalization
symmetry of the machine's configuration module, and every available one is dead.

## Referee (bh-ref-ffwz, 2026-09-18): items 1–3 PASS; item 4 not checked at source

- **Item 1.** Correct.
  - `π_1` and `π_2` respect the relations, and they induce type-preserving equivariant maps of
    trees.
  - Forward edges at `w'` surject onto all edges at `π_1(w')`, since `|m_ε| ≥ 2` and at most one
    preimage is the back edge. So `π_1(S') = T`.
  - For `π_2`, every non-back edge `(ε, z)` has the non-back preimage `(ε, (1, z))`. So
    `π_2(S')` contains a half-tree.
  - `ker π_1 ∩ ker π_2` is normal and meets `A' = A × Z` trivially, because
    `ker π_1 ∩ A' = 1 × Z` and `π_2(1,z) = b^z`. So it meets every vertex stabilizer
    trivially.
  - The step "`BS(m_1,m_2)` with `|m_1| ≠ |m_2|` has no nontrivial half-tree fixer" is cited
    from Step 9 of `nonascending-hnn-end-shifts-satisfy-e3-prime-proof`. I did not re-check it
    here; the divisibility heuristic along branches supports it.
- **Item 2.** `A × Z` has the finiteness type of `A`, since `A` is a retract. The E3′ host
  conclusion is conditional on `nonascending-hnn-end-shifts-satisfy-e3-prime` (1908f110d1),
  which has not been refereed.
- **Item 3.** Correct.
  - Being TF implies being faithful.
  - The kernel of `G*_ψ` on its tree is the largest normal `N ≤ G_1` with `ψ(N) = N`, which is
    trivial for faithful self-similar `G` (Nekrashevych).
- **Item 4.** The KMS relations G1–G8 were not read at source, so the structure lemma is
  unchecked. The "expected" homothety rigidity via `Σ^1` is correctly labelled as not proved.
- **Credit.** Kharlampovich–Myasnikov–Sapir for the groups; Bux–Llosa Isenrich–Wu for the
  finitely presented simple host.

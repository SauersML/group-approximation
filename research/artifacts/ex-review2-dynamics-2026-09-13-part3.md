# EX review 2, dynamics: part 3. Tree lattices and the remaining imports

Lane `ex-verify2-dynamics`, tip `6dd68ce8d`.
- **Tree lattices.** ex-tree-lattice-mixing (c267237d8b, 346bf1adb2, 4f039a7801; claim bodies edited at aafc5e8540).
- **Imports.** ex-nonsofic-action-entropy (3ecde705af, b7acd41a75), ex-rokhlin-lower (142d6e141e) and
  ex-tree-lattice-mixing (4581f9bd74).

| claim | verdict |
|---|---|
| `radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups` (+ `-proof`) | PASS |
| `radu-horizontal-projection-kills-delta-squared` (+ `-proof`) | PASS (first re-derivation; the first pass only named it as an input) |
| `radu-bmw-lattice-sofic`, `radu-nilpotent-by-arithmetic-quotients-are-sofic`, `radu-bmw-lattice-nonsofic` and `non-rf-tree-lattices-are-lifts-of-arithmetic-lattices` | OPEN and labelled OPEN; routes unfired |
| `cordeiro-sofic-relation-permanence` (+ `-citation`) | PASS, verbatim against arXiv:1608.05608v2, pp. 3–8 |
| `paunescu-sofic-action-class-permanence` (+ `-citation`) | PASS, verbatim against arXiv:1002.0605v5, pp. 2, 7, 13–16 |
| `popa-bernoulli-cocycle-superrigidity` (+ `-citation`) | PASS, verbatim against arXiv:math/0512646v8, p. 4. The first paragraph is a correct special case |
| `burger-mozes-infinitely-transitive-tree-groups` (+ `-citation`), items 4–5 | PASS against the Numdam scan, pp. 178, 184 and 187. Item 5 is a correct derivation from the cited statements |
| `popa-oe-superrigidity` and `alpeev-seward-stabilizer-growth-kills-outer-entropy` | source checked in the first pass (dynamics part 2, §13e) without the id; not re-read here |

## 3.1 `radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups`: PASS

**Item 1.**
- `γ_k(Λ_v)` is verbal, hence characteristic in `Λ_v`, hence normal in `Γ_R`.
- `∩_kγ_k(Λ_v) = 1` because free groups are residually nilpotent.
- Each nontrivial `g` in a ball `B_R` leaves `γ_k` for large `k`, so `G_k → Γ_R` as marked groups.
- `Λ_v = π_1(Cay(PGL_2(Z)))` has infinite rank, so `Λ_v/γ_k` is free nilpotent of class `k − 1` on infinitely many
  generators.

**Item 2.** If each `G_k` is sofic, the sofic approximations of `G_k` on `B_R(G_k) = B_R(Γ_R)` define almost actions
of `Γ_R` with the same defects. So `Γ_R` is sofic.

**Item 4.**
- *Primitivity.*
  - In `W = V/Λ_v`, the loop of `(xz)^2` visits `1, x, xz, xzx = z`. These are distinct, since `x, z` are distinct
    commuting nontrivial involutions of `PGL_2(Z)`.
  - Its edges `1–x`, `x–xz`, `xz–z` and `z–1` are distinct, so the loop is an embedded 4-cycle.
  - Three consecutive edges form a path, which extends to a spanning tree. The fourth edge then gives a free
    generator of `π_1(Y) = Λ_v` represented by `(xz)^2`.
  - So `(xz)^4 != 0` in `Λ_v^ab`.
- *Not residually finite.* `(xz)^4` lies in the finite residual of `Γ_R`, by item 2 of the Titz Mite–Witzel import,
  which was not re-read here. Every finite quotient of `G_k` is a finite quotient of `Γ_R`.
- *Not LEF.*
  - A marked limit of LEF groups is LEF, and a finitely presented LEF group is residually finite.
  - So only finitely many `G_k` are LEF.
- *Split host.*
  - `d(gh) = d(g) + ḡ·d(h)`, since paths concatenate. `d` is well defined modulo `B_1` because `T_h × T_v` is
    simply connected.
  - On `Λ_v`, `d` is the Hurewicz map into `H_1(X_Q) = Z_1/B_1 <= C_1/B_1`. So its kernel is `[Λ_v, Λ_v]`, and `G_2`
    embeds.

**Item 3.** This is the contrapositive of item 2. The open status of amenable-by-sofic permanence is recalled through
`binary-jacobson-weak-sofic-status-proof` (Arzhantseva–Berlai–Finn-Sell–Glebsky §4.4), which was not re-read here.
The claim asserts only the forward implication, and says so.

## 3.2 `radu-horizontal-projection-kills-delta-squared`: PASS

**The square table from `(RE1)`.**
- *Rewriting.* Each relator `hvh'v'` with involutive letters gives `hv = v'h'`: `axax` gives `ax = xa`, and
  `azbz` gives `az = zb` and `bz = za`. Likewise `bycy` gives `by = yc` and `cy = yb`, and `cxcz` gives `cx = zc`
  and `cz = xc`.
- *The table.* This reproduces all nine pairs of the route.

**Transducers.**
- *Rule.* `vh = h'v'` inverts `hv = v'h'`. From the table: `y` sends `a, b, c` to `a, c, b` and stays `y`. `x` fixes
  `a, b` and turns into `z` on reading `c`. `z` swaps `a, b` and turns into `x` on reading `c`.
- *Reduced words.* The outputs are reduced words. `y` applies a letter permutation, and `x, z` swap `a ↔ b` blockwise
  while `c` separates the blocks.
- *Consequence.* On `T_h`, `xz` swaps `a ↔ b` in every `c`-block, so it is the global substitution, and `(xz)^2` acts
  trivially.

**Kernel.**
- `Λ_v <= V` is normal.
- By Kurosh, a finite subgroup of `C_2 * C_2 * C_2` is conjugate into a factor, and `x, y, z` each move a vertex. So
  `Λ_v` is torsion-free, hence free.
- It contains `(xz)^4`, `u = y(xz)^2y` and `[u, xz]`.

**The level data.** The artifact output lists orders `6, 48, 192, 1536, …`, with `xz` of order 2 at every level, and
`(xz)^2` among the trivial words. This is consistent with the transducer computation.

## 3.3 Imports, against the sources

- **Cordeiro, arXiv:1608.05608v2.**
  - *p. 3.* Definition 2.1 (Ozawa's `(K,ε)`-almost morphisms into `[[N]]`, with trace condition (iii)) and
    Theorem 2.2, verbatim.
  - *p. 4.* The Remark on increasing unions.
  - *p. 6.* Proposition 3.2 (a) and (b), verbatim ("If R is sofic and A ⊆ X is any (non-null) subset, then R|A is
    sofic").
  - *p. 7.* Theorem 3.4, verbatim, including "(e.g. R is ergodic)".
  - *p. 8.* Corollary 3.5 and Theorem 3.6, verbatim.
  - *p. 5.* The Remark saying this description agrees with a sofic embedding of `vN(R)` in the sense of reference
    [11]. This matches the node.
- **Păunescu, arXiv:1002.0605v5.**
  - *p. 2.* Definitions 1.3 and 1.4, verbatim.
  - *p. 7.* Proposition 1.15, verbatim ("Let α be a free action. Then E_α is a sofic equivalence relation if and only
    if α is a sofic action.").
  - *p. 13.* The opening sentence of Section 3 ("The goal would be to prove that every (free) action of a sofic group
    is sofic. While this remains open…"), Theorem 3.1 and Definition 3.2, verbatim.
  - *p. 14.* Proposition 3.4, verbatim.
  - *p. 15.* Corollary 3.7, verbatim.
  - *p. 16.* Theorem 3.9 and its witness `Z *_((2,3)Z) Z`, verbatim.
- **Popa, arXiv:math/0512646v8, p. 4.** Theorem 0.1, the definition of "Polish group of finite type", and "Countable
  discrete groups and separable compact groups are of finite type", all verbatim as quoted.
  - The node's first paragraph is a special case of Theorem 0.1: a normal `H` is w-normal, relative (T) of `(G,H)` is
    rigidity of `H`, and a closed subgroup of the unitary group of a separable II_1 factor is of finite type.
  - The journal numbering (Invent. Math. 170) was not compared.
- **Burger–Mozes, *Lattices in product of trees*, Publ. IHÉS 92 (2000)** (Numdam scan; PDF page = journal page − 149).
  - *p. 178, §5.*
    - "(1) U(F)^+ = U(F)^(∞) is of index 2 in U(F) and simple. (2) U(F)^+ is locally ∞-transitive."
    - Proposition 5.2: `(a_h, a_v) ∈ {(0,0), (d_h − 1, d_v − 1)}`; "(2) … the lattice Γ is irreducible and
      Γ < U(P_h)×U(P_v) has dense projections".
  - *p. 184.* Proposition 6.1 (3a), verbatim.
  - *p. 187.* Theorems 6.3–6.5 and their proofs, verbatim ("argue as in Theorem 6.4").
  - **Item 5 of the node** combines Theorem 6.5 with Proposition 6.1 (3a) and Proposition 5.2 (2).
    - `^(1)X = A_(13,17) ⊠ A_(13,17)` has a non-residually-finite fundamental group, so `X` is irreducible.
    - `d_h > 2·^(0)d_h` with even permutations gives `P_h = A_(d_h)`, which is 2-transitive with simple non-abelian
      point stabilizer.
    - So dense projections follow. The derivation is correct.
    - The sentence "reducible lattices are commensurable with products of free groups" (p. 152) was not re-read here.

---
rg: 2
id: small-degree-bmw-parity-kernels-not-left-orderable-proof
kind: route
title: Exhaustive enumeration of complete one-vertex VH data, automaton finiteness certificates for the reducible classes and positive-cone SAT refutations for the rest
target: small-degree-irreducible-bmw-parity-kernels-not-left-orderable
requires: []
artifacts:
  - experiments/bmw-census-left-orders-2026-09-17/README.md
  - experiments/bmw-census-left-orders-2026-09-17/vh_enum.py
  - experiments/bmw-census-left-orders-2026-09-17/crosscheck_33.py
  - experiments/bmw-census-left-orders-2026-09-17/lo_census.py
  - experiments/bmw-census-left-orders-2026-09-17/selfcheck.py
  - experiments/bmw-census-left-orders-2026-09-17/identify.py
  - experiments/bmw-census-left-orders-2026-09-17/summarize.py
---

Scripts are in `experiments/bmw-census-left-orders-2026-09-17/`. Every step below is either
elementary or a finite computation performed by a named script.

## 1. Data

**Letters.**
- Let `A = {0,...,m-1}` carry an involution `ι_A` with `p_A` transposed pairs `(0,1),(2,3),...`
  and `m - 2p_A` fixed points. Define `B`, `ι_B`, `p_B` the same way.
- A fixed letter is a generator of order 2. A transposed pair is a generator and its inverse.

**Datum.** A datum is a bijection `SQ : A × B → B × A`, written `SQ(h,v) = (v',h')` and read
`h v = v' h'`, closed under the Klein orbit of the square
`(h,v) ↦ (v',h')`, `(ι_A h', ι_B v') ↦ (ι_B v, ι_A h)`, `(h', ι_B v) ↦ (ι_B v', h)`,
`(ι_A h, v') ↦ (v, ι_A h')`. These are the four corners at which a geometric square `h v v'^-1 h'^-1`
can be read.

**The group.** Set
`Γ = ⟨A ∪ B | c·ι(c) = 1, h v = SQ(h,v)⟩`.

**Why every BMW group arises this way.** Let `Γ ≤ Aut(T_m) × Aut(T_n)` act simply transitively on
vertices. Take as letters the elements carrying the base vertex to its horizontal and vertical
neighbours. Each geometric square at the base vertex gives one square relation, and the link
condition (link `K_{m,n}`, since the universal cover is `T_m × T_n`) is exactly that `SQ` is a
bijection. Conversely, a datum gives a one-vertex complete VH complex with universal cover
`T_m × T_n` (Burger–Mozes–Wise; see Rattaggi's thesis, §1). Injectivity of `SQ` is forced by
unique normal forms (§2), so enumerating bijections loses nothing.

## 2. Normal forms

**The rewriting system.** It has two kinds of rule:
- cancellation `c ι(c) → 1`;
- `h v → v' h'` whenever `SQ(h,v) = (v',h')`.

**Termination.** Cancellation shortens the word. The second rule keeps the length and strictly
decreases the number of pairs (horizontal letter, later vertical letter).

**Local confluence.** The overlaps are:
- `c ι(c) c`, which is trivially joinable;
- `h ι_A(h) v`;
- `h v ι_B(v)`.

Two swap left-hand sides cannot overlap. `VH.confluence()` checks that the last two overlaps join,
for every `(h,v)` of every datum. They join because of the Klein-orbit closure.

**Consequence.** By Newman's lemma every element has a unique normal form `(reduced vertical
word)(reduced horizontal word)`.

**The multiplication.** `VH.mul` computes this normal form directly: it pushes each vertical letter
of the right factor leftward through the horizontal word, then reduces.

**Check.** `selfcheck.py` verifies, on every class, that the critical pairs join and that `mul`
agrees with the rewriting normal form on 40 random pairs of words.

## 3. The parity kernel

**Definition.** The relations preserve horizontal length mod 2 and vertical length mod 2, so
`Γ → (Z/2)^2` is a homomorphism. `Γ^+` is its kernel. On normal forms it is "both lengths even",
which is how `lo_sat` selects `K = Γ^+ ∩ B_R`.

**`Γ^+` is torsion-free.**
- A finite-order element fixes a point of the CAT(0) space `T_m × T_n`.
- Vertex stabilizers are trivial, so a nontrivial such element fixes the midpoint of an edge or
  the centre of a square, and maps that cell to itself.
- Elements of `Γ^+` preserve the bipartition of each tree, so they cannot invert an edge or
  rotate a square. Hence such an element fixes a vertex and is trivial.

The script also asserts `g^{-1} ≠ g` for every `g ∈ K`.

## 4. The SAT lemma

**Lemma.** If a group `K` is left-orderable with positive cone `P`, then for every finite set
`S ⊆ K \ {1}` closed under inverses, the assignment `p_g = [g ∈ P]` satisfies:
- `p_g ⊕ p_{g^{-1}}` for `g ∈ S`;
- `¬p_g ∨ ¬p_h ∨ p_{gh}` for `g, h, gh ∈ S`;
- `¬p_g ∨ ¬p_h` for `g, h ∈ S` with `gh = 1`.

**Consequence.** An UNSAT instance on any subset of these clauses proves that `K` is not
left-orderable.

**Instances.** `lo_sat(G, R, short)` uses `S = K ∩ B_R \ {1}`, with all products in the ball
(`short = None`) or those with one factor of length at most `short`. `solve` requires CaDiCaL 1.5.3
and Glucose 4 to return the same answer.

## 5. The reducibility certificate

**Setup.** Let `F_A = ⟨A⟩ ≤ Γ`. By §2 the elements `v·1` (reduced vertical words) are the
vertices of the vertical tree through the base vertex, and left multiplication by `h` sends `v` to
the vertical part of `h v`. This is the action of `F_A` on `T_B` given by the Mealy automaton with
states `A`, inputs `B` and transition `SQ`.

**The computation.** `finite_image(G, True)` builds `E_k`, the set of automorphisms of `T_B` given
by words of length exactly `k`. Equality is decided by Moore minimization of the combined automaton.
- `E_k ⊆ E_{k+2}`, since `a ι(a) = 1`.
- If `E_k = E_{k-2}`, then `E_{k+1} = E_k·A = E_{k-2}·A = E_{k-1}`, so the image is `E_k ∪ E_{k-1}`,
  which is finite.
- Otherwise the function returns `None` once the minimal automaton has more than 4000 states.

`finite_image(G, False)` does the same for `⟨B⟩` acting on `T_A` through the inverse corner map.

**Lemma.** If both images are finite, `Γ` is reducible.

*Proof.* Let `N_A = F_A ∩ ker(Γ → Aut T_B)` and `N_B = F_B ∩ ker(Γ → Aut T_A)`. These have finite
index in `F_A` and `F_B`.
- `N_A` acts trivially on `T_B` and `N_B` acts trivially on `T_A`. So `[N_A, N_B]` acts trivially
  on `T_m × T_n`, hence is trivial, since `Γ` acts freely on vertices.
- `N_A ∩ N_B = 1` for the same reason.
- `F_A x_0` is the horizontal tree through the base vertex, which projects bijectively onto
  `V(T_A)`. So `F_A` acts simply transitively on `V(T_A)`, and `N_A` has `[F_A : N_A]` orbits there.
  Likewise `N_B` has finitely many orbits on `V(T_B)`.
- `H = N_A × N_B` acts factorwise, since each factor is trivial on the other tree. So its orbits
  on `V(T_A) × V(T_B)` are products of orbits, finitely many.
- `Γ` acts freely and transitively on vertices, so `[Γ : H]` equals the number of `H`-orbits, which
  is finite. Take `Λ_1 = N_A`, `Λ_2 = N_B`. ∎

## 6. Soundness of the census

**Enumeration.** `vh_enum.enumerate_data` backtracks over corners. For each unassigned corner it
tries every free target and imposes the whole Klein orbit consistently and injectively. So it
produces every datum exactly once. `crosscheck_33.py` confirms the counts 478, 106 and 26 in degree
(3,3) against all `9!` bijections.

**Symmetries.** The census identifies data under three operations:
- relabelling letters by permutations commuting with `ι`: an isomorphism;
- reversal `SQ_r(h, ι_B v') = (ι_B v, h')`: the datum of the presentation read backwards, so
  `Γ_r ≅ Γ^op ≅ Γ` via `g ↦ g^{-1}`, which maps `Γ^+` onto `Γ^+`;
- factor swap when the patterns agree: an isomorphism exchanging the factors.

Each of these preserves `Γ^+` up to isomorphism, and preserves irreducibility.

**Completeness check.** `census` asserts that the orbit sizes sum to the raw count, so every datum
lies in exactly one class.

## 7. Assembly

**Runs.** `run_all.sh` runs `lo_census.py` on every class. Each record contains:
- `finH` and `finV`, the certified image orders or `None`;
- the SAT outcomes. Radius 4 with all products is always run. If an image is not certified finite,
  it is followed by radius 6 with one factor of length at most 4, then radius 6 with all
  products, then radius 8 with one factor of length at most 2, stopping at the first UNSAT.

**Outcome.** `summarize.py` aggregates the outputs. Every class with `finH = None` or
`finV = None` stopped UNSAT at radius 4 or at radius 6 with short factors of length at most 4. No
class has exactly one image certified finite.

**Proof of the theorem.** Let `Γ` be irreducible of the stated degree and pattern.
- `Γ` is isomorphic to a datum in some class, by §1 and §6.
- By §5 the class is not certified reducible.
- By the outcome above, `Γ^+` has an UNSAT positive-cone instance, so by §4 it is not
  left-orderable. ∎

**Calibration.** `identify.py` maps Radu's `Γ_R` (relators `axax, ayay, azbz, bxbx, bycy, cxcz`,
all letters involutions) and Janzen–Wise (`axay, aXbY, aYBX, bxBY`) into the census. They are
classes `30_30#10` and `42_42#98`, both not certified finite and both UNSAT, which reproduces
`exotic-c2-tilde-simple-kazhdan-lattices-are-not-left-orderable`. The commuting product datum
`SQ(h,v) = (v,h)` is certified reducible (images of order 1) with a SAT radius-4 instance.

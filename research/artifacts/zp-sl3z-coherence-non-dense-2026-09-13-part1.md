# SL_3(Z) coherence, part 1: every non-Zariski-dense subgroup is coherent

Lane z3-04-sl3z-coherent, 2026-09-13. Unreviewed.

Problem (M. C. B. Zaremsky, *Some open problems*, version of July 12, 2026, Section 3,
Problem 4, verbatim): "Is SL3(Z) coherent? (Meaning every finitely generated subgroup is
finitely presented.) (Famous problem of Serre.)"

Scope. This part proves that a subgroup of SL_3(Z) whose Zariski closure is not all of
SL_3 is coherent, and that coherence passes through actions on trees with virtually
solvable edge stabilizers. Part 2 records what known incoherence constructions would need
inside SL_3(Z). Nothing here decides Problem 3.4: finitely generated Zariski-dense
subgroups of infinite index are not covered.

Conventions. Zariski closures are taken in SL_3(C). A group is *Noetherian* if all of its
subgroups are finitely generated (fg). Coherence passes to subgroups, since a fg subgroup
of a subgroup is a fg subgroup of the group.

## 1. Closure lemmas

**Lemma 1.1 (polycyclic-by-coherent).** If 1 → N → G → Q → 1 is exact with N
polycyclic-by-finite and Q coherent, then G is coherent.

*Proof.* Let K ≤ G be fg. Then K ∩ N is polycyclic-by-finite, hence finitely presented
(fp). The quotient K/(K ∩ N) ≅ KN/N ≤ Q is fg, hence fp because Q is coherent. An
extension of an fp group by an fp group is fp (P. Hall). So K is fp. ∎

**Lemma 1.2 (standard coherent classes).**
(a) Virtually free groups are coherent.
(b) Every discrete subgroup of a Lie group L that contains PSL_2(R) as a subgroup of
finite index is coherent.
(c) Polycyclic-by-finite groups are coherent.

*Proof.* (a) Let F ≤ G be free of finite index and K ≤ G fg. Then K ∩ F has finite index
in K, so it is a fg free group, and a finite extension of an fp group is fp.
(b) Let D ≤ L be discrete and K ≤ D fg. Then K_0 = K ∩ PSL_2(R) has finite index in K, so
it is a fg Fuchsian group. Fg Fuchsian groups are geometrically finite (Siegel), so they
have finite-sided fundamental polygons and finite presentations. Hence K is fp.
(c) All subgroups of a polycyclic-by-finite group are polycyclic-by-finite, hence fp. ∎

**Theorem 1.3 (trees with Noetherian edge stabilizers).** Let G act on a simplicial tree
without inversions, with coherent vertex stabilizers and Noetherian edge stabilizers.
Then G is coherent. In particular, the fundamental group of a graph of groups with
coherent vertex groups and Noetherian edge groups is coherent.

*Proof.* Let K ≤ G be fg.

*Elliptic case.* If every element of K fixes a vertex, then K fixes a vertex (Serre,
*Trees*, I.6.5), so K lies in a coherent vertex stabilizer and is fp.

*Hyperbolic case.* Otherwise K has a minimal invariant subtree T_K, and T_K/K is a finite
graph because K is fg (Bass, "Covering theory for graphs of groups", 1993, Prop. 7.9).
Bass–Serre theory writes K as the fundamental group of a finite graph of groups with vertex
groups K_v = Stab_K(v) and edge groups K_e = Stab_K(e). Each K_e is a subgroup of an edge
stabilizer of G, so it is fg.

*The vertex groups are fg.* Collapse the finite graph one edge at a time. At each step the
current group is an amalgam A *_C B or an HNN extension A *_C with C fg. Suppose A *_C B
is fg. A finite generating set involves finitely many letters S_A ⊆ A and S_B ⊆ B. Put
A_0 = ⟨S_A, C⟩ and B_0 = ⟨S_B, C⟩. The subamalgam A_0 *_C B_0 embeds in A *_C B (normal
forms, with transversals of C in A_0 and B_0 extended to transversals in A and B), and its
image contains the generators, so it is everything. An element a ∈ A has a normal form of
length ≤ 1 in A *_C B. By uniqueness of normal forms, the same element read in the
subamalgam also has length ≤ 1, and it lies in A, so it lies in A_0. Thus A = A_0 is fg,
and likewise B. For an HNN extension A *_C with fg C, the same argument with
A_0 = ⟨S_A, C, t^{-1}Ct⟩ shows A is fg. Induction down the collapse shows every K_v is fg.

*Finite presentation.* Each K_v is a fg subgroup of a coherent vertex stabilizer, so it is
fp. The fundamental group of a finite graph of groups with fp vertex groups and fg edge
groups is fp: take the vertex presentations, one stable letter per edge off a maximal tree,
and one relation per generator of each edge group. So K is fp. ∎

## 2. Parabolic subgroups

**Proposition 2.1.** Let P_1 = {g ∈ SL_3(Z) : g e_1 = ±e_1} and P_2 be the stabilizer in
SL_3(Z) of the plane Qe_1 + Qe_2. A subgroup of SL_3(Z) preserving a rational line (resp.
rational plane) of Q³ is conjugate in SL_3(Z) into P_1 (resp. P_2). Both P_1 and P_2 are
coherent.

*Proof.* A rational line meets Z³ in Zv for a primitive vector v. A rational plane W meets
Z³ in a rank-2 direct summand. A basis of Zv, or of W ∩ Z³, extends to a basis of Z³, and
changing the sign of the last basis vector puts the change of basis in SL_3(Z). So the
stabilizer is conjugate to P_1 or P_2.

Write elements of P_1 as block matrices [[a, x], [0, B]] with a ∈ {±1}, B ∈ GL_2(Z),
a·det B = 1 and x ∈ Z^{1×2}. The map g ↦ B is a surjection P_1 → GL_2(Z) whose kernel
{[[1, x], [0, I]]} is isomorphic to Z². GL_2(Z) is virtually free, so it is coherent by
Lemma 1.2(a). Lemma 1.1 then shows P_1 is coherent. The same argument applies to P_2,
whose elements are [[B, y], [0, a]]. ∎

**Remark 2.2 (a dead lead).** Every group Z² ⋊ F with F ≤ GL_2(Z) is coherent, and in
particular Z² ⋊ F_2 with F_2 a free subgroup of SL_2(Z). These are the affine groups inside
SL_3(Z). More generally Z^n ⋊ Q is coherent whenever Q is coherent, by Lemma 1.1. So
semidirect products with an abelian normal subgroup cannot witness incoherence. The
Borel subgroup is polycyclic-by-finite.

## 3. Non-dense subgroups

**Theorem 3.1 (classification).** Let H ≤ SL_3(Z) have Zariski closure Ḡ ≠ SL_3. Then
at least one of the following holds.
- (V) H is virtually polycyclic.
- (F) There is a rational ternary quadratic form q, indefinite over R, with H ≤ SO(q)(Q).
  Then H is a discrete subgroup of SO(q)(R) ≅ SO(2,1).
- (P) H preserves a rational line or a rational plane of Q³, so H is conjugate in SL_3(Z)
  into P_1 or P_2.

*Proof.* Let G° be the identity component of Ḡ. Both Ḡ and G° are defined over Q because
H ⊆ SL_3(Q). Also [H : H ∩ G°] ≤ [Ḡ : G°] < ∞, and H normalizes G°.

*Solvable case.* If G° is solvable, then H ∩ G° is a solvable subgroup of GL_3(Z), hence
polycyclic (Mal'cev), and H is virtually polycyclic. This is (V).

*Type of the semisimple part.* Suppose G° is not solvable, and let S be a Levi subgroup,
a nontrivial connected semisimple subgroup of SL_3 acting faithfully on C³. The only
simple types with a nontrivial representation of dimension ≤ 3 are A_1 (dimensions 2 and
3) and A_2 (dimension 3). A product of two simple factors needs dimension ≥ 4, since each
factor acts nontrivially. Type A_2 gives S = SL_3, so Ḡ = SL_3, which is excluded. So S
has type A_1, and C³ as an S-module is either irreducible (S = SO(q_0) for the invariant
form q_0) or 2 ⊕ 1.

*Irreducible case.* Suppose G° acts irreducibly on C³.
- The unipotent radical R_u(G°) is trivial: its fixed space in C³ is nonzero (Kolchin)
  and G°-invariant.
- So G° is reductive, G° = Z(G°)°·S. The torus Z(G°)° centralizes the irreducible S, so it
  is scalar, hence trivial in SL_3. Thus G° = S = SO(q) for a ternary form q.
- The form q is unique up to scalars. Its Galois conjugates are again invariant, so q can
  be taken rational.
- The normalizer of SO(q) in SL_3 is SO(q) × μ_3, because the automorphisms of PSL_2 are
  inner and the centralizer is μ_3. Nontrivial scalar cube roots of unity are not rational,
  so H ≤ SO(q)(Q).
- H is discrete in SL_3(R), hence in SO(q)(R). If q is definite, SO(q)(R) is compact and H
  is finite, which is (V). Otherwise we are in (F).

*Reducible case.* Suppose G° is reducible and not solvable.
- Its composition factors on C³ have dimensions 2 and 1. If all factors had dimension 1,
  G° would lie in a Borel subgroup and be solvable.
- G° has at most one invariant plane: two distinct invariant planes meet in an invariant
  line and give three composition factors of dimension 1.
- G° has at most one invariant line: two invariant lines span an invariant plane with two
  factors of dimension 1.
- Since G° is reducible, it has an invariant subspace U, the unique one of its dimension
  d ∈ {1, 2}. The G°-invariant d-dimensional subspaces form a closed subvariety of the
  Grassmannian defined over Q; it is a single point, so that point is rational, and U is
  defined over Q.
- For h ∈ H, hU is G°-invariant because H normalizes G°. So hU = U, and H preserves the
  rational subspace U. This is (P); Proposition 2.1 gives the conjugation. ∎

**Theorem 3.2.** Every subgroup of SL_3(Z) that is not Zariski-dense in SL_3 is coherent.

*Proof.* Case (V): Lemma 1.2(c). Case (F): SO(2,1) contains its identity component
≅ PSL_2(R) with index 2 and H is discrete, so Lemma 1.2(b) applies. Case (P): H is
conjugate into P_1 or P_2, which are coherent (Proposition 2.1), and subgroups of coherent
groups are coherent. ∎

## 4. The hierarchy class and the shape of a witness

Let 𝓗_0 be the set of subgroups of SL_3(Z) that are not Zariski-dense. For k ≥ 0, let
𝓗_{k+1} be the set of subgroups H ≤ SL_3(Z) that act on a tree without inversions with
vertex stabilizers in 𝓗_k and virtually solvable edge stabilizers. Put 𝓗 = ∪_k 𝓗_k.

**Corollary 4.1.** Every group in 𝓗 is coherent.

*Proof.* Induction on k. The base 𝓗_0 is Theorem 3.2. Virtually solvable subgroups of
SL_3(Z) are polycyclic-by-finite (Mal'cev), hence Noetherian, so Theorem 1.3 carries
coherence from 𝓗_k to 𝓗_{k+1}. ∎

Examples of groups in 𝓗:
- free products of non-dense subgroups, such as Zariski-dense thin subgroups obtained by
  ping-pong from pieces of parabolic subgroups;
- amalgams and HNN extensions of such subgroups over unipotent or diagonalizable
  subgroups;
- iterates of these constructions.

**Corollary 4.2 (shape of a witness).** Let K ≤ SL_3(Z) be fg and not fp. Then:
- (i) K is Zariski-dense in SL_3 (Theorem 3.2);
- (ii) [SL_3(Z) : K] = ∞, because SL_3(Z) is fp and finite-index subgroups of fp groups are
  fp (Reidemeister–Schreier). So K is thin;
- (iii) K has no infinite normal virtually solvable subgroup. The identity component of the
  closure of such a subgroup would be a connected solvable subgroup normalized by
  K̄ = SL_3, hence trivial, so the subgroup would be finite;
- (iv) K ∉ 𝓗 (Corollary 4.1);
- (v) K is not the fundamental group of a 3-manifold (Scott's core theorem) and not a
  free-by-cyclic group (Feighn–Handel, *Annals of Math.* 149, 1999).

So Problem 3.4 has a positive answer if and only if every fg Zariski-dense subgroup of
infinite index in SL_3(Z) outside 𝓗 is finitely presented.

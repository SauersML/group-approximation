---
rg: 2
id: simple-vertex-triangles-are-universal-for-triangle-vtf-proof
kind: route
title: Free actions of the edge-generated core extend to free actions of any finite overgroups of its vertex groups
target: simple-vertex-triangles-are-universal-for-triangle-vtf
requires: [simple-vertex-groups-vtf-iff-some-finite-quotient, finite-torsion-carrier-virtual-torsionfree-criterion]
---

Notation as in the claim: `T` has vertex groups `A_v`, core vertex groups
`B_v = <E_e, E_e'>`, colimits `Λ = Λ(T)` and `Λ° = Λ(T°)`.

**(U1).** The edges of `Γ_v(T)` are the elements `x in A_v` (the face group is trivial),
and `x` joins `x E_e` to `x E_e'`. Both ends lie in the left coset `x B_v`. So the
subgraph on the cosets contained in `a B_v` is a union of components, and left
multiplication by `a^{-1}` identifies it with `Γ_v(T°)`. There are `[A_v : B_v]` such
pieces, and the girths agree.

**(U2).** For a group `H`, a homomorphism from the pushout `P` of `Λ° <- B_v -> A_v` to
`H` is a homomorphism `f° : Λ° -> H` together with homomorphisms `f_v : A_v -> H` such
that `f°` and `f_v` agree on `B_v`. Given homomorphisms `f_v` that agree on the two
images of every `E_e`, the restrictions `f_v|B_v` agree on every `E_e`. So they induce
a unique `f°` on `Λ° = colim T°`. Conversely, a homomorphism from `P` gives `f_v` that
agree on every `E_e`, because `E_e <= B_v`. These bijections are natural in `H`, so
`P ≅ Λ`. No injectivity of `B_v -> Λ°` is used.

**Extension lemma.** Let `B <= A` be finite groups. Let `Ω` be a finite free `B`-set
whose number of orbits is divisible by `[A:B]`. Then `Ω` carries a free `A`-action
restricting to the given `B`-action.

*Proof.* A free `B`-set is determined up to isomorphism by its number of orbits. Put
`m = |Ω|/|A|`, an integer by hypothesis. The free `A`-set `A × {1..m}` restricted to `B`
is free with `m [A:B] = |Ω|/|B|` orbits. Choose a `B`-equivariant bijection with `Ω`
and transport the `A`-action.

**(U3), <=.** Let `π : Λ° -> Q` be finite and injective on every `B_v`. Let `k` be a
common multiple of the three indices `[A_v : B_v]`, and put `Ω = Q × {1..k}`, with `Λ°`
acting by left multiplication through `π` on the first factor.
- Each `B_v` acts freely, with `k|Q|/|B_v|` orbits, a multiple of `[A_v : B_v]`.
- By the lemma each `B_v`-action extends to a free `A_v`-action.
- An edge group `E_e` at `v` and `w` acts through `B_v` and through `B_w` by the same
  `Λ°`-action. So the three `A_v`-actions agree on every `E_e`, and by the universal
  property of the colimit they define an action of `Λ` on `Ω`.
The action is free on each `A_v`, so the image of `Λ` in `Sym(Ω)` is a finite quotient
injective on every `A_v`.

**(U3), =>.** Let `ψ : Λ -> Q` be finite and injective on every `A_v`. Compose with the
canonical map `Λ° -> Λ` of (U2). On `B_v` this composite is `B_v -> A_v -> Q`, which is
injective.

**(U4).** Let the `A_v` be simple and `φ : Λ -> Q` a homomorphism, not injective on
some `A_i`. Then `φ(A_i) = 1`.
- For an edge `ij`, `φ` kills `E_ij`, a nontrivial subgroup of `A_j`. So `φ|A_j` is not
  injective, and `φ(A_j) = 1`.
- Around the triangle `φ` kills all three vertex groups, which generate `Λ`, so `φ = 1`.
So every nontrivial homomorphism is injective on every `A_v`. This is the Lemma of
`simple-vertex-groups-vtf-iff-some-finite-quotient`, checked here at the level of the
diagram. With (U3) this gives the first equivalence.

Now let `T°` be hyperbolic. Caprace–Conder–Kaluba–Witzel, arXiv:2011.09276, Theorem 3.1
(read at source 2026-09-13) applies to `T°`: trivial face group, each `B_v` generated
by the images of its two edge groups, and `Σ 1/m_v < 1`. It gives:
- (i) `Λ°` acts on a CAT(0) 2-complex with vertex stabilizers isomorphic to the `B_v`,
  so each `B_v -> Λ°` is injective;
- (ii) every finite subgroup of `Λ°` is conjugate into some `B_v`;
- (v) `Λ°` is non-elementary hyperbolic.
By `finite-torsion-carrier-virtual-torsionfree-criterion` (1 <=> 4), with carriers
`B_v`, `Λ°` is virtually torsion-free iff it has a finite quotient injective on every
`B_v`.

Since `B_v -> Λ°` and `B_v -> A_v` are injective, the pushout (U2) is the fundamental
group of a finite graph of groups: centre `Λ°`, leaves `A_v`, edge groups `B_v`.
- A finite subgroup of `Λ` acts on the Bass–Serre tree without inversions and fixes a
  vertex. So it is conjugate into some `A_v`, or into `Λ°` and then by (ii) into some
  `B_v <= A_v`.
- The fundamental group of a finite graph of groups with hyperbolic vertex groups and
  finite edge groups is hyperbolic (Bestvina–Feighn, *A combination theorem for
  negatively curved groups*, J. Differential Geom. 35 (1992), case of finite edge
  groups). So `Λ` is hyperbolic. Alternatively, the development of `T` is a tree of
  copies of the CAT(−1) development of `T°` glued at vertices.

**(U5), (a) => (b).** Let `T°` be as in (a), with `Λ°` not virtually torsion-free.
- `|B_v| >= 4`, since `B_v` contains two nontrivial subgroups meeting trivially. So
  `n_v = |B_v| + 2 >= 6`, and `Alt(n_v)` is simple.
- `B_v` embeds in `Sym(|B_v|)` by the regular representation, and `Sym(m)` embeds in
  `Alt(m+2)` by `σ ↦ σ · (m+1, m+2)^{[σ odd]}`.
- Let `T` have vertex groups `A_v = Alt(n_v)` and the composite edge injections. The
  two edge subgroups at a vertex still meet trivially, and the core of `T` is `T°`.
`T` is hyperbolic by (U1). `Λ°` has no finite quotient injective on every `B_v` (the
criterion above), so by (U4) `Λ(T)` has no nontrivial finite quotient. It is infinite,
since it contains `Λ°`.

**(U5), (b) => (a).** Let `T` be as in (b), with `Λ(T)` quotientless. Its core `T°` has
trivial face group, nontrivial edge groups and generated vertex groups, and it is
hyperbolic by (U1). By (U4), `Λ°` has no finite quotient injective on every `B_v`, so
it is not virtually torsion-free.

**(U6).** Let `E_e = <t_e>` have order 2 for all three edges.
- At `v`, `t_e != t_e'` because the face group is trivial. So `B_v` is dihedral of order
  `2 m_v`, where `m_v >= 2` is the order of `t_e t_e'`, with presentation
  `<t_e, t_e' | t_e^2, t_e'^2, (t_e t_e')^{m_v}>`.
- Its coset graph with respect to `<t_e>, <t_e'>` is a single `2 m_v`-cycle, so this
  `m_v` is the half-girth.
- Hence `Λ° = < t_12, t_13, t_23 | t_e^2, (t_e t_e')^{m_v} >` is a Coxeter group `W`.
`W` is linear over `R`, by Tits' faithful geometric representation (Bourbaki, *Lie
groups and Lie algebras*, Ch. V §4). By Selberg's lemma it has a torsion-free
finite-index normal subgroup `N`. The special subgroup `<t_e, t_e'>` of `W` is the
dihedral group of order `2 m_v` (standard for special subgroups; Humphreys, *Reflection
groups and Coxeter groups*, §5.5). So `B_v -> W` is injective and `W/N` is injective on
every `B_v`. By (U3) <=, `Λ(T)` has a finite quotient injective on every `A_v`. No
curvature hypothesis was used.

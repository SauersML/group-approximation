# Hyperbolic covers over quotient-free groups: the kernel is the whole problem

Lane `hyperbolic-no-finite-quotient`, 2026-09-12. Target:
`non-residually-finite-hyperbolic-group` (Gromov's question), attacked from
the construction side. The plan was to build a hyperbolic group with no
nontrivial finite quotient from a Belegradek--Osin cover of a quotient-free
group such as `R^x = L_(F_2)(1,2)^x`.

**Outcome.** No counterexample was built. What follows proves exactly where
the construction circles back.
- Over a perfect quotient with no finite quotients and trivial Schur
  multiplier, every finite image of the kernel splits off as a direct factor.
  So the extension has exactly the finite quotients, the profinite completion
  and (for torsion-free hyperbolic covers of `R^x`) the residual finiteness of
  its kernel.
- Over any quotient without finite quotients, a quotient-free cover forces a
  Kazhdan kernel to contain a finite-index subgroup with no finite quotients.

The special properties of `R^x` (simplicity, acyclicity, nonsoficity)
contribute nothing.

## 1. The extension lemma

Let `1 -> N -> G -> Q -> 1` be exact with `N` finitely generated and `Q`
without nontrivial finite quotient. Call `K <= N` admissible if `K ◁ G` and
`[N:K] < ∞`.

**Step 1 (conjugation is inner).** Fix an admissible `K`. Conjugation gives
`ρ : G -> Aut(N/K)`. The composite `G -> Out(N/K)` kills `N`, because `N`
acts by inner automorphisms, so it factors through `Q`. Its image is finite,
so it is trivial. Hence `ρ(G) = Inn(N/K)`. Put `C = ker(G/K -> Inn(N/K))`,
the centralizer of `N/K` in `G/K`, and `Z = Z(N/K)`. Then:
- `C ∩ N/K = Z`;
- `C·(N/K) = G/K`, because `N/K -> Inn(N/K)` is onto;
- `C/Z ≅ (G/K)/(N/K) ≅ Q`, and `Z` is central in `C`.

**Step 2 (splitting; `Q` perfect, `H_2(Q;Z) = 0`).** For the finite abelian
group `Z` with trivial action, the universal coefficient theorem gives
`H^2(Q; Z) = Hom(H_2(Q), Z) ⊕ Ext(H_1(Q), Z) = 0`. So the central extension
`1 -> Z -> C -> Q -> 1` is a direct product, `C = S x Z` with `S ≅ Q`.
- Since `Q` is perfect, `[C,C] = S`. This is characteristic in `C`, which is
  normal in `G/K`, so `S ◁ G/K`.
- `S ∩ N/K ⊆ S ∩ C ∩ N/K = S ∩ Z = 1`.
- `S·(N/K)` contains `S`, `Z` and `N/K`, hence `C·(N/K) = G/K`.

Two normal subgroups with trivial intersection that generate give
`G/K = S x N/K`.

**Step 3 (all finite quotients come from admissible `K`).** Let
`φ : G ->> F` with `F` finite. Then `φ(N) ◁ F`, and `F/φ(N)` is a finite
quotient of `Q`, so `φ(N) = F`. With `K = N ∩ ker φ`, `K` is admissible and
`F ≅ N/K`. Conversely, Step 2 projects `G/K ≅ S x N/K` onto `N/K`.

Cofinality: since `N` is finitely generated, it has finitely many subgroups
of any given finite index. So for `M ◁ N` of finite index, `{gMg^-1 : g in G}`
is finite, and the intersection of that orbit is admissible and lies in `M`.

**Step 4 (completions).** For every finite quotient `G/L`, `N -> G/L` is
onto (Step 3). The subgroups `N ∩ L` are cofinal among finite-index normal
subgroups of `N`. So the continuous map `N^ -> G^` induced by inclusion:
- has dense image, hence is onto by compactness;
- has trivial kernel.

It is an isomorphism. Intersecting `N ∩ L` over all `L` gives
`R_f(G) ∩ N = R_f(N)`. In particular `G` has a nontrivial finite quotient iff
`N` does. One direction needs only Step 3's first sentence; the other needs
Step 2.

**Step 5 (circularity, no perfectness or `H_2` assumption).** Step 1 used
only that `Q` has no finite quotients. If `G` has no nontrivial finite
quotient, then `G ->> Inn(N/K)` is trivial for each admissible `K`, so `N/K`
is abelian. Any finite quotient of `N` factors through some `N/K`, by
cofinality, so every finite quotient of `N` is abelian.

Suppose `N^ab` is finite, which holds automatically when `N` is Kazhdan.
Then `[N,N]` has finite index in `N` and is finitely generated. Let
`M ◁ [N,N]` have finite index. Its `N`-conjugates are finitely many, and
their intersection `L` is normal of finite index in `N`. `N/L` is abelian, so
`[N,N] ⊆ L ⊆ M`. Hence **`[N,N]` has no nontrivial finite quotient.**

**Step 6 (the `H_2` hypothesis is needed).** Let `Q` be perfect with no finite
quotients and `H_2(Q;Z) ->> A ≠ 0` finite. Let `U` be the universal central
extension, and `G = U/ker(H_2(Q) -> A)`. Then `1 -> A -> G -> Q -> 1` is a
perfect central extension. Any finite image `F` of `G` equals the image of
`A` (Step 3), so it is abelian, and it is perfect, so `F = 1`. The kernel `A`
has the nontrivial finite quotient `A`. So Step 2 and item 4 genuinely use
`H_2 = 0`. Step 5 is what survives without it: only central, abelian finite
images of `N` can be absorbed.

## 2. Torsion-free hyperbolic covers of the Leavitt unit group

Let `R = L_(F_2)(1,2)` and `1 -> N -> G -> R^x -> 1` with `G` torsion-free
word-hyperbolic and `N` finitely generated. The Belegradek--Osin cover
(`hyperbolic-kazhdan-cover-of-leavitt-unit-group`) is an instance: `N` is a
quotient of a torsion-free cocompact `Sp(2,1)` lattice, and `G` is
torsion-free by Corollary 1.2's "Moreover" clause.

Inputs:
- `R^x` is integrally acyclic, so it is perfect with `H_2 = 0`
  (`binary-leavitt-unit-group-integrally-acyclic`, Khanh Theorem 4.4);
- `R^x` is infinite and simple, so it has no nontrivial finite quotient
  (`binary-leavitt-unit-group-is-simple`).

§1 then gives: `G^ ≅ N^`; `G` has a nontrivial finite quotient iff `N` does;
and `R_f(G) ∩ N = R_f(N)`.

**`G` is residually finite iff `N` is.** One direction is inheritance by
subgroups. Conversely let `N` be residually finite, so `R_f(G) ∩ N = 1`, and
suppose `1 ≠ g ∈ R_f(G)`.
- **Centralizer.** `[R_f(G), N] ⊆ R_f(G) ∩ N = 1`, so `N <= C_G(g)`. In a
  torsion-free hyperbolic group the centralizer of a nontrivial element is
  infinite cyclic (standard, from Gromov; see Bridson--Haefliger, Part III.Γ;
  the exact item was not re-read).
- **`N` is not trivial.** If `N = 1`, `G ≅ R^x` would be hyperbolic, but
  `R^x` contains Thompson's `V` (`openai-nine-leaf-leavitt-configuration`), and
  `V` contains `Z^2`.
- **Contradiction.** So `N ≅ Z` is normal in `G`. The subgroup of index at
  most 2 acting trivially on `N` centralizes a generator, hence is cyclic. So
  `G` is virtually cyclic, while it maps onto `R^x ⊇ Z^2`.

## 3. What this pins down for Gromov's question

- **Leavitt covers.** A negative answer through a torsion-free hyperbolic cover
  of `R^x` is exactly a non-residually-finite kernel `N`. A quotient-free cover
  is exactly a quotient-free kernel. `N` is an infinite, infinite-index normal
  subgroup of a hyperbolic group and a quotient of the lattice. The
  Belegradek--Osin theorem controls hyperbolicity, torsion and (T) of the
  cover, and says nothing about finite images of `N`.
- **Any quotient-free `Q`.** A quotient-free hyperbolic cover with Kazhdan
  kernel forces `[N,N]` to be a finite-index subgroup of `N` without finite
  quotients. So the `rips-kernel-without-finite-quotients` target reappears one
  finite index down, whatever `Q` is. This matches the existence-level
  equivalence `rips-kernel-target-iff-hyperbolic-nonrf` at the level of one
  extension.
- **Deligne-type central trick.** Over `R^x` it is dead: every central
  extension of `R^x` splits (acyclicity). Over a quotient with nontrivial
  Schur multiplier, only central finite images of `N` can be absorbed (Step 6).
  Nonabelian finite images of `N` always survive to `G` (Step 1).

## 4. Attempts that did not produce a construction

1. **Rips source without finite quotients.** Circular: that is statement 2 of
   `hyperbolic-rf-vtf-kazhdan-equivalence`.
2. **Residually finite Kazhdan source, small cancellation doing the killing.**
   By Step 5 the needed conclusion is that every finite image of the
   small-cancellation quotient `N` of the lattice is abelian. No mechanism in
   Belegradek--Osin (suitability, torsion, relative hyperbolicity, outer
   action) constrains finite images, and none was found here.
3. **Common Kazhdan quotients.** Already on main as the three-way equivalence;
   it transports the property and does not create it.
4. **Filling one element of a lattice.** Already reduced on main to
   simple-image orders (`filling-no-finite-quotient-iff-simple-image-orders`,
   `sp21-one-element-filling-without-finite-quotients`). Not repeated here.

## 5. Sources and trust

- **Belegradek--Osin Corollary 1.2:** as imported on main, verbatim from the v4
  PDF by the reviewer lane.
- **Khanh Theorem 4.4:** as imported on main.
- **Kapovich--Wise:** already read from the primary paper
  (`kapovich-wise-rf-iff-finite-quotients-citation`). It was not re-extracted
  on MSI this session, and nothing above uses it.
- **Hyperbolic centralizer fact:** standard; not re-read from a source.
- **Status:** no novelty claimed. The lemma is elementary and likely folklore.
  Nothing is Lean-verified or independently reviewed.

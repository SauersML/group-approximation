# Is every coset system abelian after relabeling?

Lane `ex-kac-quantum-compiler`, 2026-09-13, part 5.  Node:
`coset-system-algebras-reduce-to-abelian-coset-systems` (open).  Builds on
part 4 (`relabelable-coset-systems-are-solution-group-corners`).

## 0. Why this is the decisive question for the coset route

By part 4, a relabelable coset system is a finitely presented group-algebra
corner.  A `qc`/`qa` gap on it is a nonhyperlinear group.  So the coset route
produces something beyond `non-hyperlinear-group` only if some coset system
has an algebra that is **not** the algebra of any coset system over abelian
groups.  Below: the proved reductions, and the precise point where a proof or
a counterexample has to live.

## 1. Normal form

Let `S` have fibres `K_q`, with relations `R_e = c_e D_e` on edges
`e = (q,q')`.  By Goursat, each `D_e` is determined by
- subgroups `K_1 <= K_q` and `K'_1 <= K_(q')`;
- normal subgroups `N ◁ K_1` and `N' ◁ K'_1`;
- an isomorphism `θ: K_1/N -> K'_1/N'`.

The relation then reads:

```text
s in c_1 K_1,   s' in c'_1 K'_1,   and the cells of s, s' match under the affine map induced by θ.
```

**(N1) Support fixpoint.**  In `A(S)`, `p_q^s = 0` for `s notin c_1 K_1`.
Restricting a fibre to a coset of a smaller subgroup `K_0` restricts every
Goursat relation on it to a Goursat relation: `K_0 N / N ≅ K_0/(K_0 ∩ N)`,
transported by `θ`.  Iterating restrictions reaches a fixpoint in finitely
many steps.  There each fibre is a coset of a group `K_q`, each partition is
by a normal subgroup of `K_q`, and each identification is an affine bijection
of quotient groups (isomorphism composed with translations).  Left-translating
labels makes the supports subgroups.  The algebra is unchanged.

**(N2) Holonomy pruning.**  Take a cycle of identifications that all pass
through one common section `Θ` (a quotient group).  It transports the coarse
PVM over `Θ` to itself by an affine map `h`, so `P^θ = P^(h(θ))`.  Distinct
atoms are orthogonal, so `P^θ = 0` off `Fix(h)`.
- If `x_0` is fixed, `h(x_0 y) = x_0 y` iff `y` is fixed by
  `inn_(b^(-1)) ∘ α`, where `h(x) = a α(x) b`.  So `Fix(h)` is empty or a
  coset of a subgroup.
- So pruning keeps normal form (N1), and afterwards every holonomy acts
  trivially on the supported cells.

## 2. What is proved

**(A1) One relation.**  Every single Goursat relation is relabelable (part 4,
§3).

**(A2) Two partitions of one fibre.**  For normal `N_1, N_2 ◁ K`, the natural
map `K/(N_1 ∩ N_2) -> K/N_1 x_(K/N_1N_2) K/N_2` is a bijection: it is
injective, and both sides have `|K|/|N_1 ∩ N_2|` elements.  Hence abelian
labelings of `K/N_1` and `K/N_2` that induce the same labeling of `K/N_1N_2`
extend to an abelian labeling of `K` realizing both partitions:
fibre product times a labeling of the `N_1 ∩ N_2`-cells.

**(A3) Interlocking forces abelian sections.**  Let `N_1, N_2, N_3 ◁ K` form a
diamond: pairwise products `T`, pairwise intersections `B`.  Then `T/B` is
abelian.
- `T/B ≅ N_1/B x N_2/B`, and `N_3/B` is the graph of an isomorphism
  `φ: N_1/B -> N_2/B`.
- Conjugating by `(a,1)` with `a in N_1/B` keeps the graph normal, so
  `(a n a^(-1), φ(n))` lies in the graph, i.e. `φ(a n a^(-1)) = φ(n)`.
- So `a n a^(-1) = n`, and `N_1/B` is abelian.

So in the normal-subgroup lattice of one fibre, non-distributive
configurations only occur on abelian sections.  There the true group
structure is an abelian labeling, preserved by every isomorphism.

## 3. The remaining obstacle

A proof would label every section consistently, as follows.
- Label abelian sections that sit inside a diamond by their true group
  structure, up to translation.
- Label nonabelian sections, which sit only in distributive parts of the
  lattice, by arbitrary labelings transported along a spanning tree of
  identifications.
- Assemble fibres through (A2), with (N2) removing holonomy.

What is not checked:
1. That a *distributive* family of more than two normal subgroups of one fibre
   can always be realized with *prescribed* labelings on its maximal
   quotients.  (A2) handles two.  With three or more, the prescribed
   labelings must agree on every pairwise common quotient, and the image of
   `K` in the product of its quotients must be an abelian coset for them.
2. That the arbitrary labelings of nonabelian sections can be chosen
   compatibly when one section occurs as a common quotient inside several
   fibres, through different extensions.
3. Cycles that do not pass through one common section.  Their transport is a
   relation, not a bijection, and (N2) does not apply to it directly.

A counterexample has to live in 1, 2 or 3: a network of nonabelian sections
whose identifications force incompatible labelings, while the algebra stays
nonzero.

## 4. What either answer gives

- **If true.**  Every coset-system gap is a solution-group gap.  Then
  `tracial-non-ru-coset-system-with-nonabelian-fibre-exists`, beyond its
  inherited instances, is goal-level, and so is the non-group-dual colored
  pair built from coset systems.  The non-group-dual rung would need square
  presentations that are not torsors.
- **If false.**  A non-relabelable coset system with nonzero algebra is the
  first syntax where nonabelian local structure is visible to the algebra.
  It is the place to look for a gap beyond the goal.

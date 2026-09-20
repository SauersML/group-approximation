# Direct padded abstract Röver–Nekrashevych construction

## Provenance and review status

This is an edited mathematical reconstruction of Sections 4–10 of the first
manuscript supplied by the user in the 2026-09-20 conversation. It records the
arguments supplied there, expands some intermediate justifications, and gives
them stable Cairn consumers. It is **not** a verbatim copy, byte-preserved source,
hash certificate, independent referee report, or Lean formalization. No author
identity or priority claim has been inferred from the submission.

The construction strengthens the existing repository counterexamples by putting
all the properties in one **perfect, finitely presented group with decidable
word problem**, directly from abstract Röver–Nekrashevych tables. It avoids the
additional abstract twisted Brin–Thompson construction in the older relative
simplicity argument. The existing existential claims and their previous reviews
are separate records; they do not certify this strengthened manuscript.

The new synthesis route has a nonempty prerequisite:
`padded-abstract-rn-local-derived-normal-subgroup-theorem`. This unresolved
mathematical obligation isolates the formal-support, local-commutator and
stabilizer arguments below. Its presence prevents this submission alone from
establishing the strengthened claim. Prose in this artifact does not itself
change Cairn's compiled state.

### Inputs and attribution

* The hard finite recursion comes from Bartholdi–Mitrofanov's Theorem A″,
  with the repository's explicitly recorded repair of its detector:
  `bartholdi-mitrofanov-proposition-2-4-gap-and-repair`. The original machine
  encoding and undecidability input are theirs. The new route requires the
  repair claim; it does not silently treat the printed argument as repaired.
* Finite presentations of Higman–Thompson groups, finite generation of their
  finite-forest variants, generation by prefix swaps, and simplicity of `V_D`
  for even `D` are classical Higman–Thompson inputs. The table presentation is
  the Scott/Röver–Nekrashevych presentation, as reconstructed in
  `abstract-rover-nekrashevych-finite-presentation-proof`; no novelty is claimed
  for that presentation.
* Finite-index finite presentation uses Reidemeister–Schreier. The impossibility
  of a recursive presentation for the quotient uses enumeration of consequences
  of relators, not an assumed solution of a word problem.
* Fournier-Facio–Wu–Zaremsky supply the questions and the terminology
  “type `[A_2]`” and “relatively simple.” This direct construction does **not**
  use their abstract twisted Brin–Thompson finite-presentation theorem.

This is consequently a classical-input manuscript integration, not a
zero-literature-input Lean result.

## 4. The recursion and abstract tables

Use left actions, right-to-left composition, and
`[a,b] = a b a⁻¹ b⁻¹`. Let `F = F(s₁,…,s_r)` be a finite-rank free group and

```text
ψ : F → F^d ⋊ Sym(d),       ψ(f) = (π_f; f|₁,…,f|_d),
π_fg = π_f π_g,            (fg)|_i = f|_(π_g(i)) g|_i.
```

The finite words specifying the states of the free generators define this
homomorphism. The induced action `ρ` on the rooted `d`-ary tree is defined
recursively by `ρ(f)(iu) = π_f(i)ρ(f|_i)(u)`. Write `N = ker ρ`.
The repaired hard input supplies such data with nonrecursive `N`. It is
co-computably-enumerable: a nonmember moves a finite word, and this is a finite,
effectively checkable witness. The kernel is section closed: if `f ∈ N`, its
root permutation is trivial and each `f|_i` lies in `N`.

For any group `G` with such a recursion, a table is `(P,Q,β,λ)`, where `P,Q`
are finite complete prefix codes of equal size, `β:P→Q` is a bijection and
`λ:P→G`. At a branch `p` with label `g`, expand by

```text
p i ↦ β(p) π_g(i),         new label at p i = g|_i.
```

Expansions on distinct branches commute. Expanding to a specified refinement
of the domain has a unique result. Common further refinements give the usual
common-expansion equivalence, which is transitive. Products are formed after
matching the intermediate prefix codes, with branch label
`λ(β′(p)) λ′(p)`. The wreath identity makes products compatible with expansion.
Inverses reverse the bijection and invert the corresponding labels. These
operations define the **abstract** group `V_d(G,ψ)`.

Labels are retained as elements of `G`; tables are not identified merely when
they induce the same boundary homeomorphism. There is a surjection to the
faithful boundary group `V_d(ρ(G))`. An element of its kernel has a representative
`(P,P,id,λ)` with all labels in `ker ρ`. Indeed, an identity boundary map sends
each branch cone to itself, forcing equal domain and range words at that branch,
and its suffix action must then be trivial.

## 5. Finite presentation and the decidable abstract word problem

For `d ≥ 3` and `G = ⟨S | R⟩` finitely presented, fix a finite presentation of
`V_d` on generators `T`, and adjoin `x_s` for `s ∈ S`. The intended image of
`x_s` is the label `s` on `C(1)`, with identity elsewhere. Let `Y` finitely
generate the pointwise fixer of `C(1)` in `V_d`. Choose exact prefix transports
`c_i(1u)=1iu`. Let `e_s` permute the children of `C(1)` by `π_s` and be the
identity outside `C(1)`. Fix state words `ŝ_i` representing `s|_i`. Impose:

```text
the finite defining relations of V_d;
[y,x_s] = 1                                         (y∈Y, s∈S);
[c₁x_sc₁⁻¹,c₂x_tc₂⁻¹] = 1                         (s,t∈S);
x_s = e_s ∏_(i=1)^d c_i ŝ_i(x)c_i⁻¹                (s∈S);
r(x) = 1                                            (r∈R).
```

Call the resulting group `Π`. Here is the inverse-map argument, including the
points that prevent the presentation from accidentally quotienting by the
boundary kernel.

1. For each nonempty word `a`, choose a prefix transport `v(1u)=au` and define
   `ι_a(g)=v g(x)v⁻¹`. Two transports differ, after conjugating back, by a
   pointwise fixer of `C(1)`. The fixer relations therefore give independence
   of the choice. Base relators make each `ι_a` a homomorphism.
2. Exact prefix transport gives `vι_a(g)v⁻¹=ι_b(g)` when `v(au)=bu`.
   Any two disjoint cones with nonempty complement can simultaneously be
   transported to `C(11),C(12)`: cone counts in the complements have the same
   residue modulo `d−1`, and can be enlarged to the same size. For `d≥3` two
   disjoint cones cannot cover the whole boundary. Thus all disjoint localized
   label subgroups commute, by the displayed finite commutator relations.
3. The map from a wreath tuple to its child permutation times the product of
   child labels is a homomorphism: moving a child permutation through the label
   product permutes its indices precisely by the wreath identity. Consequently
   the generator recursion relations extend to **every** `g∈G`, not just `S`.
4. For a table with nonempty branch words define
   `θ(P,Q,β,λ)=v_β ∏_(a∈P)ι_a(λ(a))`. The factors commute. One expansion replaces
   a label by its child permutation and states, exactly as in step 3, so `θ`
   is expansion invariant. Every table can first be expanded to avoid the root
   word. Matching middle partitions and using step 2 proves multiplication
   invariance. The resulting table-to-word map is inverse to the evident
   presentation-to-table map on `T` and all `x_s`, hence on the whole group.

This proves finite presentation from the finite input data and preserves
abstract labels. The existing Cairn finite-presentation theorem is the explicit
prerequisite for this step of the new route.

If `ψ` is injective and the word problem in `G` is decidable, the word problem
in `V_d(G,ψ)` is decidable. A generator word is effectively converted to a
table. It represents the identity exactly when its prefixes match branchwise
and all its labels are `1` in `G`. One direction is immediate. For the other,
if some expansion agrees with an identity table, reverse its last expansion:
the child permutation and states are trivial, and injectivity of `ψ` forces
the parent label to be trivial. Iterating proves the criterion. The abstract
and boundary word problems must not be conflated here: a label in `N` need
not be the identity in the abstract table group.

## 6. Padding and the finite-index commutator subgroup

Adjoin `k` new letters, fixed by every root permutation, with section `f` at
every new letter. Extend the old recursion on the old letters. This gives
`ψ_k:F→F^D⋊Sym(D)`, `D=d+k`, and is a homomorphism. A new coordinate recovers
`f`, so `ψ_k` is injective when `k≥1`.

Its tree kernel is still `N`. Restriction to the old alphabet shows that a
new-kernel element lies in `N`. Conversely, every old section of an element of
`N` lies in `N`, every new section is the element itself, and all their root
permutations are trivial. Induction on the length of a mixed-alphabet word
therefore proves that elements of `N` fix the enlarged tree.

Let `A` be the integer `r×r` matrix whose column for `s_j` is the sum of the
exponent-sum columns of its **old** states. Choose `k` with

```text
D=d+k even and D≥4,             k−1 > ||A||₁,
B=(k−1)I+A.
```

Here `||A||₁` is the induced column-sum norm. There are arbitrarily large `k`
of the needed parity. If `Bv=0` over `ℝ`, then
`(k−1)||v||₁ = ||Av||₁ ≤ ||A||₁||v||₁`, so `v=0`. Thus `det B ≠ 0`.

Set `P=V_D(F,ψ_k)`. Since even-arity `V_D` is perfect, it dies in `P_ab`.
All localized copies of a state have the same abelianization. The recursion
relations give `[s_j]=A e_j+k e_j`, or `B e_j=0`. Conversely the finite
presentation has no additional abelianized relations: the fixer and disjoint
support relations are commutators, and the free base has no relators. Hence

```text
P_ab ≅ ℤ^r / Bℤ^r.
```

It is finite. Put `E=P′`; then `E` has finite index in `P`, is finitely
presented by Reidemeister–Schreier, and has decidable word problem by the
abstract table algorithm. Also `V_D≤E`, since `V_D` is perfect. Let `K` be
the kernel of the boundary action of `P`, and `M=E∩K`. The prefix subgroup
acts faithfully, so `M` is proper and `E/M` contains a faithful `V_D`.

Finite-index rewriting is effective here: the finite abelian quotient is
given by the explicit integer matrix `B`; representatives and a Schreier
generating set for its kernel can be computed. Thus a computable `P`-word
known to lie in `E` can be converted to an `E`-word.

## 7. Formal support and direct relative simplicity

For a clopen set `Y`, let `D(Y)≤P` consist of tables that, outside `Y`, have
identity prefix maps **and identity labels**. This is formal support, a
condition in the abstract group, stronger than merely acting trivially outside
`Y`. A table can be refined to resolve `Y`. The manuscript's support calculus
asserts that these groups are well defined, groups on disjoint clopens commute,
conjugation transports them, and restriction splits a table that preserves a
clopen set into commuting inside and outside tables.

For a clopen `Y`, its cone-count type is the number of cones in a partition,
modulo `D−1`. Expansion changes that number by `D−1`. Proper nonempty clopens
of the same type are prefix transportable, by enlarging partitions of both
sets and their complements to matching sizes. In particular, for every proper
clopen `Y` and every nonempty cone `B₀`, there is `v∈V_D` with `v(Y)⊂B₀`:
choose a proper clopen subset of `B₀` of the desired residue and match both
complements. This does not claim that different clopen types are equivalent.

### Local derived groups generate `P′`

Let `H` be generated by `D(Y)′` over all proper clopens `Y`. Conjugation
transport makes `H` normal in `P`. Prefix swaps can be split into swaps of
descendants, and localized labels can be expanded by iterating the recursion.
The resulting child permutations can themselves be split into sufficiently
small swaps. Thus `P` is generated by elements of arbitrarily small formal
support. With respect to the uniform boundary measure choose a generating
family whose supports each have measure less than `1/3`. Any pair of such
supports has proper union; both elements belong to its `D(Y)`, so their
commutator belongs to `H`. The quotient `P/H` is abelian. Since `H≤P′`,
this proves `H=P′=E`.

This argument needs the formal table support statement, not a claim that
boundary-trivial labels can be discarded. The reduction of arbitrarily deep
child permutations and the simultaneous transport of the required clopens
are explicit proof-review points of the unresolved structural prerequisite.

### The double commutator captures the entire derived subgroup

Let `L◁E` contain `n` whose boundary action is nontrivial. Choose a cone `O`
with `O∩n(O)=∅`, and three disjoint cones `B₀,B₁,B₂⊂O`. For arbitrary
`a,b∈D(B₀)`, choose `v₁,v₂∈V_D≤E` taking `B₀` prefixwise to `B₁,B₂`.
Put `a₀=[a,v₁]` and `b₀=[b,v₂]`. Although `a,b` need not lie in `E`, these
commutators lie in `P′=E`. Their formal supports are respectively contained
in `B₀∪B₁` and `B₀∪B₂`. Their off-`B₀` factors are disjoint, so

```text
[a₀,b₀]=[a,b].
```

Write `[n,a₀⁻¹]=c a₀`, with `c=n a₀⁻¹ n⁻¹` formally supported in `n(O)`.
It commutes with both `a₀` and `b₀`. Normality of `L` and `n∈L` now give

```text
[[n,a₀⁻¹],b₀]=[a₀,b₀]=[a,b] ∈ L.
```

Therefore `D(B₀)′≤L`. Transport any proper clopen `Y` into `B₀` using an
element of `V_D≤E`; normality gives `D(Y)′≤L`. The preceding generation
argument gives `L=E`.

Every proper normal subgroup of `E` therefore lies in `M`. Since `M` itself
is proper and normal, it is the unique maximal proper normal subgroup, and
`E/M` is simple. It contains faithful `V_D`, so is infinite and nonabelian.
The image of `E′` in that nonabelian simple quotient is nontrivial; hence
`E′` is not contained in `M`, and the same normal-subgroup conclusion forces
`E′=E`. This proves perfectness. Every nonidentity element of the core `V_D`
lies outside `M` and thus normally generates `E`.

These conclusions are conditional in the new Cairn route on the unresolved
structural theorem; this reconstruction does not substitute for its review.

## 8. Exact hardness and failure of recursive presentation

Choose `v∈V_D` taking `C(1)` prefixwise to the disjoint cone `C(2)` and put

```text
z_f=[ι₁(f),v] ∈ E.
```

On `C(1)` its boundary action is that of `f`; on `C(2)` it is a transported
inverse; the supports are disjoint. Consequently `z_f∈M` if and only if
`f∈N`. This is a computable word reduction, followed if desired by the
finite-index rewriting of Section 6. **It is not asserted to be a group
homomorphism.**

Conversely, given an `E`-word, compute its abstract table. Its boundary map is
the identity exactly when every branch has the same domain and range word
and every label belongs to `N`. An oracle for `N` decides this finite test.
Thus `M≡_T N`. In particular, `M` is nonrecursive. It is co-c.e. because
nonidentity boundary actions have effectively detectable finite-prefix
witnesses. Hence `M` is not c.e.: a set that is both c.e. and co-c.e. is
recursive.

If `E/M` admitted a recursive presentation, its identity words in any fixed
finite generating tuple would be c.e. To see that the choice of presentation
does not matter, choose words for the finitely many images of the generators
of `E` in that recursive presentation and enumerate equality proofs there.
This would enumerate `M`, a contradiction. Thus the quotient is **not even
recursively presentable**, a stronger conclusion than undecidable word
problem or failure of finite presentation. In particular `M` is not finitely
normally generated in `E`, since a finite presentation of `E` together with
finite normal generators would give a finite presentation of `E/M`.

Any nontrivial simple quotient of `E` has a maximal proper normal kernel;
relative simplicity makes that kernel `M`. Hence `E` has no nontrivial
recursively presented simple quotient at all. This does not exclude simple
subgroups: `V_D≤E` is already an infinite finitely presented simple subgroup.

## 9. The clopen action is of type `[A₂]`

Let `Ω` be the proper nonempty clopen subsets of the `D`-ary Cantor boundary.
A homeomorphism fixing every clopen set is the identity, so the kernel of
`E↷Ω` is precisely `M`.

For an ordered pair `(U,W)`, record the four Boolean atoms of `U,W`; for each
record whether it is empty, and otherwise its cone-count residue modulo
`D−1`. There are at most `D^4` records. Two pairs with the same record are
already conjugate by a prefix element: enlarge the partitions of each pair
of corresponding nonempty atoms to the same size, then match those atoms
prefixwise. Thus `V_D`, and consequently `P`, has finitely many pair orbits.
Since `E` has finite index in `P`, each `P`-orbit splits into at most `[P:E]`
many `E`-orbits. This bound concerns pair orbits; no transitivity of the
clopen action across different residue types is claimed.

For each `U∈Ω`, formal restriction gives

```text
P_U = D(U) × D(Uᶜ).
```

Each factor is finitely generated. Fix a cone properly inside `U`. The
finite-forest prefix group supported in `U` is finitely generated, and add
the finitely many free state generators localized in that cone. A table
supported in `U` is its prefix part times finitely many localized labels.
Any proper branch cone inside `U` is reached by a prefix transport within
`U`; if `U` itself is one branch cone, expand its label first. This expresses
every label using the selected finite family. The same holds for `Uᶜ`.
Finally `E_U=E∩P_U` has finite index in `P_U`, hence is finitely generated.

Together with finite presentation of `E`, this is type `[A₂]`: finitely many
orbits on `Ω²`, finitely generated point stabilizers, and finitely presented
acting group. The formal restriction and local generation assertions are
included in the unresolved structural prerequisite.

## 10. Sharp non-removal and the precise consequences

Suppose there were an injective homomorphism `j:E→H`, with `H` finitely
presented and `L◁H` finitely normally generated, satisfying the exact
intersection condition

```text
j(E) ∩ L = j(M).
```

Then `j` induces an injection `E/M→H/L`, and `H/L` is finitely presented.
A finitely generated subgroup of a recursively presented group has c.e.
identity words, by substituting its fixed generators and enumerating ambient
relator consequences. This would make `M` c.e., contradicting Section 8.
Thus **no such exact pair embedding exists**, whether or not `H/L` is simple
and whether or not an action of `H` is supplied.

Once the structural prerequisite is proved, this single `(E,M)` consequently:

* gives a type `[A₂]` action whose image is not recursively presentable;
* gives a finitely presented relatively simple pair with undecidable simple
  quotient, already with a decidable, perfect ambient group;
* supplies the obstruction to both kernel-removal requests in FFWZ Question
  5.9, interpreted by the displayed exact-intersection convention;
* realizes the non-finitely-presented action-image phenomenon of Question
  5.8 in the stronger non-recursively-presentable form.

The new graph has explicit projection routes to
`some-a2-action-has-a-nonrecursive-kernel` and
`fp-relatively-simple-pair-with-unsolvable-simple-quotient`. Existing routes
from those nodes already carry the non-removal and refutation consequences.
These observations do not solve Boone–Higman, do not supply a new simple
finitely presented host for every decidable group, and do not claim that
the stronger witness has already passed proof review.

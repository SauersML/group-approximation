# Problem 1.22, Thompson-like side: germ and dimension fences for simple groups on the line (part 1)

Lane `z1-22-lo-simple-thompson`, 2026-09-13. Zaremsky, *Some open problems* (version of July 12, 2026),
Section 1, Problem 22: "Find an example of a left-orderable simple group of type F. (Type F∞ was done by
Hyde–Lodha. If Burger–Mozes groups are left-orderable then they'd do it.)"

This part proves elementary fences that every answer must respect and that kill the natural
"upgrade a Thompson-like example" routes. Nothing here answers the problem.

**Relation to the owner lane.** `finite-cd-groups-have-no-micro-supported-line-action`
(z1-22-lo-simple-bm, 067f470465) counts disjoint intervals with nontrivial rigid stabilizers.
- Remark B2 below shows that count is vacuous for finitely generated simple groups: their faithful
  actions on the line are never micro-supported, whatever their dimension.
- The Hyde–Lodha groups therefore get their infinite dimension from disjoint supports that are not
  intervals, and Lemma A counts those.

## 0. Conventions

- `Homeo+(R)` is the group of orientation-preserving homeomorphisms of `R`. For `g` in it,
  `supp(g) = {x : g(x) ≠ x}` is the open support. It is `g`-invariant.
- A countable group is left-orderable iff it acts faithfully on `R` by orientation-preserving
  homeomorphisms.
- Type F: a finite K(G,1). It implies finitely generated, torsion-free and `cd G < ∞`.
- `Fix(G)` is the set of global fixed points. A *component of the action* is a component `C` of
  `R \ Fix(G)`. Each `g ∈ G` fixes the endpoints of `C`, so `g(C) = C`.

## 1. Lemma A: disjoint supports give free abelian subgroups

**Lemma A.** If `g_1, …, g_n ∈ Homeo+(R)` are nontrivial with pairwise disjoint supports, then
`⟨g_1, …, g_n⟩ ≅ Z^n`. The supports need not be intervals.

*Proof.*
1. Every nontrivial `f ∈ Homeo+(R)` has infinite order. Pick `x` with `f(x) > x` (the case `f(x) < x` is
   symmetric). If `f^{k-1}(x) ≥ x`, then `f^k(x) ≥ f(x) > x`, so `f^k(x) > x` for all `k ≥ 1`.
2. `g_j` fixes `supp(g_i)` pointwise for `j ≠ i`, and `g_i` preserves `supp(g_i)`. Checking on
   `supp(g_i)`, on `supp(g_j)` and off both shows `g_i g_j = g_j g_i`.
3. On `supp(g_i)`, the product `∏ g_k^{a_k}` restricts to `g_i^{a_i}`. If the product is `1`, then
   `g_i^{a_i}` is the identity on `supp(g_i)`, hence everywhere, so `a_i = 0` by step 1. ∎

**Corollary A1.** If `cd G < ∞` and `G` acts faithfully on `R`, then any family of nontrivial elements of
`G` with pairwise disjoint supports has at most `cd G` members, since `Z^n ≤ G` forces `n ≤ cd G`.

**Corollary A2.** A group containing `F'`, `F`, or `Z ≀ Z` has infinite cohomological dimension, so it is
not of type F.
- `F'` is the set of elements of `F` compactly supported in `(0,1)`. For disjoint standard dyadic
  intervals `I_1, …, I_n`, the nontrivial subgroups `F_{I_k} ≤ F'` have disjoint supports, so Lemma A
  gives `Z^n ≤ F'`.
- The base of `Z ≀ Z` contains every `Z^n`.
- `cd F = ∞` is classical (Brown–Geoghegan, Invent. Math. 77 (1984)). ∎

## 2. Lemma B: finitely generated groups have no one-sided supports

**Lemma B.** Let `G ≤ Homeo+(R)` be finitely generated with `Fix(G) = ∅`. Let `K_+` be the set of
`g ∈ G` that are the identity on some ray `[c,∞)`, and define `K_-` with rays `(-∞,c]`. Then `K_±` are
proper normal subgroups.

*Proof.*
1. `K_+` is a subgroup: two elements that are the identity on `[c,∞)` and `[c',∞)` combine to one that is
   the identity on `[max(c,c'),∞)`.
2. Normality: `h g h^{-1}` is the identity on `h([c,∞)) = [h(c),∞)`.
3. Properness: if `K_+ = G`, each of finitely many generators is the identity on some `[c_i,∞)`. With
   `c = max c_i`, all of `G` fixes `[c,∞)`, which contradicts `Fix(G) = ∅`. The same holds for `K_-`. ∎

**Corollary B1.** Let `G` be a finitely generated simple group acting faithfully on `R`, and let `C` be a
component of the action. Then no nontrivial element of `G` is the identity near either end of `C`.

*Proof.*
1. The kernel of the restriction to `C` is a normal subgroup other than `G`, so it is trivial. So `G`
   acts faithfully on `C` without global fixed points.
2. Identify `C` with `R` and apply Lemma B. The proper normal subgroups `K_±` are trivial. ∎

**Remark B2 (micro-support is vacuous for simple groups).** Under Corollary B1, let `I` be a nonempty open
interval with `I ⊆ C`, `I ≠ C`. Every element of the rigid stabilizer `G_I` is the identity near at least
one end of `C`, so `G_I = 1`.
- So no faithful action of a finitely generated simple group on the line is micro-supported, whatever
  `cd G` is.
- In particular the natural actions of the Hyde–Lodha simple groups, `G_ρ` of arXiv:1807.06478 and the
  finitely presented `Q_n` of arXiv:2302.04805, are not micro-supported. Their infinite dimension comes
  from families like `λ(F') ≤ G_ρ`, whose supports meet every unit interval (§4).

*Credit.* Hyde–Lodha (arXiv:1807.06478, §1) name germ homomorphisms at `±∞` and simplicity criteria
through increasing unions of compactly supported subgroups as the classical obstructions to finite
generation. Corollary B1 is the folklore form of that remark.

## 3. Lemma C: finitely many breakpoints force solvable end germs

**Lemma C.** Let `G ≤ Homeo+(R)` be nonabelian simple, with every element either PL with finitely many
breakpoints, or piecewise projective with finitely many pieces. Then on each component `C = (a,b)` of the
action, every element is the identity near `a` and near `b`.

*Proof.*
1. **Germs at `±∞`.** A projective map sending `+∞` to `+∞` is affine, so the germ at `+∞` is that of
   `x ↦ λx + μ` with `λ > 0`. Germs compose, so this defines a homomorphism to the metabelian group
   `Aff+(R)`. The same holds at `-∞`.
2. **Germs at a finite endpoint `a`.** A PL germ fixing `a` is `x ↦ a + λ(x − a)`, and these form an
   abelian group. A projective germ fixing `a` becomes an affine germ at `∞` after conjugating by
   `x ↦ 1/(x − a)`.
3. **Kernel.** Each germ map is a homomorphism from the nonabelian simple group `G` to a solvable group,
   so its kernel is all of `G`. ∎

**Corollary C1.** No finitely generated nonabelian simple group acts faithfully on `R` by PL maps with
finitely many breakpoints, or by piecewise projective maps with finitely many pieces.
*Proof.* Lemma C puts all of `G` in `K_±` for a component, while Corollary B1 says `K_± = 1`. ∎

*Model tests.*
- `F'` is simple and PL but not finitely generated. Thompson's `T` is PL and simple but acts on the
  circle, not the line. Monod's `H` and the Lodha–Moore group are not simple.
- The Hyde–Lodha simple groups have infinitely many breakpoints accumulating at `±∞`. All four are
  consistent with the lemmas.

## 4. The Hyde–Lodha groups contain F'

Checked against arXiv:1807.06478v2, pages 3–9:
- Definition 2.3 and Lemma 2.4: `H = ⟨F', ν_1⟩ = ⟨ν_1, ν_2, ν_3⟩ ≤ F` with `H' = F'` simple.
- Definition 3.2: `G_ρ = ⟨ζ_1, ζ_2, ζ_3, χ_1, χ_2, χ_3⟩ ≤ Homeo+(R)`, with `𝒦 = ⟨ζ_i⟩` and
  `ℒ = ⟨χ_i⟩` isomorphic to `H` via `λ` and `π`. The element `λ(f)` acts as `f`, or as `ι f ι`, on
  every `[n, n+1]`.
- Theorem 1.3: for quasi-periodic `ρ`, the group `G_ρ` is finitely generated and simple.

So `λ(F') ≅ F' ≤ G_ρ` and `cd G_ρ = ∞` by Corollary A2. Every overgroup of `G_ρ` has infinite `cd`.

Not read by this lane:
- the generalized groups `G_{ρ,α}` (§6 of that paper);
- arXiv:2302.04805. The owner lane records its Theorem 1.1 (finitely presented, type F∞ simple groups of
  homeomorphisms of `R`) and Proposition 1.4 (the groups `Q_n = [Γ_n, Γ_n]` have infinite geometric
  dimension).

## 5. Theorem D: a type-F answer, seen on the line

**Theorem D.** Let `G` be a left-orderable simple group of type F acting faithfully on `R`, and let `C` be
a component of the action.
- **(D1)** No nontrivial element is the identity near an end of `C`, and no rigid stabilizer of a proper
  subinterval of `C` is nontrivial (Corollary B1, Remark B2).
- **(D2)** `G` has no faithful action on `R` by finite-breakpoint PL maps or finitely-piecewise projective
  maps (Corollary C1).
- **(D3)** Any family of nontrivial elements with pairwise disjoint supports, not necessarily intervals,
  has at most `cd G` members (Corollary A1).
- **(D4)** `G` contains no `F`, `F'` or `Z ≀ Z` (Corollary A2).

(D1) and (D2) use only finite generation and simplicity; (D3) and (D4) use only `cd G < ∞`.

**Routes killed.**
- **(K1)** Overgroups of `F'`, of chain-group commutator subgroups, of locally moving interval groups,
  and of the Hyde–Lodha `G_ρ`: by (D4) and §4.
- **(K2)** Finitely many breakpoints: by (D2).
- **(K3)** Families with unboundedly many disjoint supports, periodic or quasi-periodic like `λ(F')`:
  by (D3).

**What survives.** A witness acts on the line with faithful end germs, no nontrivial rigid stabilizer of a
proper subinterval of a component, and at most `cd G` disjointly supported nontrivial elements. That is
far from Thompson-like dynamics.
- Model: `BS(1,2)` acting by `x ↦ 2x`, `x ↦ x + 1` has `cd 2`, a minimal action, and no two disjointly
  supported nontrivial elements; but it is not simple.
- The known torsion-free simple groups of type F are cocompact lattices in products of trees
  (Burger–Mozes, Rattaggi). For them (D3) bounds disjointly supported families by 2 in any order action.

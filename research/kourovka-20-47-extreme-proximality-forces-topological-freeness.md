---
rg: 2
id: kourovka-20-47-extreme-proximality-forces-topological-freeness
kind: claim
title: Kourovka 20.47 partial answer — for free groups (and every torsion-free group with cyclic centralizers) nontrivial elements never have disjoint supports, so every extremely proximal action is topologically free; a counterexample must be strongly but not extremely proximal, with a support whose hyperspace orbit avoids all singletons
distinct_from:
  artin-deligne-boundary-actions-are-topologically-free: that node proves topological freeness of specific boundary actions of Artin/Deligne groups; this one is a general statement for all actions of groups with cyclic centralizers, aimed at Kourovka 20.47.
---

**ESTABLISHED (partial answer to Kourovka 20.47).** Theorems 1 and 2 and Corollary 3 are lane
proofs and have not been independently reviewed. Corollary 4 depends on a structure theorem for
circle actions that I recalled but did not re-read. Kourovka 20.47 itself stays **OPEN**. No
priority is claimed: the commuting-supports trick is standard in the work of Le Boudec and Matte
Bon, and the proposers very likely know Theorem 2.

## The problem

Kourovka 20.47 (A. Le Boudec, N. Matte Bon), in the wording recorded by bh-kourovka-scout from
arXiv:1401.0300v46 (`research/artifacts/gq-bh-kourovka-scout-candidates-2026-09-19.md`,
aae1608cbe). This lane did not re-read the verbatim text:

> Is every faithful, minimal, strongly proximal F_n-action on a compact space topologically free?

Conventions: supp(f) is the closure of {x : fx ≠ x}, so supp(f) = X ∖ int Fix(f). An action is
topologically free if int Fix(g) = ∅ for every g ≠ 1. It is extremely proximal if for every
closed C ≠ X and every nonempty open U there is h with hC ⊆ U. Let 𝒵 be the class of torsion-free
groups in which the centralizer of every nontrivial element is cyclic. 𝒵 contains F_n,
torsion-free hyperbolic groups and surface groups.

## Theorem 1 (no disjoint supports)

Let G ∈ 𝒵 act faithfully by homeomorphisms on a Hausdorff space X. Then supp(g) ∩ supp(k) ≠ ∅
for all g, k ∈ G ∖ {1}.

*Proof.*
1. **Disjoint supports commute.** Each support is invariant under its element: if fx ≠ x then
   f(fx) ≠ fx, so f preserves its moved set and hence its closure. Suppose supp g ∩ supp k = ∅.
   - For x ∈ supp g: both x and gx lie in supp g, so outside supp k, and k fixes both. So
     kgx = gx = gkx.
   - For x ∈ supp k: symmetrically, gkx = kx = kgx.
   - Otherwise both g and k fix x.
   So gk and kg agree pointwise, and gk = kg because the action is faithful.
2. **They are powers of one element.** k lies in C(g), which is cyclic, say ⟨c⟩. Since
   g ∈ C(g), we can write g = c^a and k = c^b with a, b ≠ 0.
3. **Supports shrink under powers.** supp(f^m) ⊆ supp(f), because a point fixed by f is fixed
   by f^m. So c^{ab} = g^b = k^a has support in supp g ∩ supp k = ∅. It acts trivially, so
   c^{ab} = 1 by faithfulness, and ab = 0 because G is torsion-free. That is a contradiction. ∎

## Theorem 2 (extremely proximal ⇒ topologically free)

Let G ∈ 𝒵 act faithfully and extremely proximally on a compact Hausdorff space X. Then the action
is topologically free. Minimality is not needed.

*Proof.* Suppose g ≠ 1 and U = int Fix(g) ≠ ∅. Then C = supp g = X ∖ U is closed and C ≠ X.
Extreme proximality gives h with hC ⊆ U. Then supp(hgh⁻¹) = hC is disjoint from C = supp g,
which contradicts Theorem 1. ∎

This confirms, and extends to the class 𝒵, the observation recorded in aae1608cbe. Its
malnormality argument is the case where k is a conjugate of g.

## Corollary 3 (actions on trees)

Let G ∈ 𝒵 act faithfully on a locally finite tree T, minimally (no proper invariant subtree) and
of general type (no fixed end and no invariant pair of ends). Then no nontrivial element fixes
pointwise a nonempty open subset of ∂T.

*Proof.* Minimality and general type give hyperbolic elements with attracting end in any given
shadow and repelling end in any other given disjoint shadow. This is standard and recalled; the
Burger–Mozes node on main uses it in the same way. Now let C ⊊ ∂T be closed and U open and
nonempty. C misses some shadow ∂T_e. Take a hyperbolic h with repelling end in ∂T_e and attracting
end in U; a high power of h maps C into U. So the action on ∂T is extremely proximal, and
Theorem 2 applies. ∎

For example, if F_n is dense in Aut(T_d), every nontrivial elliptic element of F_n acts
nontrivially on the boundary of every half-tree.

## Corollary 4 (circle; conditional)

Let G ∈ 𝒵 be non-abelian and act faithfully and minimally on S¹. Then the action is topologically
free.

This depends on the structure theorem for minimal circle actions, which I recalled but did not
re-read: Ghys, *Groups acting on the circle*, Enseign. Math. 2001, §5; Margulis; Malyutin. A
minimal action on S¹ is either
- conjugate to an action by rotations, or
- proximal, and then it contracts every proper closed arc into every nonempty open arc, i.e. it
  is extremely proximal on S¹, or
- a finite cyclic cover of a proximal one.

*Proof, given that theorem.*
- **Rotations:** impossible, since G would be abelian.
- **Proximal:** Theorem 2, because every proper closed subset of S¹ lies in a proper closed arc.
- **Cover of degree d:** the quotient action is still faithful, because its kernel acts by deck
  rotations and so embeds in Z/d, which is trivial in a torsion-free group. It is minimal and
  proximal, hence topologically free. If some g ≠ 1 fixed an open arc upstairs pointwise, its
  image would be nontrivial and fix the projected arc downstairs, a contradiction. ∎

## Proposition 5 (what a counterexample must look like)

Let G ∈ 𝒵, for instance G = F_n, act faithfully, minimally and strongly proximally on a compact
metrizable X. Suppose g ≠ 1 has U = int Fix(g) ≠ ∅, and set K = supp g, which has nonempty
interior. Then:

- **(a) K meets all its translates.** K ∩ hK ≠ ∅ for every h ∈ G, by Theorem 1 applied to g and
  hgh⁻¹. In particular the action is not extremely proximal.
- **(b) No other small supports.** No nontrivial element has support disjoint from K. So every
  rigid stabilizer G_V = {f : f fixes X ∖ V pointwise} with V̄ ⊆ U is trivial. More generally, any
  two nontrivial elements have intersecting supports, so the action is as far from
  micro-supported as possible.
- **(c) Singletons are out of reach in the hyperspace.** In the Vietoris hyperspace 2^X, the orbit
  closure of K contains no singleton.

  *Proof.* The orbit closure is G-invariant and closed. If it contained {x}, then by minimality it
  would contain every {y}. Take y ∈ U. The set {C : C ⊆ U} is a Vietoris neighbourhood of {y}, so
  some hK ⊆ U, and then hK ∩ K = ∅, contradicting (a).
- **(d) Measures on K can be pushed into U.** For every probability measure μ with full support
  on K, every y ∈ U and every ε > 0, there is h with (hμ)(B(y, ε)) > 1 − ε. This follows from
  strong proximality together with minimality, since the orbit closure of δ_x is all Dirac
  masses.

So in a counterexample, K can be moved into U in measure but never as a set. The question is
therefore exactly about actions of 𝒵-groups that are strongly proximal but not extremely
proximal, with a non-displaceable support whose hyperspace orbit avoids the singletons. Such
actions cannot live on S¹ (Corollary 4), on tree boundaries (Corollary 3), or on convergence
boundaries: torsion-free convergence groups are topologically free on perfect limit sets, since
each nontrivial element has at most two fixed points. The remaining arena is actions on Cantor
sets and higher-dimensional spaces that do not come from geometric boundaries.

Non-topologically-free boundary actions do exist for other C*-simple groups, for example Thompson's
V on the Cantor set and T on S¹. Both groups contain Z², which is consistent with Theorem 1.

## Attempts

- **Literature check** (09-19): searched for Kourovka 20.47 and for strongly proximal, topologically
  free actions of free groups. Checked Ma–Wang–Yang arXiv:2510.05669 (CAT(0) boundaries), Alam–
  Gondek–Kalantar–Pham arXiv:2602.15009 (growth conditions), Le Boudec–Matte Bon arXiv:1906.05744,
  and Caprace–Le Boudec–Matte Bon arXiv:2107.07765. I found no answer to 20.47.
- **Not done:** Le Boudec–Matte Bon, *Subgroup dynamics and C*-simplicity of groups of
  homeomorphisms*, was not read in text form, because only the PDF was available and lane rules
  bar reading it locally. Whether Theorem 2 is stated there is therefore unchecked.

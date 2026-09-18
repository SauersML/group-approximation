# Host theorems for GL_n(Q): statements with their exact hypotheses

Lane `gq-lit-hosts`, 2026-09-17. Target: `gl-n-q-embeds-in-fp-simple-group`.

Sources were read from arXiv abstract and HTML pages through a web fetch that
returns converted text. Text in quotation marks is the source wording as
returned. Where the fetch summarized rather than quoted, the entry says
**paraphrase**. Lane remarks are marked **Remark (lane)**; they are not source
statements and are not reviewed.

## 1. Finite germ extensions (Belk–Hyde–Matucci)

**Source.** J. Belk, J. Hyde, F. Matucci, *Finite germ extensions*,
arXiv:2407.03149v1 (3 July 2024). Abstract: "we prove that every countable
abelian group can be embedded into a finitely presented simple group ... we
describe a specific 2-generated, F∞ simple group VA of homeomorphisms of the
Cantor set that contains every countable abelian group."

**Standing notation (Notation 2.2).** "let X be a Hausdorff space, let
B ≤ Homeo(X), and let G be a finite germ extension of B."

**Singular points.** "The singular points of h are the set sing(h) = {p ∈ X |
h does not agree with any element of B on any neighborhood of p}." Also
sing(G) = ⋃_{g ∈ G} sing(g).

**Definition (finite germ extension).** "A group G ≤ Homeo(X) will be called a
finite germ extension of B if it satisfies the following conditions:
(1) Every element of G has only finitely many singular points.
(2) G contains B, and indeed B is precisely the subgroup of G consisting of all
elements that have no singular points.
(3) For every g ∈ G and p ∈ sing(g), there exists an h ∈ G with sing(h) = {p}
such that h agrees with g on some neighborhood of p."

**Notation.** "SingFix_G(M, M′) ≔ {g ∈ G | sing(g) ⊆ M and g|_{M′} = id}".
Group of germs: "(G)_p = Stab_G(p)/RStab_G(p) where RStab_G(p) is the subgroup
of the stabilizer consisting of elements that are the identity in a
neighborhood of p." "Oligomorphic": "the induced action of B on sing(G)^k has
finitely many orbits for all k ≥ 1."

**Theorem 1.1.** "Let G be a finite germ extension of some B ≤ Homeo(X), and
suppose that: (1) B has type F∞, as does Stab_B(M) for every finite set
M ⊆ sing(G), (2) The action of B on sing(G) is oligomorphic, and (3) Either
|(G)_p : (B)_p| < ∞ for every p ∈ sing(G), or (B)_p ⊴ (G)_p and (G)_p/(B)_p has
type F∞ for every p ∈ sing(G). Then G has type F∞."

**Theorem 2.1 (level n).** Hypotheses: "(1) The induced action of B on
sing(G)^n has finitely many orbits," and "(2) For every pair M ⊆ M′ of subsets
of sing(G) with 0 ≤ |M′| ≤ n, the group SingFix_G(M, M′) ... has type F_n."
Conclusion: "G has type F_n." (Its proof uses the germ complex, a product of
trees; cube stabilizers are conjugate to groups SingFix_G(M, M′) with
|M′| ≤ n, per `research/artifacts/shell-envelope-local-tests-2026-09-13.md`.)

**Corollary 2.10 (level n; Theorem 1.1 is its F∞ case).** Hypotheses
(paraphrase for (1) and (2); (3) verbatim from the Cairn artifact above):
(1) B acts on sing(G)^n with finitely many orbits; (2) Fix_B(M) has type F_n
for each M ⊆ sing(G) with 0 ≤ |M| ≤ n; (3) "Either |(G)_p : (B)_p| < ∞ for each
p ∈ sing(G), or (B)_p ⊴ (G)_p for each p ∈ sing(G) and (G)_p/(B)_p has type
F_n." Conclusion: G has type F_n. Propositions 2.8 and 2.9 derive the SingFix
finiteness from (3).

**Theorem 1.3 (simplicity).** "Let G be a finite germ extension of some
B ≤ Homeo(X). Suppose that B is simple, locally moving, and has no global fixed
points, and that B and G have the same orbits in X. Then the commutator
subgroup G′ is simple, and every proper quotient of G is abelian."

**The group VA (paraphrase of Section 1.3; the HTML fetch truncated Section 4,
so the germ-group identification was not extracted).**
- VA is a finite germ extension of B = V on the Cantor set C_2. Its singular
  points are points ending in 0̄ or 1̄. Near a singular point p an element f is
  locally order-preserving and satisfies L_{f(p)} ∘ f = f ∘ L_p near p, where
  L_p is the prefix replacement deleting one 0 or 1 (a slope-2 germ).
- TA is the analogous extension of T on the circle, with dyadic singular points
  and L_p a slope-2 linear map fixing p. Both contain a group A ≤ Homeo_+(R)
  introduced by Brin, and A contains Q (by the earlier Belk–Hyde–Matucci paper).
- Verbatim: "the group VA contains ⨁_ω(A ⊕ V) ... it follows that VA contains
  ⨁_ω(Q ⊕ Q/Z), and thus contains every countable abelian group." Q/Z ≤ V is
  Higman's.
- Theorem 1.6: "Every countable abelian group embeds into a finitely presented
  simple group." VA is 2-generated, simple and of type F∞, by Theorems 1.1, 1.3
  and 1.4.

**Remark (lane): what a germ-extension route to G must supply.**
1. Finite presentation needs only level n = 2 of Theorem 2.1: finitely many
   B-orbits on sing(G)^2 and finitely presented SingFix_G(M, M′) for |M′| ≤ 2.
   With B = V acting on one V-orbit of points, the orbit condition holds,
   because V is highly transitive on each of its orbits in C_2.
2. V contains no copy of (Q,+) (Higman), so under O1 the divisible part of
   GL_n(Q) cannot lie in B = V. In VA, Q enters through the germ side (Brin's A),
   not through V. A germ-extension route over B = V must put divisibility
   into the germ groups (G)_p or into the SingFix groups. The Corollary 2.10
   branch then needs (V)_p ⊴ (G)_p with (G)_p/(V)_p finitely presented and
   containing the divisible pieces.
3. Simplicity comes only for G′. **Perfect subgroups lie in G′**, and
   SL_m(Q) is perfect for m ≥ 2. Also GL_n(Q) ↪ SL_{n+1}(Q) by
   g ↦ diag(g, det(g)^{-1}). So it suffices to put SL_{n+1}(Q) inside a
   finitely presented finite germ extension G satisfying Theorem 1.3, provided
   G′ is also finitely presented (for instance, G/G′ finite). Every lane can
   state its target for SL_m(Q), m ≥ 3, without losing G.

## 2. Twisted Brin–Thompson groups and type (A) actions (Belk–Zaremsky, Zaremsky)

**Sources.**
- J. Belk, M. C. B. Zaremsky, *Twisted Brin–Thompson groups*,
  arXiv:2001.04579v2 (9 May 2021), Geom. Topol. 26 (2022) 1189–1223.
- M. C. B. Zaremsky, *Finite presentability of twisted Brin–Thompson groups*,
  arXiv:2405.18354v2 (25 Nov 2024).

**Setting (BZ, paraphrase).** S is a set "of any cardinality", and "Let G be
any group of permutations of the set S". There is "a natural monomorphism
ι_∅ : G → SV_G".

**BZ Theorem 3.4.** "The twisted Brin–Thompson group SV_G is simple. Moreover,
if SV_G is finitely generated then it can be generated by two elements of
finite order."

**BZ Theorem A.** "The group SV_G is finitely generated if and only if G is
finitely generated and the action of G on S has finitely many orbits."

**Type (A), Zaremsky.** "(A): The action is faithful, the group G is finitely
presented, each Stab_G(s) for s ∈ S is finitely generated, and there are
finitely many G-orbits of two-element subsets of S." (Quoted in
`type-a-action-gives-boone-higman-for-subgroups`, read from source 2026-08-24.)

**Zaremsky Theorem A.** "Let G be a group acting faithfully on a set S. Then
the twisted Brin–Thompson group SV_G is finitely presented if and only if the
action of G on S is of type (A)."

**Zaremsky Corollary B.** "Any subgroup of a group admitting an action of type
(A) (has solvable word problem and) satisfies the Boone–Higman conjecture."

**Zaremsky Proposition 5.5.** "If two groups satisfy the permutational
Boone–Higman conjecture, then so does their direct product."
**Proposition 5.6.** "Let G be a group. If a finite index subgroup of G
satisfies the permutational Boone–Higman conjecture, then so does G. In
particular, satisfying the permutational Boone–Higman conjecture is a
commensurability invariant."

**Remark (lane): Corollary B needs no finite generation of the subgroup.** The
proof is containment: H ≤ Γ ≤ SV_Γ (via ι_∅), and SV_Γ is simple (BZ 3.4) and
finitely presented (Theorem A). So G reduces exactly to:

> **(A-target)** some finitely presented Γ ⊇ GL_n(Q) (or ⊇ SL_{n+1}(Q)) acting
> faithfully on a set S with finitely generated point stabilizers and finitely
> many orbits of 2-element subsets.

By O1, Γ is not residually finite, so in particular Γ is not linear.

**Related obstruction, not a conflict.** Fournier-Facio–Kropholler–Lyman–
Zaremsky, *Finiteness properties of stabilisers of oligomorphic actions*,
arXiv:2506.02319 (v1 2 June 2025, revised 27 Feb 2026; to appear in Publ.
Mat.). Abstract: "for any oligomorphic action of such a group on an infinite
set there exists a finite subset whose stabiliser is not of type FP∞", for a
large class that the Cairn artifacts record as including groups of finite vcd
and all countable linear groups. It concerns FP∞ of stabilizers of finite
subsets. Type (A) asks only for finitely generated point stabilizers. It also
constrains only the actor Γ, which cannot be linear here anyway.

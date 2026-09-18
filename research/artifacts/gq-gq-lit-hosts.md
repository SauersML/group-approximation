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
   With B = V acting on one V-orbit of points, the orbit condition holds:
   V is highly transitive on the orbit of 0̄ (quoted by BFFHZ, §3), and by the
   same disjoint-cone prefix argument on an orbit V·p. The Cairn route
   `boone-higman-via-shell-germ-stabilizers` uses exactly this.
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

## 3. Universality through highly transitive and MIF hosts (BFFHZ)

**Source.** J. Belk, F. Fournier-Facio, J. Hyde, M. C. B. Zaremsky,
*Boone–Higman embeddings of Aut(F_n) and mapping class groups of punctured
surfaces*, arXiv:2503.21882v2 (14 Apr 2025).

**Type (A) as stated there (paraphrase):** Γ finitely presented,
Stab_Γ(s) finitely generated for all s ∈ S, and "The diagonal action of Γ on
S×S has finitely many orbits". Faithfulness is part of Zaremsky's version (§2).

**Theorem A.** "For each n, the group Aut(F_n) (and hence all of its subgroups)
embeds in a finitely presented simple group, namely the twisted Brin–Thompson
group SV_Γ where Γ = Aut_V(V∗F_n) and S = Hom_V(V∗F_n, V), and hence satisfies
the Boone–Higman conjecture."

**Theorem C.** "For a finitely generated group G (with solvable word problem)
the following are equivalent: (i) G satisfies the permutational Boone–Higman
conjecture ... (ii) G embeds in a finitely presented (simple) twisted
Brin–Thompson group. (iii) G embeds in a finitely presented simple group that
is highly transitive. (iv) G embeds in a finitely presented simple group that
is MIF."

**Corollary D.** "Finitely presented (simple) twisted Brin–Thompson groups are
universal among finitely presented simple highly transitive groups, and more
generally among finitely presented simple MIF groups."

**Theorem E.** "For any finitely presented simple MIF group G, the group
Aut_G(G∗F_n) (n ≥ 2) admits an action of type (A), and hence satisfies the
(permutational) Boone–Higman conjecture."

**Corollary F.** "If A and B satisfy the permutational Boone–Higman
conjecture, then the free product A∗B also satisfies the (permutational)
Boone–Higman conjecture."

**Mechanism (paraphrase with the quoted lemma statements).**
- Aut_G(G∗F_n) is the group of automorphisms of G∗F_n restricting to the
  identity on G. S = Hom_G(G∗F_n, G), which is in bijection with G^n, and the
  action is by precomposition.
- Lemma 2.2: "Suppose that G is MIF. Then the action of Aut_G(G∗F_n) on
  Hom_G(G∗F_n, G) is faithful." (MIF is needed only here.)
- Proposition 2.3: the action is highly transitive when G is an infinite simple
  group and n ≥ 2.
- Proposition 2.6: if G is finitely generated, the point stabilizer Stab(φ_0) is
  finitely generated.
- G embeds in Aut_G(G∗F_n) by "sending g to the G-automorphism that takes x_1
  to x_1 g and fixes x_2".
- MIF criterion quoted: "Any finitely generated, highly transitive simple group
  is MIF" (Hull–Osin [HO16] Theorem 5.9; Le Boudec–Matte Bon Prop. A.1). V is
  highly transitive through its action on the orbit of 0̄.

**Remark (lane).**
1. The implication (iv) ⇒ (i) is a containment, H ≤ G ↪ Aut_G(G∗F_n). It
   holds for every subgroup H of a finitely presented simple MIF group, finitely
   generated or not. So G has the equivalent "permutational" form: GL_n(Q)
   embeds in a finitely presented simple MIF (or highly transitive) group. That
   does not make G easier. The machine Aut_G(G∗F_n) only helps once some
   finitely presented simple MIF group already contains GL_n(Q).
2. Aut_V(V∗F_n) contains Aut(F_n) and the transvection copies of V∗F_{n−1}, but
   no copy of (Q,+) is visible there. Abelian subgroups of free products lie in
   conjugates of factors or are cyclic (Kurosh), and Q ⊄ V.

## 4. Rational similarity groups (BBMZ)

**Source.** J. Belk, C. Bleak, F. Matucci, M. C. B. Zaremsky, *Hyperbolic groups
satisfy the Boone–Higman conjecture*, arXiv:2309.06224.

- **Definition 2.32 (RSG).** "A subgroup G ≤ R_{Γ,E} will be called a rational
  similarity group (RSG) if, for every pair of cones C_α, C_β ⊊ E with
  t(α) = t(β), there exists g ∈ G that maps C_α to C_β by the canonical
  similarity." Here R_{Γ,E} is the rational group of the subshift of finite type
  Σ_Γ: homeomorphisms with finitely many distinct local actions.
- **Definition 2.24 (full).** "Call G full if [[G | X]] = G", where [[G | X]] is
  the group of homeomorphisms that locally agree with elements of G.
- **Definition 2.41 (contracting).** The nucleus N_G is "the smallest set of maps
  such that for all g ∈ G we have g|_α ∈ N_G for all but finitely many
  α ∈ Cones(E)". An RSG is contracting when "Σ_Γ has an irreducible core and N_G
  is finite."
- **Theorem 3.1.** "Every full, contracting RSG is finitely presented."
- **Corollary.** "Every contracting RSG embeds into a finitely presented simple
  group, and hence satisfies the Boone–Higman conjecture."
- **Theorem A.** "Every hyperbolic group embeds as a subgroup of a finitely
  presented simple group", through [[G | ∂_h G]].
- The paper does not require an RSG to be finitely generated. The fetch found
  no remark on residual finiteness or divisible subgroups of rational groups.

**Remark (lane): a spark I am not pursuing.** Does any contracting RSG, or the
rational group R itself, contain (Q,+)? A contracting RSG containing GL_n(Q)
would settle G at once by the Corollary. Elements are finite-state
(asynchronous) transducers, so infinite divisibility of a single element looks
restrictive. Q ⊄ V is Higman's argument; whether it extends to rational groups
is not recorded in Cairn. Suggested owners: `gq-germ-necessary`,
`gq-calibrator`.

## 5. Piecewise projective groups (Monod, Lodha–Moore)

**Source.** N. Monod, *Groups of piecewise projective homeomorphisms*,
arXiv:1209.5229v2, PNAS 110 (2013) 4524–4527.
- "We define G(A) to be the subgroup of G given by all elements that are
  piecewise in PSL_2(A) with all interval endpoints in P_A." Here G = Homeo_+
  of RP^1, and "P_A ⊆ RP^1 is the collection of all fixed points of all
  hyperbolic elements of PSL_2(A)". H(A) = G(A) ∩ H, where H is the stabilizer
  of ∞.
- Theorem 1.1: "The group H(A) is non-amenable if A ≠ Z." Theorem 1.2: "H does
  not contain any non-abelian free subgroup."
- With rational breakpoints, H(Z) gives Thompson's F and G(Z) gives T (a remark
  attributed to Thurston).

**Source.** Y. Lodha, J. T. Moore, *A finitely presented group of piecewise
projective homeomorphisms*, arXiv:1308.4250v3 (1 Aug 2014). Abstract: "a
finitely presented subgroup of Monod's group of piecewise projective
homeomorphisms of R". It is generated by t ↦ t+1 and two piecewise projective
maps, with three generators and nine relators; Lodha later proved it has type
F∞. The generators and ring were not extracted: the PDF was not read locally,
per the rules.

**Remark (lane) for A = Q.**
1. P^1(Q) ⊆ P_Q: diag(2, 1/2) is hyperbolic and fixes 0 and ∞, and PSL_2(Q) is
   transitive on P^1(Q). So rational breakpoints are allowed in G(Q), and
   G(Q) ⊇ ⟨T, PSL_2(Q)⟩. H(Q) contains x ↦ q²x + b for q ∈ Q^×, b ∈ Q, so it
   contains (Q,+).
2. T's germs at rational points are parabolic. Hyperbolic germs x ↦ λx with
   λ = q² ≠ 1 are new in G(Q). Adjoining one of them to T brings in one set of
   primes only. The question for `gq-pp-*` is whether some finitely generated or
   finitely presented subgroup of G(Q) contains PSL_2(Q).

**Not read (usage limit hit on 2026-09-17); pointers for the gq-pp lanes.**
- arXiv:2204.03278, *Finiteness properties of some groups of piecewise
  projective homeomorphisms*.
- arXiv:1509.04586, Burillo–Lodha–Reeves, *Commutators in groups of piecewise
  projective homeomorphisms*.
- arXiv:2204.08230, Kodama, *An n-adic generalization of the Lodha–Moore
  group*.
- arXiv:2312.10211, *Finiteness properties of generalized Thompson groups via
  expansion sets*.

## 6. Summary for route designers

| Host family | Theorem (hypotheses in §§1–5) | Where GL_n(Q)'s divisible part could live |
|---|---|---|
| Finite germ extension of V (BHM) | Thm 2.1 at n = 2 plus Thm 1.3 (G′ simple) | germ groups (G)_p or SingFix groups, never V (Q ⊄ V) |
| Twisted Brin–Thompson SV_Γ | Zaremsky Thm A / Cor. B: Γ ⊇ GL_n(Q) with a type (A) action | Γ, which must be non-RF (O1) |
| fp simple MIF or highly transitive (BFFHZ) | Thm C / E | the MIF host itself (circular for G) |
| Contracting RSG (BBMZ) | Thm 3.1 plus Corollary | open: can rational groups contain Q? |
| Piecewise projective (Monod, Lodha–Moore) | finite presentation known only for specific subgroups | H(Q) ⊇ (Q,+); G(Q) ⊇ ⟨T, PSL_2(Q)⟩ |

In each route, replacing GL_n(Q) by the perfect group SL_{n+1}(Q) (§1,
Remark 3) puts it inside the commutator subgroup automatically.

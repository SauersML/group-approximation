# ZP review, groups, part 1 (lane z-verify-groups, 2026-09-13)

Scope: establishments in the Zaremsky region for Problems 1.07, 1.10–1.12, 1.20, 1.22, 1.25, all of
Section 2 and all of Section 3, plus z-hub's imports. Verdicts: PASS (argument re-derived and sources
checked as stated), GAP (a step is missing or unjustified), FAIL (false). Graph semantics were checked
with a least-fixpoint pass over `research/*.md` at tip `f1caaea0ab` (routes fire when all requires are
established; routes named in `invalidates:` of an established claim are dead). At that tip the
established Zaremsky roots in this scope are 1.02, 2.06, 2.15, 2.17 and the part claims 2.19(b), 2.19(e).
No root in scope is established through a `requires: []` route into the root itself.

## 1. Problem 1.2 (z-hub, 753718cce)

Nodes: `zaremsky-1-02-type-f3-groups-have-solvable-word-problem`, `zaremsky-1-02-by-no`,
`some-type-f-group-has-unsolvable-word-problem` + `-citation`.

- Source. The cambridge.org chapter page (D. J. Collins, C. F. Miller III, *The word problem in groups
  of cohomological dimension 2*, Groups St Andrews 1997 in Bath, LMS Lecture Note Ser. 260, pp. 211–218)
  was re-read on 2026-09-13. Its abstract says, verbatim: "We show that the finitely presented groups
  with unsolvable word problem given by the Boone-Britton construction have cohomological dimension 2.
  More precisely we show these groups can be obtained from a free group by successively forming
  HNN-extensions where the associated subgroups are finitely generated free groups. Also the
  presentations obtained for these groups are aspherical."
- Type F. A finite aspherical presentation complex is a finite 2-dimensional `K(G,1)`. Independently,
  finitely many HNN extensions of a finite-rank free group along finitely generated free subgroups give a
  finite graph of aspherical 2-complexes with π₁-injective edge maps, which is aspherical (Scott–Wall). So
  `G` is of type F, hence `F_3`.
- Root reading matches the list verbatim; no yes-route; the no-route fires through the import.
- Verdict: **PASS** (import at abstract level, exactly as the route says; the chapter body was not read).

## 2. Problem 2.6 (z-hub, d2cfa3ee9)

Nodes: `zaremsky-2-06-stein-f23-does-not-embed-in-v`, `zaremsky-2-06-by-hyde-skipper-zaremsky`,
`stein-group-f23-does-not-embed-in-thompson-v` + `-citation`.

- Source re-read: arXiv:2605.20564v2 (Hyde, Skipper, Zaremsky; v1 19 May 2026, v2 29 May 2026), HTML.
  Corollary D, verbatim: "The Stein group F_{2,3} does not embed in V." It follows from their Theorem C
  (robust, FG-filtered groups tame at ∞ that embed in V have cyclic finitely generated germ groups at ∞).
  Their definition of `F_{2,3}` (PL orientation-preserving homeomorphisms of [0,1], breakpoints in
  `Z[1/6]`, slopes `2^m 3^n`) matches the node.
- The problem says "Prove ..."; the only admissible answer is the theorem; the route is faithful.
- Verdict: **PASS** (literature import of the list's own note; the proof was not re-derived).

## 3. Problem 2.15 (z-hub, 09d8de801)

Nodes: `zaremsky-2-15-torsion-free-subgroups-of-v-embed-in-f`, `zaremsky-2-15-by-klein-bottle-group`,
`klein-bottle-group-embeds-in-v-but-not-in-f` + `-proof`.

Re-derived every step of the proof route:
- `K = <a, b | bab⁻¹ = a⁻¹> = Z ⋊ Z`, normal form `a^m b^n`, torsion-free and solvable. Correct.
- Embedding into T. With `λ(x) = x/2`, `ρ(x) = (1+x)/2`, `A = λtλ⁻¹ ⊔ ρt⁻¹ρ⁻¹`, `B = ρλ⁻¹ ⊔ λtρ⁻¹`:
  `B` is well defined on the circle (`B(0) = B(1) = 1/2`, `B(1/2) = 0 ≡ 1` from both pieces) and lies in T.
  On `L`: `BAB⁻¹ = (λtρ⁻¹)(ρt⁻¹ρ⁻¹)(ρt⁻¹λ⁻¹) = λt⁻¹λ⁻¹`; on `R`: `(ρλ⁻¹)(λtλ⁻¹)(λρ⁻¹) = ρtρ⁻¹`. Both
  equal `A⁻¹`. `B² = λtλ⁻¹ ⊔ ρtρ⁻¹`, so `A^m B^{2k} = λt^{m+k}λ⁻¹ ⊔ ρt^{k−m}ρ⁻¹`, trivial only for
  `m = k = 0`; odd powers of `B` swap `L` and `R`. Injective. Correct.
- Non-bi-orderability of K (conjugation preserves the positive cone, `bab⁻¹ = a⁻¹`) and bi-orderability of
  F (cone of elements whose first right germ slope exceeds 1: partition, closure under products in the
  three cases, conjugation invariance by reciprocal one-sided derivatives). Correct.
- Verdict: **PASS**.

## 4. Problem 2.17 (z-hub, e8bf5080d)

Nodes: `zaremsky-2-17-t-contains-t-times-t`, `zaremsky-2-17-by-no`,
`thompson-t-has-no-subgroup-isomorphic-to-t-times-t` + `-proof`,
`finite-subgroups-of-thompson-t-are-cyclic` + `-proof`.

- Free action: a finite-order orientation-preserving circle homeomorphism with a fixed point is the
  identity (cut at the point; a nontrivial increasing interval map has strictly monotone orbits).
- Cyclic: an orbit of `n = |G|` points in cyclic order; `g ↦ c(g) ∈ Z/n` with `g(x_i) = x_{i+c(g)}` is a
  homomorphism with trivial kernel. Correct.
- The half rotation is in T, so `T × T ⊇ Z/2 × Z/2`, not cyclic. Correct.
- Verdict: **PASS**.

## 5. Problem 1.22 support lemma (z1-22-lo-simple-bm, 067f470465)

Node: `finite-cd-groups-have-no-micro-supported-line-action` + `-proof`.
- Disjointly supported nontrivial rigid-stabilizer elements commute; finite cd forces torsion-freeness;
  the map `Z^k → G` is injective by restricting to each interval; `cd Z^k = k ≤ cd G`. Items 2 and 3
  follow (a finite `K(G,1)` gives a finite free resolution). Model tests are right.
- Verdict: **PASS**. Not an answer to 1.22; the root stays open.

## 6. Problem 2.18, literal reading (z2-18-f-h2-action, 006d3b3684)

Nodes: `abelian-isometry-groups-of-h2-are-not-cobounded` + `-proof`,
`thompson-f-has-no-cobounded-action-on-hyperbolic-plane` + `-proof`.

- Abelian case. Index-2 orientation reduction (`A·x ⊆ N_c(A⁺·x)`) is right. Centralizers in `PSL_2(R)`:
  the sign case `HGH⁻¹ = −G` forces `tr G = 0` and then `H = [[a,b],[b,−a]]`, of negative determinant, so it
  does not occur; elliptic, hyperbolic and parabolic centralizers are `SO(2)`, the dilations and the
  translations. Orbits lie on a circle, an equidistant curve (distance to the axis is unbounded on `H²`), or
  a horocycle (`log Im z` is 1-Lipschitz). Correct. The model test `Z[1/2] ⋊ Z` is cobounded, as stated.
- F case. `Isom(H²) ≅ O⁺(2,1)` is linear; an image without free subgroups is virtually solvable by the Tits
  alternative (J. Tits, *Free subgroups in linear groups*, J. Algebra 20 (1972), Theorem 1); a free pair in
  the image lifts to a free pair in F, which Brin–Squier exclude. `[F,F]` is infinite, non-abelian and
  simple, hence not virtually solvable (normal-core argument), so `[F,F] ≤ ker ρ` and the image is a
  quotient of `Z²`. Correct.
- Graph: the root does NOT fire, because `zaremsky-2-18-by-no` also requires the open
  `thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2` (the source reading). That is the right
  semantics.
- Verdict: **PASS** for both claims.

## 7. Problem 2.19(e): Q embeds in 2V (z2-19-glnz-q-2v)

Nodes: `zaremsky-2-19e-rationals-embed-in-2v-resolved`, `zaremsky-2-19e-by-yes`,
`rationals-embed-in-brin-thompson-group-2v` + `-proof`.

Re-derived the odometer construction:
- (O1) Piecewise maps `(x, y_j w) ↦ (g_j x, y'_j w)` with `g_j ∈ V` and two partitions of C into cones
  are in 2V (refine by the domain codes of `g_j`). Correct.
- `t(00w) = 0w, t(01w) = 10w, t(1w) = 11w` is in V and `t^k(01w) = 1^k 0w`, so t has infinite order.
- The codes `{0, 10, …, 1^{r−2}0, 1^{r−1}}` are complete; the mixed-radix value `N_n` is a bijection onto
  `{0, …, (n+1)! − 1}` with `N_n = (n+1)N_{n−1} + d_n`.
- `s_n^k = (t^{⌊(N_n+k)/(n+1)!⌋}, digits of (N_n + k) mod (n+1)!)`. For `k = n+1`,
  `N_n + n + 1 = (n+1)(M+1) + d_n` with `M = N_{n−1}`; this is `< (n+1)!` unless `M = n! − 1`, in which
  case it wraps once with remainder `d_n`. So `s_n^{n+1}` increments the first `n−1` digits mod `n!`, fixes
  `d_n`, and applies t exactly on overflow: that is `s_{n−1}`, with `c_{n+1,d_n}` absorbed into the tail.
- `s_0 = t × id` has infinite order, `⟨s_n⟩ ≅ (1/(n+1)!)Z` compatibly, and the directed union is Q.
- Verdict: **PASS**. Wording note (not load-bearing): the claim body's remark that nV has no proper action
  on a CAT(0) cube complex is quoted from Kojima–Sheng and not derived here; say so where it is used.
- Credit: this is not a first answer. Kojima–Sheng, arXiv:2603.18410 (v3 May 2026), Theorem 1.2, give
  continuum many copies of Q in nV (n ≥ 2), before the list's July 12, 2026 version. The node credits them.

## 8. Problem 2.11: braided V is not inner amenable (z2-11-bv-inner-amen, 55604bc42e)

Nodes: `braided-v-is-not-inner-amenable` + `-proof`, `braided-v-kernel-elements-have-equivariant-breakpoint-sets`
+ `-proof`, Haagerup–Olesen imports; artifact `zp-braided-v-not-inner-amenable-2026-09-13.md`.

Re-derived the argument (artifact §§1–4):
- Criterion [HO arXiv:1609.05086, Cor. 3.3, via Rosenblatt]: a non-amenable subgroup H with amenable
  `C_H(f)` for every `f ≠ e` rules out inner amenability. H = a lift of a rank-2 free subgroup of Λ ≅ PSL(2,Z)
  ≤ T; `π|_H` is injective because the composite with π is.
- `f ∉ K`: `C_H(f)` embeds in `C_Λ(π f)`, amenable by the proof of [HO] Thm 3.4.
- `f ∈ K ∖ 1`. Lemma 1.2 (pure representatives, trivial iff β = 1) holds because two representatives have
  a common expansion and cabling is injective. Fact 1.1: forgetting strands is functorial; deleting one of two
  parallel strands returns the original strand; deleting other strands commutes with doubling (Brin's
  splitting is parallel cabling). Lemma 2.1: a minimal nontrivial strand set cannot contain both halves of a
  doubled strand (its image would be smaller and nontrivial), so `r` and the box union `B` are unchanged by
  expansion (both halves `I_{i'}`, `I_{i''}` occur). Lemma 2.2: `f_{σ(Q)}(σβσ⁻¹) = f_Q(σ) f_Q(β) f_Q(σ)⁻¹`
  for pure β, so `M` is transported and `B(hkh⁻¹) = π(h)^{×r} B(k)`. Lemma 3.1: along coordinate circles `B`
  is a finite union of closed dyadic arcs, so `E` is finite and dyadic and transported by `π(h)`; `E ≠ ∅`
  because a nonempty `B` avoids the non-dyadic diagonal points (each box uses `r ≥ 2` distinct leaf arcs).
- `C_H(f)` preserves the finite set E. In PSL(2,Z) only the identity fixes two distinct cusps (parabolics
  fix one cusp, hyperbolics fix quadratic irrationals, elliptics fix no boundary point), so `|E| ≥ 2` gives a
  finite group and `|E| = 1` a subgroup of a cusp stabilizer ≅ Z. Amenable either way.
- Corollary 4.2 (ICC, `L(bV)` without property Γ via Effros [HO] Thm 3.1, overgroups of H) follows.
- Consistency: Bashwinger–Zaremsky (arXiv:2104.04826) show braided F is inner amenable; F contains no Λ.
- Verdict: **PASS**. The held answer route `zaremsky-2-11-by-no` may land. Novelty check requested from
  z-status-b before any first-answer wording.

## 9. Problem 2.19(b): a hyperbolic group outside V (z2-19-hyperbolic-nv, b3800e8705)

Nodes: `zaremsky-2-19b-hyperbolic-group-outside-v-resolved`, `zaremsky-2-19b-by-yes`,
`some-hyperbolic-group-does-not-embed-in-thompson-v` + `-proof`, which requires the existing
`thompson-v-has-haagerup-property` (Farley, IMRN 2003 no. 45) and `torsion-free-hyperbolic-kazhdan-partner-exists`
(a torsion-free finite-index subgroup of a cocompact lattice in Sp(2,1)).
- The chain is standard: the Haagerup property passes to subgroups; an infinite countable group cannot have
  both (T) and the Haagerup property; Sp(n,1) lattices (n ≥ 2) are Kazhdan and word-hyperbolic (Švarc–Milnor on
  a negatively curved symmetric space); Selberg's lemma gives torsion-freeness; infinitude is automatic.
- The reading matches the list's note (Xiaolei Wu) and the answer is credited to him.
- Verdict: **PASS**.
- Adjacent check: Kojima–Sheng's paper exists as cited (arXiv:2603.18410; v1 19 Mar 2026, v2 20 Apr 2026,
  v3 23 May 2026; abstract: "for n≥2, the group nV contains continuum many copies of the additive rational
  numbers Q").

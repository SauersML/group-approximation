---
rg: 2
id: integral-piecewise-projective-groups-are-locally-subgroups-of-f
kind: claim
title: Every finitely generated group of finitely-piecewise PSL_2(Z) homeomorphisms of the line, with any breakpoints and including every finitely generated subgroup of Monod's H(Z), is conjugate in Homeo(R) into Thurston's F; so these groups are amenable iff F is, and co-amenable-host strategies for F inside rational piecewise projective groups are circular
distinct_from:
  f-overgroups-with-a-non-integral-rational-piece-are-nonamenable: that kills every overgroup of F with a non-integral rational piece and leaves the integral overgroups as the only survivors; this shows the integral survivors are locally conjugate into F, so they carry no information F lacks.
  thompson-t-is-isomorphic-to-ppsl2z: that is the circle with rational breakpoints; this is the line with quadratic irrational breakpoints allowed, which leave F, and the odd rescaling that returns them to F.
  thompson-f-co-amenable-hosts-have-integral-end-germs: that proves integrality at the ends and R_G = R_F off Q; this identifies the whole integral group up to local conjugacy with F.
  lodha-moore-breakpoint-orbit-is-hereditarily-amenable-not-ea: that is a calibrator on Q for the Lodha-Moore groups; this is about the PSL_2(Z) pieces only.
  germ-extensions-omit-standard-gl-n-q: that is germ extensions of V; this is a conjugacy statement for line groups.
  quadratic-breakpoint-psl2z-groups-satisfy-boone-higman: that embeds the circle group PP_Z locally in a finitely presented simple group; this conjugates the line group locally into F itself, by an explicit homeomorphism.
  rational-breakpoint-dyadic-pl-groups-satisfy-boone-higman: that is the dyadic PL side with rational breakpoints on the circle; here that PL group on the line is the Minkowski image of the integral projective group, and its finitely generated subgroups rescale into F.
artifacts:
  - experiments/thompson-f-overgroups-2026-09-17/question_mark_localization.py
---

**ESTABLISHED** (lane proof, not reviewed) by
`integral-piecewise-projective-locally-f-proof`. No priority is claimed. The Minkowski dictionary
is classical, and the statement may be folklore; the literature was not searched.

**Setting.**
- `G_Z` is the group of homeomorphisms `g` of `R` with this property: there are finitely many
  points off which `g` agrees, on each complementary interval, with an element of `PSL_2(Z)`.
- The breakpoint condition is automatic. At a breakpoint `ξ` the two adjacent pieces satisfy
  `γ_-^{-1}γ_+ ξ = ξ`. So `ξ` is rational (a parabolic fixed point) or a real quadratic irrational
  (a hyperbolic fixed point).
- Near `+∞` and near `−∞`, `g` is `t ↦ t + n` with `n ∈ Z`. An element of `PSL_2(Z)` that fixes
  `∞` and is increasing is a translation by an integer.
- `F = ⟨a, b⟩` is Thurston's model: the `C^1` piecewise-`PSL_2(Z)` homeomorphisms of `R`
  (Lodha–Moore, arXiv:1308.4250, `vN_fp.tex` l.132–134, l.271–272).
- `F ≤ G_Z`. Monod's `H(Z)`, the piecewise-`PSL_2(Z)` maps with breakpoints fixed by hyperbolic
  elements, is `≤ G_Z` (Monod, arXiv:1209.5229; the definition was not re-read at source).
- `Φ : R → R` is the Minkowski question mark function, extended by `Φ(x + n) = Φ(x) + n`.

**Theorem.**
1. **(Minkowski dictionary.)** `Φ G_Z Φ^{-1} = P`. Here `P` is the group of homeomorphisms `h` of
   `R` that are piecewise `s ↦ 2^k s + d`, with `k ∈ Z` and `d ∈ Z[1/2]`, with finitely many pieces,
   and equal to translations by integers near `±∞`.
   - The breakpoints of an element of `P` are automatically rational.
   - For `g ∈ G_Z` and `h = ΦgΦ^{-1}`: an irrational `x` is a breakpoint of `g` iff `Φx` is a
     breakpoint of `h`. Such `Φx` are non-dyadic rationals. At rational `x`, conjugation can create
     or remove breakpoints, but only at the dyadic point `Φx`. For example, `γ = t/(t+1)` has no
     breakpoint at `0`, yet `ΦγΦ^{-1}` has slope `2` on the left of `0` and slope `1/2` on the right.
   - `ΦFΦ^{-1} = P_1`, the elements of `P` with dyadic breakpoints.
2. **(Odd filtration.)** For odd `M ≥ 1`, let `A_M = (1/M)Z[1/2]` and let `P_M` be the elements of `P`
   with all breakpoints in `A_M`.
   - `P_M` is a subgroup.
   - `P = ⋃_M P_M` is a directed union, with `P_M ∪ P_{M'} ⊆ P_{lcm(M,M')}`.
   - Every finitely generated subgroup of `P` lies in some `P_M`.
3. **(Rescaling.)** `σ_M(s) = Ms` gives `σ_M P_M σ_M^{-1} ⊆ P_1`.
4. **(Local conjugacy into F.)** Let `G_M = Φ^{-1}P_MΦ ≤ G_Z` and `ψ_M = Φ^{-1} σ_M Φ ∈ Homeo(R)`.
   Then `ψ_M G_M ψ_M^{-1} ≤ F`. Hence:
   - `G_Z = ⋃_M G_M` is a directed union of groups, each conjugate in `Homeo(R)` to a subgroup of `F`;
   - every finitely generated `H ≤ G_Z` satisfies `ψ_M H ψ_M^{-1} ≤ F` for some odd `M`.
   - `G_1 = F`. In general `G_M` is the set of `g ∈ G_Z` whose irrational breakpoints `x` all have
     `Φx ∈ A_M`, that is, the odd part of the denominator of `Φx` divides `M`.

**Corollaries.**
- **(C1) Amenability.** `G_Z` is amenable iff `F` is. The same holds for every group `F ≤ G ≤ G_Z`.
  - (⇐) Amenability passes to subgroups and to directed unions.
  - (⇒) `F ≤ G`.
  - For Monod's `H(Z) ≤ G_Z` only (⇐) is claimed: if `F` is amenable, so is `H(Z)`. Its breakpoints
    are hyperbolic fixed points, so `F ⊄ H(Z)`, and the converse is not addressed here.
  - More generally, every property that passes to subgroups and to directed unions of countable
    groups holds for `G_Z` iff it holds for `F`. `G_Z` is countable. Examples: amenability, the
    Haagerup property, having no nonabelian free subgroup, and satisfying a given law `w = 1`.
- **(C2) Answer to NEED `dff8c0a2`, item (1).** Let `H` be Monod's group `H(R)`, which contains `F`
  (Lodha–Moore l.132–134). A nonamenable subgroup of `H` all of whose pieces lie in `PSL_2(Z)`
  exists iff `F` is nonamenable.
  - (⇐) Take `F` itself.
  - (⇒) Such a subgroup lies in `G_Z`. Its finitely generated subgroups are conjugate into `F`, and
    a group is amenable iff all its finitely generated subgroups are.
- **(C3) The maximal amenable overgroup.** Suppose `F` is amenable. Among groups of finitely-piecewise
  `PGL_2^+(Q)` homeomorphisms of `R` containing `F`, `G_Z` is then the unique maximal amenable one.
  - `G_Z` is amenable by C1.
  - Every amenable such group lies in `G_Z`, by part 1 of
    `f-overgroups-with-a-non-integral-rational-piece-are-nonamenable`. A group with a
    non-integral piece is nonamenable.
- **(C4) Class kill: co-amenable hosts in the rational projective world are circular.** Let `G` be a
  group of finitely-piecewise `PGL_2^+(Q)` homeomorphisms of `R` with `F ≤ G`. Any proof that `F` is
  nonamenable by exhibiting such a `G` with `F` co-amenable in `G` and `G` nonamenable dies at the
  host-choice step.
  - If some element of `G` has a non-integral piece, `F` is not co-amenable in `G` (part 1 of
    `f-overgroups-with-a-non-integral-rational-piece-are-nonamenable`).
  - Otherwise `G ≤ G_Z`. By C1, `G` is nonamenable only if `F` already is.
  - The invariant is *local conjugacy into `F`*: every finitely generated integral host is a subgroup
    of `F` up to the homeomorphism `ψ_M`. So an integral host proves nothing about `F` that is not
    already a statement about subgroups of `F`.
  - The same applies to amenability proofs. Følner sets of a finitely generated `H ≤ G_Z` and of
    `ψ_M H ψ_M^{-1} ≤ F` correspond word for word, so enlarging `F` to an integral host gains nothing.
- **(C5) Where the class dies.** The step "choose `G ⊇ F` inside `PP_Q` and transfer" dies on the
  dichotomy "non-integral piece" versus "integral". The first branch dies at the congruence drag of
  `f-overgroups-with-a-non-integral-rational-piece-proof`. The second dies at Theorem 4 here.

**Artifact.** `experiments/thompson-f-overgroups-2026-09-17/question_mark_localization.py` checks,
in exact rational arithmetic:
- (1) `ΦγΦ^{-1}` is dyadic affine on `Φ(I)` for 300 random pairs of `γ ∈ SL_2(Z)` and a Farey
  interval `I`;
- (2) affine maps between standard dyadic intervals pull back to `SL_2(Z)` (200 trials);
- (3) random words in bumps with breakpoints in `(1/15)Z[1/2]` keep them there, and `t ↦ 15t`
  makes them dyadic;
- (4) the breakpoint `1/3` pulls back to `?^{-1}(1/3) = [0;2,1,1,…] = (3 − √5)/2`, a hyperbolic fixed
  point, and the conjugate by `t ↦ 3t` has dyadic breakpoints.

It prints `OK 1`–`OK 4`.

---
rg: 2
id: f-functor-cocycles-need-an-exotic-recurrent-action
kind: claim
title: "A functor cocycle with amenable kernel proves amenability of a group containing F only on an action where F acts faithfully, and via recurrence only through an exotic recurrent F-set whose stabilizers contain no end-rigid subgroup and fix no interior point"
distinct_from:
  thompson-f-recurrent-orbits-have-stabilizers-containing-f: that kills the recurrence criterion whose amenability input is a point stabilizer; this kills the twisted-embedding criterion of Juschenko–Matte Bon–Monod–de la Salle, whose input is the kernel of a functor cocycle, on every action where F acts unfaithfully.
  f-free-groups-are-closed-under-recurrent-extensions: that is a closure theorem for stabilizer-based recurrent extensions; this concerns semidirect products F(X) ⋊ G with a functor F and a cocycle, which that claim does not cover.
  thompson-f-point-orbits-are-transient: that proves every point orbit on (0,1) is transient; this uses its stabilizer constraint to describe which recurrent F-sets a cocycle argument could still use.
  thompson-f-end-rigid-schreier-graphs-are-amenable: that shows Schreier graphs with end-rigid stabilizers are amenable; this shows recurrent ones with end-rigid stabilizers factor through the abelianization.
---

**ESTABLISHED.** **Setting (Juschenko–Matte Bon–Monod–de la Salle, arXiv:1503.04977).**
- `𝐈` is the category of finite sets and injective maps, and `𝐀𝐦𝐞𝐧` the category of
  amenable groups. A functor `𝔉 : 𝐈 → 𝐀𝐦𝐞𝐧` is extended to all sets by direct limits over
  finite subsets. A group `G` acting on `X` acts on `𝔉(X)` by `g ↦ 𝔉(g)`.
- A *cocycle* is a map `c : G → 𝔉(X)` with `c_(gh) = c_g · g(c_h)`, so that
  `g ↦ (c_g, g)` is a homomorphism `G → 𝔉(X) ⋊ G`. Its *kernel* is
  `ker c = {g : c_g = 1}`, which is a subgroup.
- An action `G ↷ X` is *recurrent* if every orbit is recurrent for every symmetric finitely
  supported measure on `G` (JMBMdlS §4.2, quoted in the route).
- `F` is Thompson's group and `F′` its commutator subgroup. A transitive `F`-set `F/H`
  is *exotic* if `H ⊉ F′`. Equivalently, the action does not factor through
  `F/F′ ≅ Z²`.
- `θ : F → G` is an injective homomorphism.

**The method being tested (JMBMdlS, verbatim).**
- Corollary in §1 (source label `prop:functor:amenable:intro`): "Let $G \acts X$ be an extensively amenable action and let
  $F\colon \cati \to \cata$ be any functor. A subgroup $H$ of $F(X) \rtimes G$ is amenable
  as soon as the intersection $H \cap (\{1\} \times G)$ is so."
- Remark after it: "A particular case in which this criterion applies is when one is able
  to construct a \emph{twisted embedding} $G\hookrightarrow F(X)\ltimes G$ of the form
  $g\mapsto (c_g, g)$ with the property that $\{g\in G\: : \: c_g=1\}$ is an amenable
  subgroup of $G$. [...] The conclusion is then that $G$ is amenable."
- Recurrent actions supply the extensive amenability: "Recurrent actions are extensively
  amenable" (Theorem 1.2 of Juschenko–Nekrashevych–de la Salle, as stated in JMBMdlS §4.2).
  In the source, `\cati` is 𝐈, `\cata` is 𝐀𝐦𝐞𝐧 and `\acts` is `↷`. Text read from the
  arXiv source of 1503.04977 on 2026-09-17.

**Statement.** Let `G ↷ X`, `𝔉`, a cocycle `c` and `θ` be as above. Let
`N = {n ∈ F : θ(n) acts trivially on X}`.
1. **Cocycle collapse.** If `N ≠ 1`, at least one of the following holds:
   - `ker c ∩ θ(F)` contains a subgroup isomorphic to `F`;
   - for some finite `A ⊆ X`, the image of `𝔉(A) → 𝔉(X)` contains a subgroup
     isomorphic to `F`.
   So proving that `ker c` is amenable, or that `𝔉(A)` is amenable, already requires
   amenability of `F`. No extensive amenability is assumed here.
2. **Dichotomy.** If `G ↷ X` is recurrent, then either `N ≠ 1` and item 1 applies, or some
   `θ(F)`-orbit is an exotic recurrent `F`-set.
3. **End-rigid collapse.** Let `F/H` be a recurrent `F`-set and `c ∈ (0,1)`. If `H`
   contains `F_[0,c]` (the elements that are the identity on `[c,1]`), then `H` contains
   every element that is the identity near `1`, hence `H ⊇ F′`. The same holds with
   `F_[c,1]` and "the identity near `0`".
4. **Profile of an exotic recurrent `F`-set `F/H`.** Every conjugate of `H`:
   - contains a subgroup isomorphic to `F`
     (`thompson-f-recurrent-orbits-have-stabilizers-containing-f`);
   - meets every subgroup `Z³ ≤ F` nontrivially
     (`recurrent-orbits-force-every-z3-to-meet-the-stabilizer`);
   - meets every rigid copy `F_p` in a group with no fixed point in `int [p]`
     (`thompson-f-point-orbits-are-transient`);
   - contains no `F_[0,c]` and no `F_[c,1]` (item 3).

**What is killed.** This covers every proof that some `G ⊇ F` is amenable by the
twisted-embedding method, with any functor `𝔉` and any cocycle, run on an action on
which `F` acts unfaithfully. For example, `F` might act through its germs at the
endpoints, through `F/F′`, or trivially.
- *Invariant:* "contains a section isomorphic to `F`".
- *Where every member dies:* either the kernel step ("`ker c` is amenable") or the
  functor step ("`𝔉(A)` is amenable"). In each case the offending copy of `F` is the
  image of a nontrivial normal subgroup of `F`.

When the extensive amenability comes from recurrence, a surviving member needs an exotic
recurrent `F`-set with the profile of item 4. None is known.
- By `thompson-f-point-orbits-are-transient`, no `F`-set whose stabilizer fixes an
  interior point qualifies.
- By item 3, no `F`-set whose stabilizer contains an end-rigid subgroup qualifies.
- Whether any exotic recurrent `F`-set exists is
  `thompson-f-recurrent-f-sets-factor-through-the-abelianization` (OPEN). A proof of that
  claim kills the recurrence-plus-functor-cocycle route to amenability of every group
  containing `F`.

**Scope.**
- Extensive amenability obtained without recurrence, on a faithful action, is untouched.
  An example is the dyadic action, where the breakpoint cocycle has trivial kernel.
- The argument uses only the cocycle identity, the functor axioms and the normal-subgroup
  import. No priority is claimed.

Proof route: `f-functor-cocycles-need-an-exotic-recurrent-action-proof`.

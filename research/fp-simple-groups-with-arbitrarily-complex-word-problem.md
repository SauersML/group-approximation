---
rg: 2
id: fp-simple-groups-with-arbitrarily-complex-word-problem
kind: claim
root: true
title: For every recursive time bound some finitely presented simple group has a harder word problem
distinct_from:
  simple-envelope-forces-solvable-word-problem: that says every finitely presented simple group has solvable word problem; this asks that those solvable word problems are not uniformly bounded by any recursive time function.
  complexity-bounded-host-classes-are-not-universal: that is the established non-universality theorem for bounded host classes; this is the open existence statement for the specific class of all finitely presented simple groups, which the conjecture would force.
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

**OPEN.** For every recursive `T: N -> N` there is a finitely presented simple
group `S` whose word problem has no algorithm running in time
`C*T(C*l) + C*l + C` for any constant `C`.

Every finitely presented simple group has solvable word problem
(`simple-envelope-forces-solvable-word-problem`), so this asks only that the
class have no uniform recursive complexity bound. By
`complex-fp-simple-groups-from-boone-higman` it is a **necessary consequence**
of `boone-higman-conjecture`. A proof of the conjecture must therefore, among
other things, construct finitely presented simple groups beyond every recursive
time bound. That is a concrete test for any proposed universal envelope: its
word problems must be unboundedly complex, i.e. the construction must consume
the input's algorithm, as
`compilers-cannot-drop-the-decidability-hypothesis` already says in a
different form.

It is a root because it is independently well posed, strictly weaker than the
conjecture, and not implied by any established node here.

## What is known

Every finitely presented simple group whose word-problem complexity has been
determined is easy. The hardest known case is due to Birget, *The word problem
of the Brin--Thompson group is coNP-complete*, arXiv:1902.03852, read from the
abstract 2026-09-11: "the word problem of the Brin--Thompson group nV over a
finite generating set is coNP-complete for every n >= 2". Each `nV` is infinite,
finitely presented and simple. coNP lies inside `2^(n^O(1))` time, so the whole
known Thompson-like family sits under one recursive bound. By
`complexity-bounded-host-classes-are-not-universal`, or its finitely presented
residually finite form `uniform-wp-bound-excludes-bh-universal-targets`, that
family is non-universal for Boone--Higman. (This paragraph was carried over from
the retired duplicate root `bh-forces-unbounded-fp-simple-wp-complexity`.)

## Attempts

1. **Twisted Brin--Thompson groups over complex actors.** A finitely
   presented group with a type (A) action whose word problem beats `T` would
   give a simple example through
   `type-a-action-gives-boone-higman-for-subgroups`. The candidate actors in
   this graph are the shift envelope `infinite-shift-higman-compiler`, the
   shell envelopes `perfect-decidable-inputs-have-fp-shell-envelopes`, and the
   fiber-product data `universal-fiber-product-data-for-word-problem-groups`.
   All are open.
2. **Finitely presented self-similar hosts.** Via
   `fp-self-similar-groups-embed-in-fp-simple-groups`, it would suffice to
   embed algorithmically complex finitely presented residually finite groups
   in finitely presented self-similar groups, a special case of
   `every-fp-rf-group-embeds-in-fp-self-similar-group`. By its condition
   (N2) those hosts cannot be automaton groups.
3. **Classical Thompson-like hosts.** *Dies as a method* by
   `complexity-bounded-host-classes-are-not-universal`: any family sharing
   one recursive bound, such as all rational homeomorphism groups, cannot
   supply the needed examples.
4. **Finite germ extensions of `V` certified by the Belk--Hyde--Matucci germ
   corollary.** *Dies as a family, under orbit-preserving transports* (2026-09-13,
   `orbit-preserving-germ-corollary-extensions-of-v-are-rational`).
   - *The theorem.* Let `G` be a finitely generated finite germ extension of `V`
     satisfying, at each singular point, hypothesis (2) of Corollary 2.10 for
     singletons and the either-or of hypothesis (3). If every element maps each
     singular point into its own `V`-orbit (for instance when `sing(G)` is one
     `V`-orbit), every element of `G` is rational, so `G` and all its subgroups
     have word problem in `F(2^n)`.
   - *Where hardness can still enter this branch.* Theorem 2.1 with germ groups
     that normalize no finite-index subgroup of their `V`-germs, as for shell
     envelopes of non-virtually-cyclic inputs; or a singular transport between
     different `V`-orbits, where a germ may apply unboundedly many iterates of a
     fixed annulus map. No finitely presented example of either kind is known.
   - *Provenance.* Birget, arXiv:math/0310335 §1, states this root as a
     consequence of a conjecture he attributes to Higman, reports every analyzed
     finitely presented simple group in `P`, and says neither side "ha[s] much
     evidence". Zaremsky (arXiv:2305.15176) gives the first finitely presented
     simple groups with at least exponential Dehn function; that bounds nothing
     here from below. Pins in `research/artifacts/hl-bh-hard-simple-2026-09-13.md`.
5. **Faithful finite-index HNN extensions of hard vertex groups** (bh-free-02,
   2026-09-18). `finite-index-edge-hnn-embeds-in-fp-simple-group` needs no envelope
   for the vertex group. So one finitely presented residually finite `A` with a hard
   word problem and a faithful HNN extension over finite-index subgroups would settle
   this root.
   - *Scaling shape: dies.* For `A = M ⋊ H` with `M` elementary abelian and a
     scaling fixing `H`, which is the shape a Kharlampovich--Myasnikov--Sapir group
     `T ⋊ H` offers first, faithfulness forces `A` to be linear over `F_p((x))`
     (`equivariant-scaling-hnn-vertex-groups-are-linear`). Linear groups share the
     classical low bound, so this shape cannot supply hard inputs.
   - *Still open:* scalings that move `H`; non-ascending extensions over two proper
     edges whose isomorphism is not the restriction of an automorphism.
   - Notes: `research/artifacts/gq-bh-bh-free-02-complexity-root-notes.md`.
6. **Germ extensions of `V` whose hardness sits in one free tail parameter.**
   *Dies at finite presentation, with no germ hypothesis* (2026-09-17,
   `tail-uniform-germ-extensions-of-v-are-not-fp`).
   - *The class.* `G = < V, g_1, ..., g_m >`, each `g_i` read off one point `x` by
     a finite tail template: prefix replacements plus finitely many relative
     shifts at singular points `a σ^j x`. The model is `h_x`, which shifts the
     annuli `C(x|n ¬x_(n+1))` down by one around `x`. For computable `x` its word
     problem computes `x`, so these groups beat every recursive bound.
   - *Where every member dies.* If `x` is not eventually periodic and some
     singular germ is not a `V`-germ (nonzero tail offset), `G` is not finitely
     presented. Each relation is decided by a finite prefix of `x` (locality), and
     flipping one deep bit gives a marked group satisfying every relator of a
     candidate finite presentation but failing a conjugation relation. This is
     the Grigorchuk `G_ω` mechanism. So every finitely presented member is
     rational and falls under Attempt 3.
   - *What it closes.* The single-tail case of Attempt 4's "singular transport
     between different `V`-orbits", in which the singular points are shifted
     copies of one aperiodic tail. What stays open is germs that apply
     unboundedly many rules at one singular point, and germ groups given by
     other finitely presented groups acting on the tail.
6. **Piecewise prefix-and-automaton hosts are capped** (bh-free-02, 2026-09-18).
   `automaton-tail-full-groups-have-conp-relative-word-problem` covers every
   finitely generated group of homeomorphisms that act piecewise by prefix
   replacement followed by elements of automaton groups `H_i` on the tails. This
   includes `nV`, Rover--Nekrashevych groups of automaton groups, and the product
   2-graph hosts `2V_τ` and `2V_H`. Each such group has word problem in
   `coNP^{WP(H_i)}`, and hence in `PSPACE`.
   - *Dies as a family* for this root: the family shares the bound `PSPACE`.
   - *Calibration.* The new hosts `2V_τ` and `2V_{G_N}` are coNP-complete, exactly
     Birget's level. Zaremsky's exponential-Dehn hosts have word problem in `coNP`.
   - *Beating coNP needs a finitely presented automaton group with word problem
     outside `P`,* for example `NP`- or `PSPACE`-hard. It then passes up through
     Zaremsky's Theorem 1.1. Beating every recursive bound needs infinite-state
     coefficient groups.
7. **Linear superposition beats coNP: `(L ⊗ L)^x` is `coNP^⊕P`-complete** (bh-free-26,
   2026-09-18, `leavitt-square-units-have-conp-parity-p-complete-word-problem`; lane proof,
   not reviewed).
   - *Result.* The group `(L_(F_2)(1,2) ⊗ L_(F_2)(1,2))^x` has word problem complete for
     `coNP^⊕P = ∀·⊕P`, so it is outside PH unless PH collapses (Toda). Hardness for an
     explicit finitely generated subgroup and the upper bound are unconditional. That the
     group is finitely presented and simple comes from
     `leavitt-square-unit-group-is-fp-simple-and-acyclic`, **conditional on the Khanh and
     Ara--Cortiñas imports**. Modulo those imports and the standard hypothesis, it is the
     first finitely presented simple group here beyond Birget's coNP level. Cross-checked
     by bh-free-02 (math PASS, e0faf3f03).
   - *Mechanism.* The superposition letters `τ = s_0 + s_1` and `σ = t_0 + t_1` enter through
     slot units and one commutator. The second tensor factor supplies baker scrolling, so
     reversible circuits have polynomial length. This is not a piecewise-prefix host, which is
     why item 6's cap does not apply: its elements are linear combinations, not homeomorphisms.
   - *Every prime.* With a characteristic-free slot unit, the (conditionally) finitely presented simple group
     `(L_(F_p)(1,2)^(⊗2))^x / F_p^x` has `∀·Mod_pP`-complete word problem, for every prime `p`
     (`leavitt-square-units-mod-p-complete-word-problem`). By Toda--Ogiwara,
     none of these word problems lies in PH unless PH collapses.
   - *Limit, now a theorem.* `leavitt-tensor-unit-word-problems-have-one-counting-quantifier`:
     every finitely generated linear group over any Leavitt tensor algebra over `F_q` has word
     problem in `∀·Mod_pP`. Over `Z[1/M]` the bound is `C_=P`, attained by an integral group
     `Γ_Z`. So more tensor factors give nothing new, and this family can reach `PSPACE` only
     if `PSPACE ⊆ ∀·Mod_pP` or `PSPACE = PP`. The obstruction is finite depth. Beating it
     needs self-similar elements, as in item 6. Boone--Higman applied to `Γ_Z` predicts a
     finitely presented simple group with `C_=P`-hard word problem.
8. **Hard real parameters in PL hosts: die by order rigidity** (bh-free-32, 2026-09-18; lane
   proofs, not reviewed).
   - *Idea.* Keep the combinatorics of a Thompson-like host, but let one breakpoint or slope be a
     computable transcendental `λ` whose digits are hard. A bump `u` with endpoint `e(λ)` and an
     `F`-bump `k_r` on `(r, 1)` commute iff `e(λ) < r`, so the word problem decides the digits.
   - *Dies.* `fp-pl-groups-with-f-have-no-transcendental-support-endpoints`: no finitely
     generated PL group of an interval or circle with data in `Q(λ)` that contains a dyadic `F`
     and such a bump is finitely presented. The reason is that the finitely many relators persist
     when `λ` moves slightly, while `[u, k_r]` does not. For line groups,
     `fp-bieri-strebel-line-groups-are-deformation-rigid` shows more: a finitely presented
     `G(R;A,P)` has algebraic slopes, and its breakpoints lie in `Q(P)` after rescaling. So its
     parameters live in a number field, where the word problem is arithmetic of bounded
     complexity. This also shows that the necessary conditions of Bieri--Strebel D13.3 are not
     sufficient, e.g. for `G(R; Z[1/2] + Z[1/2]τ, gp(2))` with any irrational `τ`.
   - *Update (bh-free-32): every definable-parameter host dies.*
     `definable-parameter-hosts-cap-simple-subgroups-at-pspace` covers two kinds of host: groups
     acting by semialgebraic bijections in any dimension, and groups acting on Cantor space by
     ω-automatic bijections (`V`, `nV`, Röver--Nekrashevych, extended along arbitrary addresses).
     In both, the parameters may be arbitrary real numbers or arbitrary addresses. If such a group
     is finitely presented, it specializes to tame parameters on every finite set. So its finitely
     generated simple subgroups, and every input they contain, have word problem in PSPACE. This
     family therefore shares one bound for this root.
     `fp-piecewise-projective-groups-rigidity-criterion` gives the matching test for finite
     presentation, e.g. `⟨F, F^λ⟩` is not finitely presented for transcendental `λ`.
   - *Lesson.* Hardness has to sit in the combinatorial rule of the host, not in its constants,
     and its generators must not be definable in a decidable tame structure. Notes:
     `research/artifacts/gq-bh-bh-free-32-order-rigidity.md`.
9. **Transcendental-slope Thompson groups as inputs** (bh-free-19, 2026-09-18; lane proof, not
   reviewed). Route `arbitrarily-complex-fp-simple-via-transcendental-slope-thompson`.
   - *Established half.* `transcendental-slope-thompson-groups-have-hard-word-problems`. The Sturmian
     detector `[u', ρ^n w' ρ^{-n}] = 1 ⟺ ⌊(n+1)λ⌋ = ⌊nλ⌋` lives inside `D(V_λ)`, which contains no
     dyadic `F`. With a Liouville `λ` that carries hard digits, this makes the 2-generated simple
     group `D(V_λ)` beat any given recursive `T`.
   - *Open half.* `transcendental-slope-thompson-groups-satisfy-boone-higman`. Attempt 8 excludes PL
     hosts carrying `λ`. So a host must compute `λ`'s digits by other means, and this route shows the
     open half is at least as strong as this root.
   - *Every one-dimensional piecewise-projective host is capped* (same lane):
     `fp-piecewise-projective-groups-specialize-to-algebraic-data`. A finitely presented simple group
     of piecewise-projective maps of an interval, circle or line, with arbitrary real data, is
     isomorphic to one over a real number field and has polynomial-time word problem. This settles
     the piecewise-projective part of Attempt 8's "still open" item; germ-type hosts remain.
10. **Twisted Brin--Thompson towers climb the polynomial hierarchy, exactly** (swarm-0917-w23
    bh-break, 2026-09-20; lane proof, unreviewed): `twisted-bt-towers-climb-the-polynomial-hierarchy`.
    - *The tower.* Start from `G_0 = F` acting on the dyadics, and put
      `G_(k+1) = SV_(G_k)`, acting on the clopen sets of its cube.
    - *The result.* Each `G_k` is finitely presented and simple, with a
      `Π^p_k`-complete word problem. This holds unconditionally, under deterministic
      many-one reductions.
    - *The engine, Lemma Q.* A labelled branch `τ_t` controlled by the workspace
      digits of two coordinates `a, b` fixed by `t` is an element of `SV_G`, and it
      leaves the workspace in place. So a universally quantified `y`, written in
      those digits, selects one letter of an actor word per Birget-style reversible
      circuit. The fiber over `y` then carries the actor word `Φ(z,y)`, and a single
      coordinate `r` reads off `∀y Φ(z,y) r != r`.
    - *The layer count.* Each layer adds exactly one alternation. This replaces the
      heuristic "iteration stays elementary", which is an upper bound only.
    - *The cap.* Towers over `PSPACE` actors stay in `PSPACE`, since
      `coNP^PSPACE = PSPACE`, and infinite towers are not finitely presented. So this
      closes the whole twisted-BT-iteration family below `PSPACE`, from both sides.
    - *Status.* The root stays OPEN. The first open rung is now a single finitely
      presented simple group with `PSPACE`-hard word problem, which needs unbounded
      alternation inside one finitely presented group.

---
rg: 2
id: every-decidable-group-embeds-in-an-isolated-group
kind: claim
title: Every finitely generated group with solvable word problem embeds in an isolated group (Cornulier--Guyot--Pitsch Question 4)
distinct_from:
  boone-higman-conjecture: that asks for a finitely presented simple overgroup and implies this, since finitely presented simple groups are isolated; this asks only for a finitely presented, finitely discriminable overgroup, which CGP print as a separate, weaker question.
  permutational-boone-higman-conjecture: that asks for a finitely presented overgroup with a type (A) action; this asks for a finitely presented, finitely discriminable overgroup and does not mention actions.
  decidable-groups-embed-in-outer-extensions-of-fp-simple-groups: that is a specific sufficient condition, an overgroup that is an outer extension of a finitely presented simple group; this is the printed question itself.
  linear-and-metabelian-groups-embed-in-isolated-groups: that is this question answered on the finitely generated quasi-linear groups; this is the question for all groups with solvable word problem.
---

**OPEN.**

**The printed question.** Cornulier--Guyot--Pitsch, *On the isolated points
in the space of groups*, arXiv:math/0511714, read on 2026-09-13 from the TeX
source on MSI (`/scratch.global/sauer354/bh-isolated/math_0511714.tex`). It is
the fourth `question` environment, lines 828–834, verbatim:

> "Does every finitely generated group with solvable word problem embed into
> an isolated group?"
>
> "Note that the stronger well-known question whether every finitely
> generated group with solvable word problem embeds in a finitely presented
> simple group is open."

**Terms.** A group is isolated iff it is finitely presentable and finitely
discriminable (CGP Proposition, lines 554–557). Finite discrimination is the
existence of a finite `F ⊂ G − {1}` meeting every non-trivial normal subgroup
(Proposition--Definition, lines 519–533).

**Why solvable word problem is necessary.** CGP (line 705): "An isolated group
has solvable word problem." A finitely generated subgroup of a group with
solvable word problem has solvable word problem, so the hypothesis cannot be
dropped.

**Known cases.** `linear-and-metabelian-groups-embed-in-isolated-groups`:
every finitely generated group linear over a finite product of fields,
including every finitely generated linear or metabelian group. More generally,
every group on main that is known to embed in a finitely presented simple
group.

## Attempts

1. **Permutational wreath monoliths.**
   - **Sources.** CGP Proposition `prop wreath_nocentre`: `W ≀_X G` is finitely
     discriminable when `X = G/H` is faithful and transitive and `W ≠ 1` is
     finitely discriminable with trivial centre. Their Theorem
     `thm wreathfinpres`, due to Cornulier (arXiv:math/0509090, Theorem in §1,
     TeX lines 147–157): for `W ≠ 1`, `W ≀_X G` is finitely presented iff `W`
     and `G` are finitely presented, `H` is finitely generated, and `G` has
     finitely many orbits on `X x X`.
   - **Reduction.** So an isolated wreath monolith over a faithful transitive
     `X`, with `W` finitely presented and centreless, is exactly a type (A)
     action of `G` (`type-a-action-gives-boone-higman-for-subgroups`: finitely
     many orbits on ordered pairs is equivalent to finitely many orbits on
     two-element subsets). An input placed in `G` already lies in the
     permutational Boone--Higman class. A finitely generated input placed in
     the base `W^(X)` lies in a finite product `W^n`.
   - **Verdict.** Killed as a new route: it reduces to
     `permutational-boone-higman-conjecture`, or to subgroups of products of
     one finitely presented group.
2. **Split outer actions on one fixed simple group.**
   - **Setup.** Let `Q ≤ Aut(S)` be finitely generated with `Q ∩ Inn(S) = 1`.
   - **Why it fails.** `q = 1` in `Q` iff `q` fixes the finitely many generator
     images of `S`, so the word problem of `Q` reduces to that of `S` with a
     recursive time bound depending only on `S`. By
     `complexity-bounded-host-classes-are-not-universal`, no single `S` serves
     every input this way. This is a hand argument, first noted in
     `research/artifacts/ideas-2026-09-13/bh/bh-ec-groups.md`, approach 2.
   - **Verdict.** Killed for a fixed `S`; `S` must depend on the input.
3. **Non-split outer extensions of a fixed simple group.**
   - **Setup.** Let `1 → S → I → Q → 1` with `Q → Out(S)` injective.
   - **Original remark (superseded; see Status).** Here `q = 1` iff some lift of
     `q` acts on `S` by an inner automorphism. That is a search for a conjugator
     in `S`, with no time bound depending only on `S`. So one fixed `S` is not
     ruled out by `complexity-bounded-host-classes-are-not-universal`: the
     overgroup `I` varies with the input, and so does its word-problem
     complexity. This is a hand remark.
   - **Status.** Refuted on 2026-09-13 by
     `outer-extension-word-problem-is-kernel-bounded` (lane
     solve-bh-outer-ext).
     - The innerness search above decides triviality in the quotient `Q`, but
       the input must sit in `I`.
     - Since `C_I(S) = 1`, `I` embeds in `Aut(S)`, and the word problem of `I`
       reduces to that of `S` after one exponential substitution.
     - So one fixed `S`, split or not, is excluded by
       `complexity-bounded-host-classes-are-not-universal`.
     - The outer-extension route therefore needs unboundedly complex simple
       kernels, as the conjecture does
       (`complex-fp-simple-groups-from-outer-extensions`).
4. **Locally moving hosts (2026-09-17, lane swarm-0917-w5-bh-heretic).** *New
   decomposition, one half established, one half open.*
   - **Established half.** `fp-groups-with-a-locally-moving-simple-subgroup-are-isolated`.
     Let `Γ` act faithfully, and let `T ≤ Γ` be either a simple group of homeomorphisms of
     a Hausdorff space whose rigid stabilizers of open sets are nonabelian, or
     `Alt_fin(X)`. Then every nontrivial subgroup normalized by `T` contains `T`, and
     `ncl_Γ(T)` is a simple monolith with trivial centralizer. So `Γ` is isolated as soon
     as it is finitely presented. `T` need not be normal, finitely generated or finitely
     presented, which is what separates this from Attempts 2–3 and from
     `isolated-overgroup-via-outer-extensions`. Examples: every finitely presented
     `Γ ≤ Homeo(C)` containing `V`, Thompson's `F` and `T`, and Houghton's `H_n` with
     `n ≥ 3`.
   - **Open half.** `decidable-groups-embed-in-fp-locally-moving-groups`, with route
     `isolated-overgroup-via-locally-moving-hosts`. It is implied by
     `permutational-boone-higman-conjecture` (hand remark via twisted Brin--Thompson
     groups). On Cantor hosts it upgrades to Boone--Higman exactly when the full closure
     `[[Γ]]` is finitely presented (landed type (A) criterion on origin/main).
   - **Kills recorded there.**
     - No infinite LEF group is isolated: a finitely presented LEF group is residually
       finite, and residual finiteness plus a finite discriminating set forces
       finiteness. So no approximation-built host works.
     - Free lampshufflers `FSym(H) ⋊ H` satisfy (fin) but are never finitely presented
       over infinite `H` (Genevois--Tessera, as recorded in
       `lampshuffler-groups-are-not-fp2-over-q`). That would have given Question 4
       outright from Clapham's decidable finitely presented overgroups. My own attempt
       on `H = Z^2` stalled: local transposition relations do not visibly imply far
       commutations, since the induction on distance stalls at radial edges of the grid.
       This agrees with that theorem.
     - The kernel-bounded complexity argument of Attempt 3 does not exclude one fixed
       `T = V`, because `V` is not normal and `ncl_Γ(V)` need not be finitely generated.
   - **Counterexample direction.** A decidable group defeating this route must have no
     finitely presented overgroup with a faithful locally moving action. No invariant was
     found that such hosts force beyond solvable word problem, non-LEF and non-residually
     finite, and those constraints bind the host, not the input.
5. **Finiteness of locally moving hosts (2026-09-17, lane swarm-0917-w5-bh-cgp-q4).**
   *Class kill for branch (fin), reduction for the V-branch of (top).*
   - **(fin) is exactly PBH.** `permutational-boone-higman-iff-finitary-alternating-hosts`.
     - Every finitely presented `Γ ≤ Sym(X)` containing `Alt_fin(X)` acts with type (A)
       (`fp-finitary-alternating-overgroups-have-type-a-actions`: correct generators by
       finitary even permutations and glue alternating groups along overlaps).
     - Conversely a type (A) actor `Γ_0` gives the finitely presented isolated host
       `FSym(Ω) ⋊ SV_{Γ_0}` over the proper clopens `Ω`
       (`finitary-symmetric-extensions-of-oligomorphic-actions-are-fp`, a Coxeter
       presentation using finitely many orbits on 4-tuples).
     - So branch (fin) of Attempt 4 proves Boone--Higman for its inputs. It carries no
       content beyond `permutational-boone-higman-conjecture` and cannot answer this
       question in a way weaker than Boone--Higman. Houghton's `H_n` and `FSym(Ω) ⋊ V`
       are finitely presented isolated examples.
   - **V-hosts reduce to one finiteness condition.**
     `fp-cantor-groups-containing-v-type-a-iff-clopen-stabilizer-fg`. A finitely presented
     `Γ ≤ Homeo(C)` containing `V` acts faithfully and transitively on clopens with at most
     five orbits of pairs. So it is a type (A) actor iff one clopen stabilizer is finitely
     generated.
   - **Where the remaining room is.** A host-geometry answer to this question that is
     strictly weaker than PBH must use one of:
     - a finitely presented `Γ ≥ V` in `Homeo(C)` with a non-finitely-generated clopen
       stabilizer;
     - a (top) host on a non-Cantor space;
     - an isolated host that is not locally moving at all.
     None is known here. The attempt made no progress on the (top) stabilizer question.
   - **Relevance to Boone--Higman.** The bus result `local-boone-higman-iff-boone-higman`
     (other lane, same wave; not yet on this branch) makes Local Boone--Higman equivalent
     to Boone--Higman. So this question is not needed as a half of
     `boone-higman-iff-isolated-hosts-and-local-boone-higman`; it stays open as CGP's own
     question.
6. **Permanence and new monolith shapes (2026-09-18, lane bh-free-05).** *Partial results, not a
   solution.*
   - **Permanence.** `ascending-hnn-of-isolated-groups-embed-in-isolated-groups`. The class of
     groups embedding in isolated groups is closed under finite products and finite extensions,
     because `J ≀ S_k` is isolated for every isolated `J`. It contains every ascending HNN
     extension `I*_α` of an isolated group, for any injective endomorphism `α`. So it contains
     `S*_α` for every finitely presented simple `S`, MIF or not, surjective or not; the
     Boone--Higman analogue is on main only in special cases. For the Baumslag--Gersten group
     this gives a criterion: `BG` embeds in an isolated group iff `C = ncl(a)` embeds in an
     isolated group whose automorphisms extend the shift `a_n ↦ a_(n+1)`, iff some
     homomorphism to an isolated group is injective on `C`. Not settled.
   - **Abelian and central monoliths.** Two shapes, both finitely discriminable, not covered
     by Attempts 1–5:
     - (a) `Γ` with an abelian minimal normal `M` and `C_Γ(M) = M`. If `N ∩ M = 1` then
       `[N, M] = 1`, so `N ⊆ M` and `N = 1`.
     - (b) Heisenberg hosts `H(V) ⋊ Q`, `p` odd, with `V` a faithful nondegenerate
       symplectic `F_p Q`-module. The centre `<z>` is contained in every nontrivial normal
       subgroup, since a noncentral element of `H(V)` has commutator `z^c`, `c ≠ 0`, with
       some element, and `C_Γ(H(V)) = <z>`.
   - **Where they stop.** If `M` (or `V`) is a permutation module `F_p[X]`, its augmentation
     submodule, or a sum of copies, then `Γ` is commensurable with a quotient of
     `W ≀_X Q` by a finite normal subgroup, with `W` finite abelian. Cornulier's criterion
     (Attempt 1) then forces finitely many `Q`-orbits on `X × X` and finitely generated
     stabilizers, a type (A) action. So these shapes add nothing beyond PBH. Non-permutation
     modules stay open.

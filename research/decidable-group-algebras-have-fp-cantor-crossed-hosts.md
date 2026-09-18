---
rg: 2
id: decidable-group-algebras-have-fp-cantor-crossed-hosts
kind: claim
title: Every decidable group algebra over F_2 embeds in a finitely presented central simple crossed product LC(X, F_2) ⋊ P over a torsion-free Farrell–Jones group
distinct_from:
  decidable-group-algebras-have-fp-central-simple-hosts: that asks for any finitely presented central simple host B with K_1 and K_2 of B ⊗ L zero; this restricts B to crossed products LC(X, F_2) ⋊ P over torsion-free Farrell–Jones groups, where the K-theory condition is automatic, and asks only for existence.
  free-minimal-z2-sft-is-quantum-rigid: that asks for one finitely presented crossed product of a free minimal Z^2-SFT over some field; this asks for a family of crossed products over F_2, by arbitrary torsion-free Farrell–Jones groups, containing every decidable group algebra.
  decidable-group-ring-has-fp-projective-simple-host: that asks for ring hosts whose projective elementary groups are finitely presented and simple; this asks for algebra hosts of a fixed dynamical shape and says nothing about elementary groups.
artifacts:
  - research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md
  - research/artifacts/fp-crossed-product-shape-free-group-kill-2026-09-17.md
---

**OPEN.** Let `G` be a finitely generated group with solvable word problem.
Then there are:
- a torsion-free group `P` satisfying the `K`-theoretic Farrell–Jones conjecture
  with additive categories as coefficients, with respect to `VCyc`;
- a nonempty compact totally disconnected Hausdorff `P`-space `X`,

such that `B = LC(X, F_2) ⋊ P` is finitely presented as an `F_2`-algebra, is
simple, has centre `F_2`, and admits a unital embedding `F_2[G] -> B`.

**Why it matters.** With `cantor-crossed-product-leavitt-tensors-are-k-trivial`
it gives `decidable-group-algebras-have-fp-central-simple-hosts` (route
`fp-central-simple-hosts-via-cantor-crossed-products`), and hence
`boone-higman-conjecture` through `boone-higman-via-central-simple-leavitt-tensor-host`.
So, granted that chain (which rests on
`leavitt-tensor-hosts-acyclic-steinberg-and-fp`, conditional on the imported
criteria of Khanh arXiv:2609.08428v1), it is at least as hard as Boone–Higman.

**Necessary shape** (artifact Section 6, proved there).
- If `B` is finitely generated, then `P` is finitely generated and `X` is
  conjugate to a `P`-subshift.
- If `P` is infinite and `B` is simple, the action is minimal and `X` is
  infinite.
- A minimal topologically free action gives `Z(B) = F_2`.
- No single pair `(P, X)` serves every `G`. Its host `B` would make
  `(B ⊗ L)^x` one finitely presented simple group containing every such `G`
  (by the route into the target and `boone-higman-via-central-simple-leavitt-tensor-host`),
  and `complexity-bounded-host-classes-are-not-universal` forbids that.

## Attempts

1. **`P = Z`. Dies.** Simplicity forces an infinite minimal subshift, and
   `minimal-subshift-crossed-product-is-not-finitely-presented` says its crossed
   product is not finitely presented.
2. **`P = Z^2`. Gated, and one host at a time.**
   - For abelian `P`, a minimal action in which some `g ≠ e` has a fixed point
     has `g` acting trivially. Then `g` is a non-scalar central element, so a
     host with centre `F_2` needs a free action.
   - Finite presentation forces an SFT (`fp-subshift-crossed-products-are-sfts`,
     unreviewed) and is equivalent to quantum rigidity over `F_2`
     (`sft-crossed-product-fp-iff-quantum-rigid`, unreviewed).
   - Existence of even one such free minimal SFT is the `F_2` form of the open
     `free-minimal-z2-sft-is-quantum-rigid`.
   - Every such host has a faithful Følner rank model
     (`free-minimal-crossed-products-are-simple-with-rank-models`, unreviewed).
     So the `Z^d` case would make every finitely generated group with solvable
     word problem `F_2`-linear sofic, tying it to an open approximation problem.
3. **Amenable `P`. Gated by linear soficity.** Every minimal action of a
   countable amenable group has a faithful Følner rank model over every field
   (`amenable-minimal-crossed-products-have-faithful-rank-models`, ESTABLISHED,
   unreviewed; freeness is not used). A simple host is minimal, so the amenable
   case would make every finitely generated group with solvable word problem
   `F_2`-linear sofic.
4. **`P = F_d`, any `X`. The whole family dies (2026-09-17).**
   - `boundary-crossed-product-is-a-leavitt-path-algebra` gives one finitely
     presented simple host with centre `F_2` over the minimal, topologically
     free SFT `∂F_d`. So nothing dynamical excludes free groups.
   - `free-group-cantor-crossed-products-are-not-universal-hosts` (ESTABLISHED,
     unreviewed) shows some two-generated decidable `H` has `F_2[H]` in no
     finitely presented `LC(X, F_2) ⋊ F_d`, for any `d >= 0` and any `X`,
     simple or not. Finite presentation forces an SFT over any group
     (`fp-crossed-products-force-sft-over-any-group`). Tree SFTs have the local
     extension property, so their ball languages are decidable by local checks.
     So every unit subgroup has doubly exponential word problem
     (`free-group-sft-host-units-have-doubly-exponential-wp`), and
     `complexity-bounded-host-classes-are-not-universal` finishes.
   - Invariant: the local extension property of tree SFTs. Failing step: the
     unital embedding of the hard input `H`. This also covers `P = Z` and
     `P = 1`, independently of Attempt 1.
5. **Hosts from the Boone–Higman embeddings of hyperbolic groups
   (Belk–Bleak–Matucci–Zaremsky, arXiv:2309.06224). Out of scope.** Their natural
   algebras are Steinberg algebras of ample groupoids that are not
   transformation groupoids of torsion-free groups. The Farrell–Jones argument
   does not apply to them.
6. **Sharpened necessary shape (2026-09-17).** Any witnessing family uses:
   - `P` finitely presented
     (`fp-crossed-products-force-finitely-presented-acting-group`, unreviewed);
   - `X` an SFT;
   - `P` not free.

   Open prerequisite, which can fail on its own: the hosts must have no common
   recursive word-problem bound on unit subgroups. The table algorithm of the
   free case works over any `P` with solvable word problem once the SFTs have a
   language algorithm, so a uniform bound on both kills the family as in
   Attempt 4. Therefore a viable `P` must carry minimal,
   topologically free SFTs with finitely presented crossed products whose ball
   languages have no uniform recursive time bound (artifact
   `fp-crossed-product-shape-free-group-kill-2026-09-17`, Section 7, sketch).
7. **Homoclinic kill over every acting group (c-pbh0, 2026-09-17).** The hole
   stays OPEN, but the host must be shell-determined.
   - `fp-minimal-crossed-products-have-no-homoclinic-pairs` (ESTABLISHED,
     unreviewed): over any finitely generated `P`, if `LC(X,k) ⋊ P` is finitely
     presented and `X` is infinite minimal, then `X` has no homoclinic pair, and
     every pattern on `F` is determined by its `r`-shell. Engine: a wall lemma
     over any group, using the module `k[P] ⊗ k^2` in two bases. The `Z^2`
     family of `sft-wall-rigidity-iff-idempotent-commutator-ideal` needs no
     property of `Z^2`. Recurrence splices one homoclinic pair into a wall.
   - `fp-minimal-crossed-products-have-shell-bounded-complexity` (ESTABLISHED,
     unreviewed) gives:
     - `|L_F| <= |A|^(|N_r(F) \ F|)`;
     - zero entropy over every amenable `P`;
     - virtually cyclic `P` is impossible, independently of Attempts 1 and 4;
     - `log|L_(B_N)| <= C N^(d-1)` over `Z^d`.
   - Invariant: the homoclinic relation of `X` (equivalently, unique shell
     filling). Failing step: finite presentation, since the two-basis module
     satisfies every relator.
   - Classes killed, over every `P`: strongly irreducible minimal SFTs, and
     every construction that stores bits in locally re-colourable cells, such
     as a rigid base with free decorations or independent local flips.
     Consistent with `∂F_d` and with products over infinite factors, which have
     no homoclinic pairs.
   - Over `Z^2`, with the growth-counting lower bound `e^(cN)` for hosting
     `F_2` (Attempt 8 on another branch, commit 37e605aea), ball complexity is
     pinned to `e^(Θ(N))`. The hard language must come from which boundary rows
     occur, with the bulk forced.
   - Surviving shape: shell-determined minimal SFTs with hard language, i.e.
     deterministic space-time simulations. Artifact
     `research/artifacts/fp-minimal-crossed-products-homoclinic-kill-2026-09-17.md`.
   - **Overlap.** Attempt 9 below, landed the same day on another lane, is an
     independent derivation of the same wall obstruction, in the more general
     form `fp-crossed-products-force-connected-differences`. Its parts 2 and 3
     subsume both claims here; the two arrivals are a mutual check, not two
     results.
8. **Growth counting: polynomial-growth `P` with slow spaces die at input `F_2`
   (2026-09-17).** This attempt uses growth, not word-problem complexity.
   - `crossed-product-growth-bounded-by-ball-patterns` (ESTABLISHED,
     unreviewed): the degree-`n` span of a finite subset of `LC(X, k) ⋊ P` has dimension at most
     `|B_P(mn)| · |L_(B_P(mn+r))(X)|`. The group elements of a hosted `k[G]` are linearly
     independent, so `|B_G(n)|` obeys the same bound.
   - `poly-growth-cantor-hosts-need-exponential-complexity` (ESTABLISHED, unreviewed):
     - If `P` has polynomial growth and `log |L_(B_P(N))(X)| = o(N)` along a subsequence, only
       subexponential-growth groups are hosted, so `F_2` is not.
     - If the pattern count is polynomial, only virtually nilpotent groups are hosted.
     - In particular Labbé's host `LC(Ω_U, k) ⋊ Z^2`, the one explicit candidate on the
       quantum-rigidity lane, hosts no non-virtually-nilpotent group algebra, whatever
       `labbe-wang-shift-crossed-product-is-finitely-presented` turns out to be.
     - Invariant: the ball pattern count. Failing step: the embedding of `k[F_2]`, with no use of
       finite presentation.
   - Over `Z^2`, positive entropy already kills finite presentation
     (`positive-entropy-sft-crossed-products-are-not-fp`). A pure `Z^2` witness must lie in the band
     `e^(cN) <= |L_(B(N))| <= e^(o(N^2))`, for some `c > 0` along every sequence of radii. The natural
     candidates are minimal SFTs simulating a positive-entropy effective row content (heuristic). Substitutive
     or cut-and-project shifts do not qualify. This is a new prerequisite that
     can fail on its own: a quantum rigid free minimal `Z^2`-SFT with linear-exponential complexity.
   - **Product lanes cannot borrow finite presentation.**
     `tensor-product-algebra-fp-iff-factors-fp` (ESTABLISHED, unreviewed) gives:
     - `LC(Ω × Y) ⋊ (P × Q)` is finitely presented iff both factors are.
     - So `B_Ω ⊗ L_∂` over `Z^2 × F_d` still needs a quantum rigid `Ω`. The boundary factor supplies
       only growth, which does repair the obstruction above, e.g. for `Ω = Ω_U`.
     - A Labbé-times-boundary host remains subject to the uniform language-bound kill of Attempt 6 if
       that sketch is made rigorous, because `Ω_U` has a decidable substitutive language.
   - **Separation from the units-only version.** Route step 1 of
     `boone-higman-via-central-simple-leavitt-tensor-host` uses only `G ≤ B^x`, and there group
     elements need not be linearly independent.
     - Unit groups of polynomial-growth algebras can contain `F_2` (`GL_2(F_2[t])`, recalled).
     - So the growth kill does not reach the units-only form. There an input must use non-permutational
       units, or full-group elements with fat fixed-point sets: the growth-bound node, part 3, shows
       meagre fixed sets make `k[G]` embed and so inherit the bound. That part of the node also
       calibrates the hypothesis: disjoint supports give `(1 - u_g)(1 - u_h) = 0`.
     - For permutational units over subexponential-growth `P`, Juschenko–de la Salle (as quoted in
       `elek-monod-near-hit-has-torsion-no-kazhdan-subgroup-proof`) also excludes infinite Kazhdan
       subgroups. So simple Kazhdan inputs (`boone-higman-iff-simple-kazhdan-decidable-inputs`) must use
       non-permutational units there.
   - **Dead side idea: renormalization rigidity over an ascending HNN acting group
     `Z[1/2]^2 ⋊ Z`, with a determinism rule `x(g) = F(x|_(gtW))`.** It dies at the reduction step.
     Conjugating a difference element by powers of `t` shrinks it into a finite set only when it
     commutes with a power of `t`. Other differences drift to different cosets with growing word length.
     So one deterministic direction reduces only differences in `⋃_j C(t^j)`, and determinism from
     infinity makes the language easy, which Attempt 6 forbids.
9. **Boundary determinism over every acting group (2026-09-17, lane swarm-0917-w5-pull2-boone-1).**
   *Class kill, and new necessary shape.* Invariant: coarse connectivity of difference sets.
   - `fp-crossed-products-force-connected-differences` (ESTABLISHED, unreviewed). A presentation
     with relators of length `<= n` forces every `Δ(x, y)` to be `2n`-connected, over any finitely
     generated `P` and any field. The proof uses a `k^2`-valued sitewise representation that
     switches basis on one half of a split difference set. This is the `Z^2` wall certificate made
     group-free.
   - For a simple host (minimal, infinite) it gives two consequences.
     - No finite asymptotic pairs.
     - `F`-patterns are determined by the layer `∂F` of width `2r`, so `|L_F(X)| <= |A|^|∂F|`.
   - **Killed classes.** Each dies at the step "glue two far copies of a local modification into one
     point, then split the difference set":
     - hosts with a locally flippable tile or free bits, over every `P`;
     - positive-entropy minimal hosts over every amenable `P`, extending the `Z^2` entropy kill;
     - every virtually cyclic `P`, independently of Attempts 1 and 4.
   - **`Z^2` band collapses.** The band of Attempt 8 becomes `e^(cN) <= |L_(B_N)| <= e^(O(N))`. A
     pure `Z^2` witness must have boundary-deterministic, exactly linear-exponential complexity.
   - **Multi-ended `P`** (`fp-minimal-crossed-products-map-onto-ends`, ESTABLISHED, unreviewed).
     - Each ball pattern is undetermined toward exactly one end.
     - This gives a continuous equivariant map `X -> Ends(P)`, onto when the end action is minimal.
     - Over `F_d` it gives linear pattern counts, which is a structural second proof of the shape of
       Attempt 4's hosts.
     - For torsion-free `P = Q_1 * Q_2`, every host extends the end action.
   - **Where it does not reach.**
     - One-ended non-amenable `P`, where `|∂B_N| ≍ |B_N|` and the bound is empty.
     - Free products whose one-ended factors carry the free end inside a sheet.
     - Hard languages are not excluded: boundary determinism is a rigidity condition, not a time
       bound. So the Attempt 6 prerequisite now reads: minimal, topologically free SFTs with
       finitely presented crossed products, *without finite asymptotic pairs*, and with no uniform
       recursive bound on their ball languages.
10. **Boundary products (c-cantor, 2026-09-17). Reframing; the rank-model gate
   is lifted, the target stays OPEN.** This item follows the landed Attempt 6.
   - **Closure.** `cantor-crossed-hosts-are-closed-under-boundary-products`
     (ESTABLISHED, unreviewed) says that valid hosts are closed under
     `(P, X) ↦ (P × F_d, X × ∂F_d)`, with algebra `B ⊗ L_∂`. Valid means:
     `P` torsion-free with FJCw; `B` finitely presented, simple, centre `k`.
     - The new host contains `B` unitally.
     - It has no unital rank model.
   - **The linear-soficity gate.** The gate of Attempts 2 and 3 is a property
     of amenable hosts only. It does not follow from the target.
   - **Hard SFTs.** `minimal-z2-sfts-have-no-uniform-language-time-bound`
     (ESTABLISHED, unreviewed, Durand–Romashchenko import plus a Sturmian
     diagonalization) answers the language part of Attempt 6 for `Z^2`, and so
     for `Z^2 × F_d`. The SFTs it produces are not known to be free or quantum
     rigid.
   - **Decomposition.** Route
     `cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts` reduces the
     target to the OPEN
     `decidable-algebras-embed-in-z2-sft-boundary-product-hosts`.
     Its prerequisites can fail separately:
     - (Q) a quantum rigid free minimal `Z^2`-SFT over `F_2`;
     - (H) unbounded language complexity among them;
     - (E) the embedding `F_2[G] -> B_Ω ⊗ L_∂`.
   - **Group-level weakening.** The OPEN
     `decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units`, with
     route `boone-higman-via-units-of-cantor-crossed-leavitt-tensors`, asks only
     for `G -> (B ⊗ L)^x`, and already gives Boone–Higman.
   - **Where it stops.** No free, minimal, quantum rigid, hard `Z^2`-SFT was
     produced, and no embedding (E) was attempted for a non-linear-sofic group.
     The absence of finite asymptotic pairs required by Attempt 9 is also not
     known for these SFTs.
     Artifact `cantor-crossed-host-boundary-products-2026-09-17`.

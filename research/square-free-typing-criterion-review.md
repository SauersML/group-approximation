---
rg: 2
id: square-free-typing-criterion-review
kind: claim
title: Referee review of 968ada84c1 (typing criterion for quasiconvex subgroups of hyperbolic RACGs, and the DFWZ bridge node) — PASS; both directions of the criterion check (developing map as a local isometry into the Davis complex; restriction of the Davis typing to a convex core), items 2–5 check, and both DFWZ quotations (§1.2 and §2.2.2 of arXiv:2309.03695v1) are verbatim at source; minor wording repairs only
distinct_from:
  quasiconvex-in-hyperbolic-racgs-iff-square-free-typing: that is the lane claim under review; this checks it.
  cubulated-hyperbolic-groups-are-quasiconvex-in-hyperbolic-racgs: that is the open bridge node; this checks its provenance.
---

**ESTABLISHED (referee bh-ref-e, 2026-09-19; review of the lane nodes by bh-q11-bridge, landed in 968ada84c1).** No
priority claimed.
- **Read at source:** the claim, its route and the open node on origin/main; Douba–Fléchelles–Weisman–Zhu,
  arXiv:2309.03695v1, arXiv HTML, §1.2 and §2.2.2.
- **Not reviewed:** `convex-cores-inherit-greedy-coding-na`, which is also in the commit.
- **No code was run.**

## 1. The criterion

**(ii) ⇒ (i), via the developing map: correct.**
- **`D` is well defined.** Edge paths with common ends differ by backtracks and square moves, since `Y` is simply
  connected and its 2-cells are squares.
  - The opposite sides of a square are dual to one hyperplane, so they have one type. The boundary word is `stst`.
  - The two corner edges span a square, so by (T2) their types are adjacent, and `st = ts` in `W(Δ)`.
- **`D` is a local isometry.**
  - (T1) makes the link map injective.
  - (T2), together with flagness of `lk_Y` (Y is CAT(0)) and of `L(Δ)`, makes it an isomorphism onto a full
    subcomplex.
  - Haglund–Wise's lemma then makes `D` injective with convex image. `Y` is finite-dimensional because it is
    cocompact.
- **`ρ` is an injective homomorphism.**
  - `G`-invariance of `τ` gives `D(gy) = ρ(g) D(y)`.
  - `ρ(g) = 1` forces `g y_0 = y_0`, so `g = 1`, since `G` acts freely on vertices.
- **Quasiconvexity.**
  - `ρ(G)` acts cocompactly on the convex subcomplex `D(Y)`, whose 1-skeleton is combinatorially isometrically
    embedded. So it is quasiconvex in the word metric on `W(Δ)`.
  - `W(Δ)` is hyperbolic by Moussong's criterion (recalled).

**(i) ⇒ (ii), by restricting to a convex core: correct.**
- Every defining graph of a hyperbolic RACG is square-free, by Moussong.
- A quasiconvex `G` acts cocompactly on a convex subcomplex `Y ⊆ Σ(Δ)` (cores: Haglund; Sageev–Wise; recalled).
  - The action is proper, and free on vertices.
  - Hyperplanes of `Y` are the traces of ambient hyperplanes, which are connected by convexity.
- **(T1) and (T2).** They hold because a convex subcomplex contains every square spanned by two of its edges at a
  common vertex, so its links are full in `L(Δ)`.

## 2. Items 2–5: correct

- **Item 2.** Full subgraphs of a square-free `Δ` are square-free.
- **Item 3.**
  - Crossing hyperplanes have meeting carriers, and the diagonal carrier pairs meet by hypothesis. Helly then gives a
    common vertex `u`.
  - `u` is an endpoint of an edge dual to each `H_i`. Two edges at `u` span a square exactly when their hyperplanes
    cross, since CAT(0) cube complexes have no inter-osculation. So `lk(u)` contains an induced 4-cycle.
  - The converse is immediate.
- **Item 4.**
  - **(M1).** (T2) never tests a never-co-occurring pair.
  - **(M2).** The only adjacencies that change pair `a` with a type `c ~ b` that co-occurs with `a` and is non-adjacent
    to it. The osculation hypothesis excludes these, and `a ≁ b` keeps the merged graph loop-free.
  - **Wording.** "Only (M1) and (M2)" is a statement about modifications of `Δ` along the same typing. Say that.
- **Item 5.**
  - C-specialness gives (T1), by no self-crossing or self-osculation, and (T2), by no inter-osculation.
  - An invariant typing is a function on `Hyp(X)`, so it factors as `φ ∘ τ_HW`, with `φ` a full embedding on
    links.
  - For Davis–Januszkiewicz doubling, `A(Γ) ⊇ Z²` rules out hyperbolicity.
  - **Wording.** (B\*) is a finite problem *for each fixed cover* `X′`. Over all finite covers it is not a finite
    search.

## 3. DFWZ at source

- **§1.2 ("Actions of reflection groups on projective space"), verbatim, matching the node.** "However, the
  Haglund–Wise construction typically yields a quasiconvex embedding of a compact special hyperbolic group Γ into a
  *non-hyperbolic* right-angled Coxeter group C, and when this occurs we cannot invoke the results in [13] or [14].
  Further, we know of no procedure that replaces C with a hyperbolic Coxeter group (although we do not know of any
  reason such a procedure cannot exist)."
- **§2.2.2 ("Quasiconvex subgroups"), verbatim.** "even in the case that the action of Γ on X̃ is the action of a
  hyperbolic right-angled Coxeter group on its Davis complex, the right-angled Coxeter group C_X that one obtains via
  the process above may not be hyperbolic." This matches the claim's Examples section.
- **Wording (repair).** DFWZ state a missing procedure, not a numbered question. So "asked in print" should read
  "raised in print (DFWZ §1.2: no known procedure, no known obstruction)".
- **Equivalence of framings.** Their framing is for compact special groups. By Agol's theorem, every cocompactly
  cubulated hyperbolic group is virtually compact special, so the node's "virtually" framing is equivalent.
- **Literature check.** I did not search beyond DFWZ for later answers.

## Verdict

**PASS.**
- The typing criterion is correct in both directions.
- Items 2–5 hold.
- The provenance is verbatim at source.
- Repairs are wording only:
  - "raised in print" for "asked in print";
  - (B\*) is finite per cover;
  - the scope of "only (M1)/(M2)".
- The recalled inputs are standard: Moussong; Haglund–Wise local isometries; cores; Helly.

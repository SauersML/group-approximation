---
rg: 2
id: topologically-free-fg-subgroups-of-v-are-virtually-free
kind: claim
title: A finitely generated subgroup of Thompson's V with a free orbit, or acting topologically freely, is virtually free
distinct_from:
  raag-subgroups-of-v-contain-no-one-ended-hyperbolic-group: that excludes one-ended hyperbolic groups only from the RAAG subgroups of V (via Z^2 * Z); this constrains every finitely generated subgroup of V through orbit Schreier graphs.
  cyclic-centralizer-subgroups-of-nv-have-meeting-supports: that says supports of nontrivial elements meet; this says, for any non-virtually-free subgroup, that almost every point is interior-fixed by some nontrivial element.
  support-constraints-on-v-subgroups-cannot-see-one-endedness: that shows support-meeting conditions cannot see one-endedness; this uses a V-specific geometric invariant (orbit Schreier graphs are quasi-trees) that does see it at free orbits.
artifacts:
  - research/artifacts/gq-bh-scout-bbmz-ranked.md
---

**ESTABLISHED** by `topologically-free-fg-subgroups-of-v-virtually-free-proof` (lane proof). It was refereed PASS by
bh-ref-t0 at 6a216bf0dc: HSZ Theorem A is checked verbatim at source, and (F1), (F2), items 1, 2 and 3(a)–(c) are
correct.
- It is a short corollary of Hyde–Skipper–Zaremsky, arXiv:2605.20564v2 (29 May 2026), Theorem A, and all credit
  for the key input is theirs.
- Item 1 is HSZ's own argument for their Corollary 1.7, which uses that a free orbit would make the Cayley graph a
  quasi-tree, in general form. No priority is claimed.

Let `G ≤ V` be finitely generated, acting on the Cantor space `C = {0,1}^ℕ` by prefix replacements.
For `g ∈ G` write `Fix(g)` for its fixed set.

1. **Free orbits.** If some point of `C` has trivial stabilizer in `G`, then `G` is virtually free.
2. **Topologically free actions.** If no nontrivial element of `G` fixes a nonempty open subset of `C`
   pointwise, then `G` is virtually free.
3. **Structure of a non-virtually-free `G`.** Suppose `G` is not virtually free. Let
   `O = ⋃_{g ≠ 1} int Fix(g)` (open, `G`-invariant) and `K = C ∖ O` (closed, `G`-invariant). Then:
   - (a) `K` is countable. So all but countably many points of `C` are interior fixed points of some
     nontrivial element.
   - (b) Every `x ∈ K` is eventually periodic, and `Stab_G(x)` is infinite cyclic, `= ⟨c_x⟩`. It embeds
     in the germ group of `V` at `x`, which is infinite cyclic.
   - (c) For every `x ∈ K`, the Schreier graph of `G` on `G/⟨c_x⟩` is quasi-isometric to a tree.

**Consequence for BBMZ survey Question 4.7** (`closed-hyperbolic-surface-groups-embed-in-thompson-v`).
Any embedding of a one-ended hyperbolic group, in particular a closed surface group, into `V` has all
three features in part 3. So it is never topologically free, and it has no free orbit. This is the first
constraint on the question that uses a property of `V` that the rational group `R` lacks. BBM embed every
hyperbolic group in `R`, with free orbits on the horofunction boundary; the node's own remark says a
negative answer must see exactly this difference.

**Update, 09-19, later.** Lemma L below is now proved (`one-ended-hyperbolic-subgroups-of-v-are-locally-fixed`, lane
proof). So `K = ∅` for every one-ended hyperbolic subgroup of `V`, and torsion-free ones contain no element with
north–south dynamics. What was listed as remaining, as first written:
- **Lemma L:** for a one-ended hyperbolic `Γ` and `c ≠ 1`, the Schreier graph `Γ/⟨c⟩` is not quasi-isometric
  to a tree. With this, `K = ∅`.
- **The case `K = ∅`:** then, by compactness, `C` is a finite union of clopen sets each fixed pointwise by a
  nontrivial element, while all moved sets pairwise meet.

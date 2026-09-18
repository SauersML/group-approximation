---
rg: 2
id: fg-amenable-subgroups-of-thompson-t-have-finite-orbits
kind: claim
title: A finitely generated amenable group of circle homeomorphisms whose generators have periodic points has a finite orbit; so a subgroup of Thompson's T with no finite orbit is nonamenable
distinct_from:
  amenable-infinite-simple-circle-groups-fix-a-point: that uses the invariant measure to force a global fixed point for simple groups; this forces a finite orbit for every finitely generated amenable group whose generators have rational rotation number, with no simplicity assumption.
  thompson-t-dyadic-rotation-cosets-are-not-amenably-transitive: that node's structure lemma gives a normal subgroup fixing a point with finite or abelian quotient; this sharpens the quotient to finite and produces an actual finite orbit, which is what makes the twist census decidable.
---

**ESTABLISHED** through `fg-amenable-subgroups-of-thompson-t-have-finite-orbits-proof`.

**Statement.** Let `H = ⟨h_1, …, h_n⟩ ≤ Homeo+(S¹)` be amenable, and suppose each generator `h_i` has a
periodic point. Then:

1. `H` has a finite orbit `O ⊂ S¹`;
2. the pointwise stabilizer `H_0` of `O` has finite index in `H`, and `H` is amenable iff `H_0` is;
3. in particular, if some finitely generated `H ≤ Homeo+(S¹)` whose generators have periodic points has no
   finite orbit, then `H` is nonamenable.

For `H ≤ T` the hypothesis on generators always holds, since every element of `T` has rational rotation
number (Ghys–Sergiescu 1987). The proof does not use that theorem: in the census below each generator's
periodic point is found explicitly.

**Use.** A rotation twist `⟨f_iρ_{θ_i}⟩ ≤ T` of a finite `S ⊆ F` with no finite orbit on `S¹` is nonamenable
without any hypothesis on `F`. This is decidable up to the choice of test words: a finite orbit lies in
`Per(w)` for every `w ∈ H`, so an empty maximal invariant subset of `⋂_w Per(w)` certifies that there is no
finite orbit (`experiments/rotation-twist-finite-orbits-2026-09-17/classify_twists.py`). The twists that
survive have a finite orbit `O`. Cutting `S¹` at a point of `O` puts `H_0` inside the PL homeomorphisms of an
interval, where Brin's Theorem 1 (`brin-plo-i-one-sided-approach-gives-a-copy-of-f`) and virtual abelianity
can be tested exactly.

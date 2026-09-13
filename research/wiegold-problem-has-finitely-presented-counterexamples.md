---
rg: 2
id: wiegold-problem-has-finitely-presented-counterexamples
kind: claim
title: Some finitely presented perfect groups are not the normal closure of a single element
distinct_from:
  left-orderable-free-products-have-normal-rank-above-one: that is the Chen--Lodha normal-rank theorem for free products of two nontrivial left-orderable groups; this is the existence statement answering Wiegold's question, which follows from it once finitely presented perfect left-orderable factors are supplied.
  l2-normal-rank-bound-fails-for-torsion-free-groups: that refutes the torsion-free Osin--Thom bound with infinitely generated locally free groups of normal rank one; this exhibits finitely presented perfect groups of normal rank greater than one.
---

**ESTABLISHED** by `wiegold-problem-chen-lodha-citation` (literature import, not
reproved).

**Statement.** There exist finitely presented perfect groups `G` that no single
element normally generates. In other words, the normal rank (weight) of `G` is at
least 2.

This answers Wiegold's 1976 question negatively (Kourovka Notebook 5.52): it is
**not** true that every finitely generated perfect group is the normal closure
of one element.
- **Finite case.** Finite perfect groups do have normal rank 1, and so does the
  free product of any two of them. See
  `finite-perfect-free-pairs-have-normal-rank-one`.
- **Kourovka.** The 21st issue (2026) lists the problem as answered, citing
  Chen–Lodha.

**Examples, as listed in the source** (not re-derived here):
- free products `A * B` of finitely presented perfect left-orderable groups;
- the factors can be commutator subgroups of the braid groups `B_n` (`n >= 5`), a
  central extension of Thompson's group `T`, or Higman's group;
- infinitely many hyperbolic integer homology 3-spheres (Chen–Lodha Theorem C),
  which gives linear examples.

**Do not target this as an open problem.** The open questions next to it are:
- `gordon-free-products-of-three-groups-have-normal-rank-above-one`: three or
  more factors, with torsion allowed;
- `torsion-free-free-products-have-normal-rank-above-one`: two torsion-free
  factors;
- `left-orderable-free-products-of-n-factors-have-normal-rank-n`: normal rank at
  least `n` for `n` left-orderable factors.

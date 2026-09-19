---
rg: 2
id: trace-extending-bcs-to-lcs-maps-are-already-terminal
kind: claim
title: A trace-extending BCS-to-LCS map is already the terminal theorem
artifacts:
  - research/two-arrow-trace-transfer-to-lcs-proof.md
distinct_from:
  nested-conjugacy-stops-at-tv-dictator-projectors: that identifies the local non-group relation which Fanizza et al. leave in BCS form; this proves abstractly that upgrading their trace-extending codomain to LCS would immediately solve the nonhyperlinear-group problem.
  locally-affine-support-bcs-is-exactly-the-lcs-boundary: that gives a support criterion inside one chosen trace; this needs no support description and isolates the two functorial properties sufficient for the terminal transfer.
  perfect-completeness-constant-soundness-lcs-compiler: that asks for an effective machine-indexed quantitative family; this is a one-instance exact transfer theorem.
---

Let \(\mathcal A_B\) be a finite BCS algebra which has a tracial state but
has no unital \(*\)-homomorphism to \(\mathcal R^{\mathcal U}\), as supplied
by the MIP\(^*=\)RE separation.  Let \(\mathcal A_L\) be the algebra of a
finite binary LCS.

Suppose there is a unital \(*\)-homomorphism

$$
\iota:\mathcal A_B\longrightarrow\mathcal A_L          \tag{1}
$$

and at least one tracial state \(\tau\) of \(\mathcal A_B\) extends across
\(\iota\): there is a tracial state \(\widetilde\tau\) of
\(\mathcal A_L\) with

$$
\tau=\widetilde\tau\circ\iota.                         \tag{2}
$$

Then \(\mathcal A_L\) is tracially satisfiable but not
\(\mathcal R^{\mathcal U}\)-satisfiable.  Indeed, (2) supplies its trace,
while any map \(\mathcal A_L\to\mathcal R^{\mathcal U}\) would compose
with (1) to contradict the source hypothesis.

By Paddock--Slofstra
[Proposition 5.8](https://arxiv.org/html/2310.07901v2#S5), this is
equivalent to a finitely presented nonhyperlinear solution group.  Neither
injectivity of \(\iota\) nor extension of every source trace is required.

A useful sufficient variant is the two-arrow condition: unital maps

$$
\mathcal A_B\longrightarrow\mathcal A_L
\longrightarrow\mathcal A_B                            \tag{3}
$$

in arbitrary composition order already suffice, because the second arrow
pulls any source trace back to the LCS.

Consequently Fanizza et al. Theorem 5.5 would be a complete solution if
its trace-extending BCS codomain could always be chosen linear.  Its
retained ordinary BCS relation is not a cosmetic final step; it is exactly
the terminal open theorem.  Likewise, the two-way algebra maps in
constraint-language definability reductions cannot be specialized from a
nonaffine MIP source to LIN without already constructing a nonhyperlinear
group.

This claim proves a transfer criterion, not the existence of the required
map.

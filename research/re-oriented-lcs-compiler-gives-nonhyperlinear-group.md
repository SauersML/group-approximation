---
rg: 2
id: re-oriented-lcs-compiler-gives-nonhyperlinear-group
kind: claim
title: A machine-indexed LCS family with perfect commuting completeness and strict matrix soundness yields an explicit nonhyperlinear group
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  perfect-lcs-gap-implies-nonhyperlinear: that consumes one game already known to have perfect commuting value and quantum value below one; this effectively selects such a game from a machine-indexed family by a proof-search recursion-theorem fixed point.
  kleene-self-destroying-microstate-lemma: that is the coRE orientation (nonhalting gives the nontrivial word, halting gives matrix soundness) and searches finite matrices; this is the RE orientation (halting gives a nontrivial solution-group mark, nonhalting gives strict matrix soundness), and its fixed point searches only for a formal proof that J equals one.
---

Let `M -> L_M` be a computable map from Turing machines to finite binary
linear constraint systems with solution groups `Gamma_M` and central
involutions `J_M`, such that

```text
M halts         =>  J_M != 1 in Gamma_M
                    (equivalently omega^co(L_M)=1),                    (RE1)
M does not halt =>  omega_q(L_M) < 1.                                 (RE2)
```

Then one can effectively construct a machine `M_*` such that `M_*` does not
halt, `J_(M_*) != 1` in `Gamma_(M_*)`, and `Gamma_(M_*)` is nonhyperlinear.
In particular, once the compiler is given effectively, its output contains
an explicit finite presentation of a nonhyperlinear group.

*Proof.*  Given a machine index `e`, write `Gamma_e=Gamma_(M_e)` and
`J_e=J_(M_e)`.  Compute the finite presentation of `Gamma_e` and enumerate
formal consequences of its relators.  Let `P_e` halt exactly when this
enumeration finds a proof that `J_e=1`.
The effective recursion theorem supplies an index `e_*` with

```text
M_(e_*) = P_(e_*).                                      (RE3)
```

If `M_(e_*)` halted, its stopping certificate would prove
`J_(e_*)=1`, contradicting `(RE1)`.  Hence
`M_(e_*)` does not halt.  Conversely, if `J_(e_*)=1`, finite-presentation
proof enumeration would eventually find a derivation and `(RE3)` would halt.
Therefore `J_(e_*)!=1`.

By the Cleve--Liu--Slofstra criterion, `L_(M_(e_*))` has perfect commuting
value.  Its machine is nonhalting, so `(RE2)` puts its quantum value strictly
below one; `perfect-lcs-gap-implies-nonhyperlinear` now proves that the
explicit solution group `Gamma_(e_*)` is nonhyperlinear.

**What this says about Taller--Vidick.**  `taller-vidick-lcs-re-hardness`
supplies `(RE2)` with `delta = 1/72` and supplies `(RE1)` only in the
weakened form "some finite-dimensional strategy has value at least
`1 - epsilon`", which does not make `J` nontrivial in the solution group.  The
missing hypothesis is exactly perfect completeness
(`perfect-completeness-constant-soundness-lcs-compiler`).  The effective
fixed point above is used only to name a witness, not to search matrix
strategies or cross an unknown soundness threshold.  Compare the coRE
orientation of `hs-pcp-boone-compiler`, where the exact side is infinite
(nonhalting gives a nontrivial word) and the matrix side must be sound on
halting inputs: the two orientations ask for soundness on opposite sides
of the halting set.  The constant `1/72` gap delivered by the PCP machinery
is stronger than the strict instancewise inequality used here.

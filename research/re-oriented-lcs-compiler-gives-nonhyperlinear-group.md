---
rg: 2
id: re-oriented-lcs-compiler-gives-nonhyperlinear-group
kind: claim
title: A machine-indexed LCS family with perfect finite-dimensional completeness and constant soundness yields a nonhyperlinear group
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  perfect-lcs-gap-implies-nonhyperlinear: that consumes one game already known to have perfect commuting value and quantum value below one; this produces such a game from a machine-indexed family by undecidability of halting, with no recursion theorem and no matrix search.
  kleene-self-destroying-microstate-lemma: that is the coRE orientation (nonhalting gives the nontrivial word, halting gives matrix soundness) and needs the self-referential search; this is the RE orientation (halting gives an exact finite-dimensional J equals minus one representation, nonhalting gives constant soundness) and needs only that the word problem is recursively enumerable.
---

Let `M -> L_M` be a computable map from Turing machines to finite binary
linear constraint systems with solution groups `Gamma_M` and central
involutions `J_M`, and let `delta > 0` be a constant such that

```text
M halts         =>  some finite-dimensional representation of Gamma_M
                    sends J_M to -I,                                  (RE1)
M does not halt =>  omega_q(L_M) <= 1 - delta.                        (RE2)
```

Then some `Gamma_M` is not hyperlinear.  Explicitly, there is a nonhalting
`M` with `J_M != 1` in `Gamma_M`, and that `Gamma_M` is nonhyperlinear.

*Proof.*  Suppose every nonhalting `M` had `J_M = 1` in `Gamma_M`.  By
`(RE1)`, halting `M` have `J_M != 1`.  So `M` halts iff `J_M != 1` in
`Gamma_M`.  The right-hand side is co-recursively-enumerable (enumerate
consequences of the finite presentation and wait for `J_M`), so the
halting set would be co-r.e., hence decidable.  Therefore some nonhalting
`M` has `J_M != 1`; by the Cleve--Liu--Slofstra criterion its game has
perfect commuting value, while `(RE2)` bounds its quantum value, and
`perfect-lcs-gap-implies-nonhyperlinear` applies.

**What this says about Taller--Vidick.**  `taller-vidick-lcs-re-hardness`
supplies `(RE2)` with `delta = 1/72` and supplies `(RE1)` only in the
weakened form "some finite-dimensional strategy has value at least
`1 - epsilon`", which does not give a representation with `J = -I`.  The
missing hypothesis is exactly perfect completeness
(`perfect-completeness-constant-soundness-lcs-compiler`), and no
self-reference is needed once it is available.  Compare the coRE
orientation of `hs-pcp-boone-compiler`, where the exact side is infinite
(nonhalting gives a nontrivial word) and the matrix side must be sound on
halting inputs: the two orientations ask for soundness on opposite sides
of the halting set, and `(RE2)` is the side that the PCP machinery already
delivers.

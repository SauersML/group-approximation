# Nonhyperlinear existence: exact certificate attempt

The requested existence proof was not obtained. The completed results are
an exact rational falsification procedure for a proposed HS word coefficient
and a two-dimensional lower bound for the Higman four-cycle. Neither
establishes the root `non-hyperlinear-group`.

## Completed work

`failed-hs-word-bounds-have-rational-witnesses` proves that a failed
finite word-energy inequality has a strict witness on exactly unitary
Q(i) matrices. A fair rational Cayley enumeration therefore semidecides
failure of a specified coefficient. The statement refines the existing
radical certificate criterion and uses the same elementary Cayley method
already present in the HS-Dehn word-problem route.

`experiments/hs_word_certificate.py` implements that enumeration and
independent exact witness verification. It checks dimensions and exact
unitarity, uses signed-index free words, and computes normalized squared
entry distances. Stored energy fields are ignored during verification.
No-witness searches are explicitly inconclusive. The first source
milestone was published to main as
`c8327330c41dc0f86829431c76d2789d90370276`.

For Higman's relators `g_i g_(i+1) g_i^(-1) g_(i+1)^(-2)`, the proposed
bound `e_(g_0)<=C sum_i e_(r_i)` was tested directly. The explicit matrices
in `higman-hs-word-coefficient-witness.json` prove

```
C >= 2748800041/1512087866 > 9/5
```

for any valid coefficient. The accompanying artifact derives the
fourth-relator trace by multiplication. This exact result requires no
numerical search. A preliminary floating-point search suggested looking
at two-dimensional tuples; its output is not a proof input, and the
committed witness uses a simpler closed-form rational family.

The subsequent exact search at C=2 tested 1,000 tuples, up to dimension
two and Cayley enumeration height two. Its recorded outcome is
inconclusive. This is a finite prefix, not an exhaustion of either U(2)^4
or all dimensions.

## Attempts that did not close the existence argument

The saturated group's operator-norm collapse estimate gives only
`D_2 <= C sqrt(d) d_2` after norm conversion. Because microstate
dimensions may grow, this supplies no fixed HS gap. No way to remove
that dimension factor was established.

The proposed HS energy polynomial has trace -2 at the canonical regular
representation of a group with the specified word nontrivial. Thus a
proof using only universal tracial sum-of-squares rules cannot establish
the desired positive matrix trace bound. The repository's earlier
regular-trace obstruction already identifies this failure; it was not
treated as a new theorem here.

The Higman calculation rules out small constants. It does not supply a
larger valid one. Identity-padding the witnesses makes all relator errors
small, but also makes the marked word collapse, so it does not give a
hyperlinear approximation either. The exact four-edge BS stability theorem
still leaves the simultaneous seam correction unresolved.

## Verification and remaining target

Seven exact verifier tests passed, including the committed Higman witness,
an independent trace formula, Pauli/inverse-word controls, malformed and
nonunitary inputs, strict equality, and normalization under padding.
Cairn's changed-source checks and preview were run; the new claims are
research-level established statements, and the main existence target
remains OPEN. No Lean source was changed or new Lean proof certified.

A successful continuation still needs a concrete nontrivial word in a
specified group together with a proof of one finite relator-energy
inequality valid in every matrix dimension, or a different complete
nonhyperlinearity argument. Neither a sequence of larger search bounds
nor a succession of rejected coefficients provides that proof.

The primary literature check included
[Taller--Vidick, version 2](https://arxiv.org/html/2507.22444v2), read on
2026-09-07. Its perfect-completeness implication remains conditional.
No claim is made that this source check exhausts the current literature.

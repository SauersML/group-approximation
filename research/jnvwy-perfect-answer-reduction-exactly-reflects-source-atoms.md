---
rg: 2
id: jnvwy-perfect-answer-reduction-exactly-reflects-source-atoms
kind: claim
title: Perfect JNVWY answer reduction is an exact classical low-degree mixture and reflects every source atom
distinct_from:
  jnvwy-positive-perfect-proof-atoms-have-boolean-input-cubes: that adds the source-specific Booleanity of the first two tables and makes this exact atomwise decoder odd-additive on the accepted perfect-atom domain.
  jnvwy-low-degree-pcp-reflects-affine-unsafety: that follows arbitrary honest completeness proofs forward to preserve an odd-xor obstruction; this decodes every atom of an arbitrary perfect strategy backward through the answer reduction.
  dfnqxy-halt-completeness-support-is-not-canonically-specified: that records the absence of a canonical chosen completeness support; this proves exact atomwise decoding without choosing a canonical proof or identifying supports belonging to different source outcomes.
  finite-affine-profile-or-removes-pcpp-section-gate: that replaces a later PCPP by profile-dispatched linear proofs; this concerns the unmodified JNVWY v3 low-individual-degree PCP and proves no affine or coherent-section property.
---

**ESTABLISHED.**  Fix the answer-reduced verifier of
Ji--Natarajan--Vidick--Wright--Yuen, arXiv:2001.04383v3, Sections
10.4--10.7 and Figure 14.  In a value-one tensor-product or
commuting-operator strategy, pass to the standard synchronous faithful
tracial quotient.  The same conclusion holds directly in any faithful
tracial measurement model of the typed verifier.

For each fixed source question or source oracle question-pair, the point
PVMs in each of the six classical low-individual-degree tests have a common
classical refinement.  Every nonzero atom of that refinement is the
evaluation table of an actual polynomial of individual degree at most `d`.
For `POINT_6`, this gives an exact global bundle

```text
Pi=(g_1,...,g_5,c_0,...,c_m')                           (EAR1)
```

of individual-degree-`d` polynomials.  The input and proof-encoding
cross-checks identify the first five bundled polynomials with polynomials
depending only on their prescribed `m`-variable blocks.  Thus `(EAR1)` is
a low-degree PCP proof in the literal sense of JNVWY Definition 10.23, not
merely an object within the nonzero error supplied by Theorem 7.8.

Perfect acceptance of the game check forces every nonzero bundle atom to
satisfy

```text
M_AR(z,eval_z(Pi))=1  for every z in F_q^(m').          (EAR2)
```

The soundness clause of JNVWY Theorem 10.25 therefore applies separately
to every atom and says that

```text
(Delta(g_1),Delta(g_2))                                 (EAR3)
```

is a pair of padded source answers accepted by the original decider.
Coarse-graining the polynomial-table PVMs by `(EAR3)`, and using the input
consistency checks, gives an exact value-one strategy for the oracularized
source verifier and hence for the source verifier.  Consequently

```text
V_AR has a perfect tensor/commuting/faithful-tracial model
    => V has a perfect model of the same kind.           (EAR4)
```

This is an exact value-one statement.  It does not follow by substituting
`epsilon=0` in the robust answer-reduction theorem, whose stated error has
a finite-field floor; it follows from the zero-rejection algebra of the
particular line tests.

## What exactness does not say

The classical refinement may be a nontrivial mixture of polynomial tables.
Nor must `g_1,g_2` be the canonical multilinear encodings used by the honest
completeness strategy.  The PCP fixes their decoded Boolean-cube values,
not their off-cube extension.  Definition 10.22 in fact forces the odd
integer `d=k` to be at least `7`: its condition
`(2+5k)m'/2^k<1/2` already fails for `k=1,3,5`.  One may therefore add a
nonzero multiple of

```text
x_j(1-x_j)                                               (EAR5)
```

to an honest multilinear `g_i`.  The redefined formula-test polynomial
`c_0` has individual degree at most `4`, and Proposition 10.21 supplies
degree-at-most-`4` coefficients `c_j` for the zero-on-subcube identity.
The resulting distinct low-degree table is still accepted everywhere and
decodes to the same source answer.  Auxiliary `c_j` witnesses can likewise
be changed by the usual syzygies between `z_i(1-z_i)` and
`z_j(1-z_j)`.  Degenerate
zero-direction line questions can also retain syntactic polynomial-label
freedom, although this does not change any point table.

Thus `(EAR4)` supplies exact source-atom reconstruction, but it supplies
neither a unique/canonical PCP proof, nor an affine dependence of the proof
on the source answer, nor a coherent proof section across different source
outcomes or question pairs.  In particular it does not remove the affine
support and coherent-PCPP-section fences recorded elsewhere in Cairn.

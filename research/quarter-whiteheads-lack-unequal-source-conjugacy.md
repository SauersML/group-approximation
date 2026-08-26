---
rg: 2
id: quarter-whiteheads-lack-unequal-source-conjugacy
kind: claim
title: The two quarter-label Whiteheads have no named unequal-source conjugacy rows
artifacts:
  - research/quarter-whitehead-source-row-audit-proof.md
distinct_from:
  same-center-whitehead-gram-is-not-native-selector-gram: that rejects replacing the prescribed quarter/eighth target pair by the tautological Gram of two quarter-label Whiteheads; this tests the different proposal of keeping both quarter outputs and importing unequal source ranks from existing native or Hecke covariance rows.
  center-chain-four-hecke-flags-have-native-ranks: that computes source fractions `1/2,1/4` and target fractions `1/4,1/8` for four compressed Hecke flags without typing an occurrence row; this audits whether its source flags are already conjugated to the literal quarter-label Whiteheads.
  projective-row-data-do-not-authenticate-hecke-polars: that permits independent spectator gauges in separately named source/target covariance rows; this keeps the conjugate Whitehead gauges fixed and proves that no named mixed row identifies those separate targets with them.
---

**ESTABLISHED BOUNDED COVARIANCE AUDIT.**  On the same-center carrier `F`,
the two literal native Whiteheads have the exact forms

```text
W_1=J_1=SWAP_(1,2) tensor V_1,
W_2=J_2=SWAP_(2,3) tensor V_2,                         (QWS1)
```

where each fixed label swap has negative fraction `1/4`, and the Coxeter
braid makes `V_1,V_2` unitarily conjugate.

There would be a valid affine shortcut if existing ordinary rows supplied
unitaries `U_i` and actual source reflections `R_i` on one positive
reducing carrier with

```text
U_1R_1U_1^*=W_1,       neg(R_1)=1/2,
U_2R_2U_2^*=W_2,       neg(R_2)=1/4.                  (QWS2)
```

Indeed, writing `theta` for the common positive spectral fraction of the
conjugate `V_i`, both target label fractions would be `q=1/4`, so the two
affine equations would be

```text
1/2=3/4-theta/2,       1/4=3/4-theta/2.               (QWS3)
```

Equivalently the first row forces `theta=1/2` and the second forces
`theta=1`.  Robustly, if the two row defects are `delta_1,delta_2`, then

```text
delta_1>=|theta-1/2|,       delta_2>=|theta-1|,
delta_1+delta_2>=1/2,       delta_1^2+delta_2^2>=1/8,
max(delta_1,delta_2)>=1/4.                               (QWS4)
```

Thus no analytic one-eighth reflection would be needed **after** `(QWS2)`.
But none of the established named native or Hecke covariance rows is
`(QWS2)`:

1.  The literal same-center covariance rows are

    ```text
    W_mA_mW_m^*=A_(m+1),       W_mB_mW_m^*=B_(m+1).   (QWS5)
    ```

    Every displayed `A_m,B_m` is a balanced Pauli reflection.  More
    importantly, `W_m` is the **conjugator** in `(QWS5)`, not the target
    reflection.  Its reservoir factor occurs twice and cancels from the
    Pauli covariance, so `(QWS5)` does not attach `V_m` to either output.

2.  The four center-chain Hecke flags do have source fractions `1/2,1/4`,
    but they are supports of the compressed partial isometries `eB_2e` and
    `eB_3e`.  No established ordinary unitary row conjugates their source
    reflections to `W_1,W_2`.  Their rank calculation is explicitly
    occurrence-untyped.  They also start on `e=e_chi` for the center-chain
    subgroup, whereas `(QWS1)` is typed on the same-center cut
    `F=((1-z)/2)((1-C)/2)`; no named row identifies these carriers.
    In particular, writing `1-2r_i` for the two support projections would
    manufacture analytic group-algebra reflections, not identify actual
    group words.  The finite regular model makes every nonidentity ordinary
    involution half-negative, while a quarter cut can occur only after a
    representation-type choice whose authenticated transports preserve its
    rank.  Thus the proposed source reflections themselves are absent from
    the named ordinary-word menu.

3.  On the largest positive corner reducing both `J_1,J_2`, the two
    Whiteheads retain the forms `(QWS1)`, but the two cumulative Hecke
    target maps collapse:

    ```text
    (eA_1e)p_*=(eA_2A_1e)p_*.                         (QWS6)
    ```

    Hence restriction to a common Whitehead carrier erases, rather than
    authenticates, the unequal Hecke row.

4.  The compression-preimage conjugacies

    ```text
    T_1W_87(s_0,t_0)T_1^(-1)=J_1,
    T_2W_98(x_1,y_1)T_2^(-1)=J_2                     (QWS7)
    ```

    relate Whitehead occurrences across moving charts.  Their source words
    have no independently authenticated negative fractions `1/2,1/4`, and
    their reservoir equation is the two-chart identity
    `D_(J_i)=B D_(W_i) A^(-1)`, not a shared-gauge affine row.

5.  The odd order-seven words `(J_iv_i)^7=1` do not supply a hidden source
    covariance.  They remove a spectator only after a `J_i`-reducing Hecke
    cut has already been authenticated.  They contain no conjugacy from the
    reflections of the two Hecke source supports to `J_i`; their unresolved
    compression leakage is exactly the missing carrier input.

The scoped finite obstruction is exact.  Take the same-center three-qubit
Pauli model and a finite `S_3` reservoir with `V_1,V_2` the two adjacent
transpositions; this realizes `(QWS1)`, `(QWS5)`, and the braid with
nontrivial conjugate gauges.  Independently, the balanced-spectator model of
the separately projective native rows realizes their correct source/target
ranks and every named separate covariance.  Their direct product preserves
all these rows because no displayed relation equates either projective
target with `W_i`.  The proposed contradiction appears only after adding
exactly the missing mixed identifications `(QWS2)`.

Therefore the smallest alternative compiler input is not a new analytic
label reflection.  It is one positive-carrier ordinary occurrence row for
each source scale which places the literal `W_i` itself on the target side
of a conjugacy with the actual source reflections of fractions `1/2` and
`1/4`, while preserving the already conjugate `V_i` gauges.  No such row is
currently established.  Imposing it as a fixed whole-carrier identity is
not a construction: `(QWS3)` would collapse that carrier in the exact
regular model.  A positive route must derive both comparisons on a
model-dependent positive subcorner with loss charged to ordinary word
defects; deriving them would already be the desired no-microstate proof.
No Property T, Kazhdan input, canonical trace
profile, literature theorem, local computation, or Lean compilation is
used.

DERIVATION
quarter-whitehead-source-row-audit-proof

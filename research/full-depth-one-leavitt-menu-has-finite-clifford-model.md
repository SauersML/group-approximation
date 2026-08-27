---
rg: 2
id: full-depth-one-leavitt-menu-has-finite-clifford-model
kind: claim
title: The complete depth-one Leavitt actor menu has a finite marked Clifford model
invalidates:
  - depth-one-actor-menu-supplies-moving-bridges
artifacts:
  - research/full-depth-one-leavitt-menu-clifford-proof.md
distinct_from:
  binary-branch-flip-weyl-has-s3-c2-model: that adds the first full branch-exchange Weyl word to the closed compression-fold cell; this closes every depth-one root-position relabeling and mixed square at once.
  finite-positive-root-fragments-have-marked-regular-models: that treats arbitrary positive-root coefficient fragments but no opposite-root actors; this includes all depth-one opposite-root Whiteheads and Weyl conjugacies used by ESB.
  finite-extraspecial-mixed-words-cannot-ungauge-singer-transport: that assumes a normal extraspecial packet and permits arbitrary finite normalizer enlargements; the depth-one compression preimages here are nonnormal, and finiteness is proved from their explicit role/Pauli action.
---

**ESTABLISHED DEPTH-ONE FIREWALL.**  Let `M_1` be the complete finite
occurrence menu consisting of:

1. both binary inverse and crossed-zero coefficient rows;
2. the common-output range-sum row `C_0C_1=J`;
3. both exact compression-preimage identities `(CPW3)`;
4. the branch-flip unit `u=s_0t_1+s_1t_0` and Weyl conjugacies `(BFW4)`;
5. every fixed root-position Weyl permutation used to put these rows in the
   signed-Hecke and ESB coordinate roles; and
6. every conjugacy/naturality mixed square among the named occurrences and
   their depth-one Singer translates.

All coefficient occurrences are literal and shared: the same named arm is
used in its inverse, crossed-zero, Whitehead, branch-flip, and fold rows.
`M_1` has one exact finite monomial/Clifford model in which the marked
involution remains nontrivial.

Start with the three character signs and two controlled Pauli factors from
`(BFW5)`.  Their generated matrix group is finite.  The two compression
preimages act by the transpositions `W_0,W_1`; the branch-flip acts by

```text
(1 2)_(characters) tensor SWAP_(two Pauli factors),    (DFC1)
```

and the inverse/crossed-zero/fold outputs are the already exact controlled
Pauli commutators.  Every depth-one coefficient conjugacy acts on the four
Pauli exponent bits by a permutation or binary symplectic transvection.
Hence it is implemented inside the finite two-qubit Clifford group.

For the root positions, let `Omega` be the finite set of coordinate roles
appearing in `M_1`.  Put every fixed Weyl/root-position relabeling on the
permutation factor `l^2(Omega)`.  A conjugated occurrence is represented by
the literal conjugate of its source Pauli/character operator.  Consequently
all mixed squares commute exactly: both paths are the same permutation of
`Omega` followed by the same Clifford automorphism of the Pauli label.
The depth-one Singer translates add only their finite seven-coordinate actor
permutations and therefore remain in the same finite monomial group.

Thus the complete actor lies in the finite group

```text
G_1 <= Mon(Omega) semidirect
       (((C_2)^2 semidirect S_3) x Clifford_2).         (DFC2)
```

The concrete model already has a positive-rank `J=-1` projection.  If a
canonical exact marked model is desired, take the left regular
representation of `G_1`: the nonidentity involution `J` then has trace zero,

```text
||lambda_(G_1)(J)-1||_2=sqrt(2),                       (DFC3)
```

while every row of `M_1`, including all mixed squares, has zero defect.

Therefore no estimate proving `(ESB2)` can follow from the **entire
depth-one menu**, rather than merely from one audited word at a time.  The
first relation capable of breaking this firewall must leave the finite
role/Clifford action.  Concretely it must distinguish two address histories
which have the same depth-one Pauli label—for example a depth-two asymmetric
payload return or a coefficient occurrence whose action is not an affine
symplectic relabeling.  No Property `(T)`, Kazhdan input, trace profile,
literature theorem, or Steinberg lift is used.

## Attempts

- **Add every missing Weyl square simultaneously.**  Defining every target
  occurrence by literal conjugation makes the squares naturality identities
  inside the finite monomial group; no new reservoir equation appears.
- **Use the depth-one Singer permutations.**  They enlarge the finite role
  permutation factor but do not act nontrivially on the independent Clifford
  multiplicity coordinate.
- **Regularize the whole actor menu.**  This strengthens the fence: the left
  regular model makes all menu relations exact and keeps the mark at fixed
  normalized-HS distance `sqrt(2)` from the identity.

DERIVATION
full-depth-one-leavitt-menu-clifford-proof


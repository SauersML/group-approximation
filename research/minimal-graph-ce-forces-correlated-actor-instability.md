---
rg: 2
id: minimal-graph-ce-forces-correlated-actor-instability
kind: claim
title: Rank-three minimal-graph CE forces correlated actor and projective-Clifford instability
distinct_from:
  kt-full-actor-extension-is-locally-hs-unstable: that supplies generic bad actor microstates whose lamp sites all coincide and therefore fail the marked correlation maximally; this extracts instability from canonical minimal-graph microstates carrying the marked Majorana wall
  kt-majorana-wall-certifies-macroscopic-actor-instability: that gives a quantitative local bound for the rank-three Laurent interface; this records the full weak-ucp consequence for the complete actor and the separate blockwise projective-Clifford dichotomy
  kazhdan-weak-ucp-stability-is-flexible-stability: that is an abstract equivalence for hyperlinear Kazhdan groups; this supplies the canonical correlated actor approximation which contradicts either equivalent stability property
  minimal-marked-graph-crossed-product-ce: that asks for every lamp, actor and mixed moment of one named crossed product; this proves necessary instability consequences and does not claim that either is sufficient
---

Use the endpoint-relevant Kun--Thom choice `q=2`, `r=d=3` and the notation
of `minimal-marked-graph-crossed-product-ce`.  Let `K subset Gamma` be a
finite Kazhdan generating packet, let `o=Gamma`, and put

```text
h=e_12((x_1 x_2 x_3)^(-1)),       y=h Gamma.
```

The minimal marked form has `b(delta_o,delta_y)=1`, and `h` belongs to the
normal closure of `Gamma` in `G`.

**Theorem.**  If

```text
M_min=A_(S_min) crossed_product G
```

is Connes embeddable, then:

1. `G` is neither flexibly normalized-Hilbert--Schmidt stable nor weakly
   ucp-stable;
2. on the fixed finite image table of the finitely presented Steinberg
   cover, the CE microstates cannot be retracted at vanishing normalized-HS
   cost to invariant irreducible Clifford blocks with blockwise-normalizer
   actor maps.

## The canonical correlated actor witness

Connes embeddability supplies actor matrices `u_g` and, after spectral
rounding, a self-adjoint involution `c` lifting the base lamp.  Set

```text
d=u_h c u_h^*.
```

Along the matrix sequence,

```text
max_(s in K)||[c,u_s]||_2 -> 0,
||cd+dc||_2 -> 0.                                      (MCI1)
```

The first row is base-lamp stabilizer covariance and the second is the
marked edge.  The actor restriction is a hyperlinear approximation of `G`:
all fixed multiplication defects vanish and the crossed-product trace is
zero on every nonidentity actor word.

Suppose `G` were weakly ucp-stable.  Kun--Thom Theorem E makes `G`
residually finite and Kazhdan, hence hyperlinear, so
`kazhdan-weak-ucp-stability-is-flexible-stability` upgrades this to flexible
HS-stability.  After adding `o(dim)` dimensions, the `u_g` are compressions
of genuine finite-dimensional representations `rho_n` of `G`.

Extend `c` by the identity on the added corner.  Off-diagonal leakage and
the first row of `(MCI1)` make this extension asymptotically commute with
`rho_n(K)`.  Kazhdan averaging followed by spectral rounding replaces it at
`o_2(1)` cost by an involution in `rho_n(Gamma)'`.  By
`infranormal-compact-closure-normal`, the closure of `rho_n(Gamma)` is normal
in the compact closure of `rho_n(G)`.  Since `h` lies in the normal closure
of `Gamma`, `rho_n(h)` belongs to the former closure.  The rounded
involution therefore commutes with `rho_n(h)`.  Compressing back gives

```text
||[c,u_h]||_2 -> 0.
```

Hence `d-c -> 0` and `||cd+dc||_2 -> 2`, contradicting `(MCI1)`.  This proves
item 1.

## The projective-Clifford retraction failure

Fix the finite actor multiplication table from
`finite-presentation-refutes-marked-graph-scalar-window`, containing the
images in `G` of all presentation prefixes of the Steinberg actor cover,
and let it have `m` triangles.  Call a **covariant Clifford retraction** a vanishing-HS perturbation
which writes the model as

```text
H=directSum_i H_i,
```

with exact completed Clifford lamps on every irreducible `H_i`, exact tested
lamp covariance, and block-preserving Clifford-normalizer actor matrices.
Let `eta` be the maximum normalized-HS change of a tested actor matrix and
`epsilon` the original maximum multiplication defect.  The unitary product
Lipschitz estimate gives

```text
max_triangle ||u'_g u'_k-u'_(gk)||_2 <= epsilon+3 eta. (MCI2)
```

On every block and triangle the multiplication curvature is a scalar times
one Pauli operator.  Once every squared triangle defect is below `2/m`,
`clifford-direct-sum-dilution-forces-an-exact-good-block` selects a block on
which all `m` phase-space curvatures are scalar simultaneously.  That block
is precisely the scalar-curvature section forbidden by the Steinberg-cover
claim.  Hence no CE microstate sequence can admit a covariant Clifford
retraction at vanishing cost.  Quantitatively, otherwise the direct-sum
theorem applies as soon as every squared triangle defect is below `2/m`, so

```text
epsilon+3 eta >= sqrt(2/m).                             (MCI3)
```

Along CE microstates `epsilon->0`, giving the fixed floor
`liminf eta >= sqrt(2/m)/3`.  This proves item 2.

## Exact scope

Item 2 does not use a finite presentation of `G`.  Allcock finitely presents
`St_3(R)`, and the table uses only the images in `G` of its finitely many
generators and relator prefixes.  Thus the uncontrolled unstable kernel
`K_2(3,R)` is bypassed rather than finitely normally generated.

The theorem is a frontier compression, not a converse.  Generic actor
instability does not construct `(MCI1)`:
`kt-full-actor-extension-is-locally-hs-unstable` extends its bad actor tuples
only with a central balanced lamp, so all lamp sites coincide and the second
row of `(MCI1)` has norm `2`.  Conversely,
`clifford-phase-space-curvature-is-a-twisted-f2-cocycle` starts after a fixed
exact blockwise symplectic action has been chosen; it does not supply the
covariant retraction.  Weak-ucp failure, generic local instability, and
fixed-action cocycle repair are therefore necessary boundary information,
not solutions of the CE target.

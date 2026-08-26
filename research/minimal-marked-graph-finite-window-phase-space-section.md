---
rg: 2
id: minimal-marked-graph-finite-window-phase-space-section
kind: claim
title: Finite marked-graph windows admit Clifford lifts with scalar-only multiplication curvature
distinct_from:
  finite-clifford-symplectic-section-obstruction: that rules out a global multiplicative section of the full finite symplectic group; this asks only for scalar curvature on one prescribed finite partial group table, after choosing a new vertex-supported completion for that table
  vertex-supported-symplectic-completion: that solves the finite lamp algebra and its trace exactly but supplies no actor maps; this is precisely the missing actor-coherence statement on top of those completed blocks
  minimal-marked-graph-crossed-product-ce: that is the full Connes-embeddability conclusion; this is a concrete sufficient finite-window certificate whose scalar curvature can be cancelled by conjugate doubling
  kun-thom-clifford-relative-wall: that asks only for one wall in a matrix ultraproduct; this constructs all tested lamp and actor moments for the named minimal marked-graph crossed product
---

Let `S_min` be the minimal marked orbital graph of the Kun--Thom pair,
`V = F_2^(G/Gamma)` with its nondegenerate adjacency form `b`, and
`A_min` its twisted lamp factor.

**Claim.**  For every finite actor table `E subset G`, finite lamp window
`F subset G/Gamma`, and finite set of tested products

```text
T subset {(g,h,gh): g,h,gh in E},
```

there are a finite nondegenerate binary symplectic space `K`, an isometric
map of the tested lamp span into `K`, its irreducible Clifford matrices
`W_x`, `x in F`, and Clifford-normalizer unitaries `U_g`, `g in E`, such
that:

1. the `W_x` have exactly the signs prescribed by `b`, and every nontrivial
   tested Weyl word has normalized trace zero;
2. `U_g W_x U_g^* = W_(gx)` whenever `x,gx in F` is a tested covariance
   equation;
3. for every `(g,h,gh) in T`, the Clifford multiplication curvature has
   zero phase-space component:

   ```text
   U_g U_h U_(gh)^* in T 1.                         (FWP1)
   ```

The completion and the lifts may depend on the whole finite table.  No
global section `Sp(K) -> Clifford(K)` is requested.

## Why this certificate is sufficient

Write `(FWP1)` as

```text
U_g U_h = omega(g,h) U_(gh).
```

Replace the actor by

```text
Uhat_g = U_g tensor conjugate(U_g)
```

and represent each lamp by `W_x tensor 1`.  The scalar multipliers cancel,
so every tested actor product is now exact, while the first tensor factor
retains the required lamp covariance and twisted lamp trace.

The Kun--Thom actor `G` is residually finite.  Tensor once more with the
regular representation of a finite quotient which separates the finitely
many nonidentity actor words being tested.  This kills their normalized
traces exactly.  Mixed lamp--actor words with nonidentity actor part are
killed by the same tensor factor, while words with identity actor part keep
the exact Clifford trace from item 1.  Thus the certificate produces all
finite-window microstates in the finite-window formulation of
`minimal-marked-graph-crossed-product-ce`.

Consequently this claim implies
`minimal-marked-graph-crossed-product-ce`, hence
`invariant-graph-crossed-product-ce` and the Kun--Thom hyperlinear-nonsofic
endpoint.

## Why the known nonsplitting theorem does not decide it

`finite-clifford-symplectic-section-obstruction` says that for a fixed qubit
block of rank at least two there is no multiplicative section on the entire
symplectic group.  Here only finitely many partial actor maps and finitely
many multiplication triangles are prescribed, the ambient completion may
change with the window, and scalar curvature is allowed.  The global
nonsplitting theorem therefore supplies a design constraint but not a
counterexample.

What remains is the phase-space part of the Clifford factor set.  Scalar Weil
multipliers are harmless by conjugate doubling; a nonzero Pauli label is not.

## Attempts

- **Use one global symplectic-to-Clifford section — dead.**
  `finite-clifford-symplectic-section-obstruction` rules this out in every
  qubit block of rank at least two.  The finite-window target deliberately
  permits a new completion for each table and asks only for a partial
  scalar-curvature lift.
- **Average independently completed blocks — does not bypass the target.**
  `clifford-direct-sum-dilution-forces-an-exact-good-block` shows that, below
  the fixed `2/m` threshold for `m` tested triangles, one constituent block
  already has zero Pauli factor on every triangle.  Randomness may search for
  that block but cannot replace its existence.
- **Private-neighbour completion — live, not yet reduced.**  The available
  `private-neighbour-density` theorem supplies many vertex choices while
  preserving nondegeneracy.  The open calculation is whether requiring the
  finitely many phase-space factor labels to vanish cuts out only finitely
  many affine denominator cosets in those Laurent parameters.  If it does,
  density chooses all completion vertices simultaneously; no such affine
  description has yet been proved.

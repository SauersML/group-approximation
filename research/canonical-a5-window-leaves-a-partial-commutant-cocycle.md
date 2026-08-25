---
rg: 2
id: canonical-a5-window-leaves-a-partial-commutant-cocycle
kind: claim
title: Canonical A5 windows exactify to regular packets but leave a full partial-commutant cocycle
distinct_from:
  simple-lamp-normalizers-have-unitary-multiplicity-fibers: that computes the normalizer of a whole finite lamp packet under a total automorphism; this gives the partial-window normal form, its dimension-free conditional-expectation estimate, and the boundary-completion holonomy.
  full-a5-path-memory-kills-holonomy-but-not-reiter-boundary: that transports bases along a path-labelled carrier and computes its Reiter loss; this starts directly from a canonical lamp microstate, exactifies the fixed packet, and identifies the operator algebra in which every unmatched boundary arrow remains free.
  finite-cylinder-mixed-traces-kill-normalizer-holonomy: that removes the cocycle after a finite actor group acts on one common atom PVM; this proves why those mixed traces have no stabilizer table to act on before boundary completion and identifies the minimal additional copy-Cartan datum.
  invariant-cartan-completion: that asks for one actor-normalized diagonal ultraproduct for the whole Kun--Thom Bernoulli algebra; this gives the finite-window regular-packet normal form and proves quantitatively why a bounded family of binary address labels cannot construct that diagonal.
---

**ESTABLISHED FIXED-WINDOW NORMAL FORM AND EXACT OBSTRUCTION.**  Let `K` be
`A5` (the same statements hold for `C2`), let `Y` be finite, and put

```text
Q_Y=K^Y.
```

A canonical normalized-Hilbert--Schmidt microstate restricted to `Q_Y`
can, after the standard flexible finite-group exactification, be written on
a `1-o(1)` regular core as

```text
lambda_(Q_Y) tensor 1_(m_n).                            (APC1)
```

This follows from the canonical character: finite-group exactification and
Plancherel multiplicities extract a multiple of the regular representation,
with only `o(d_n)` dimensions left over.  Thus there is no residual
irreducible-type freedom on one fixed lamp window.

What survives is much larger.  Let `D,R subset Y`, let
`alpha:K^D->K^R` be the coordinate isomorphism induced by one actor arrow,
and choose any bijection `bar alpha:Y->Y` extending it.  On

```text
H_Y=ell^2(Q_Y) tensor C^m
```

let `P_(bar alpha)` be the canonical basis permutation.  If a unitary `U`
implements `alpha` on the named source coordinates, then

```text
C=P_(bar alpha)^* U
  belongs to lambda(K^D)'                                (APC2)
```

and, under `Q_Y=K^D times K^(Y minus D)`,

```text
lambda(K^D)'
 =rho(K^D)'' tensor
   B(ell^2(K^(Y minus D)) tensor C^m).                  (APC3)
```

This is the exact residual multiplicity algebra.  A single missing boundary
coordinate leaves a full matrix factor of size at least `|K|m`; the freedom
is not small in normalized Hilbert--Schmidt norm.

The normal form is dimension-uniformly robust.  If

```text
max_(q in K^D)
 ||U lambda(q) U^* - lambda(alpha(q))||_2 <= epsilon,   (APC4)
```

then averaging `C` over the finite group `lambda(K^D)` gives a contraction
`B` in the commutant with `||B-C||_2<=epsilon`.  Since `C` is unitary,
`||B^*B-1||_2<=2 epsilon`; extending the polar part of `B` inside the finite
commutant gives a unitary `V in lambda(K^D)'` with

```text
||U-P_(bar alpha)V||_2 <= 3 epsilon.                    (APC5)
```

Pairwise alignment of the regular source and target cores costs only the
usual `o(1)` exactification term for a fixed collection of arrows.  It does
not select the different `V`'s coherently.

For actor words `g,h`, choose arbitrary boundary completions `bar alpha_g`.
Writing `U_g=P_g C_g`, actor multiplication has the exact bookkeeping

```text
C_(gh) approximately
 Omega(g,h) (P_h^* C_g P_h) C_h,                       (APC6)

Omega(g,h)=P_(gh)^* P_g P_h.                           (APC7)
```

The approximation loss is the original actor product defect plus the fixed
errors in `(APC5)`.  The permutation `Omega(g,h)` is the boundary-completion
holonomy; even when it is killed along a tree, `(APC3)` leaves the arbitrary
unitary cocycle.  This is the exact finite-window residue, not an unspecified
rounding loss.

Canonical mixed traces do not remove it before a coherent finite actor table
has been built.  If `(P_g^0)` is any partial lamp-coordinate implementation
and `(v_g)` is any canonical actor microstate, then

```text
U_g=P_g^0 tensor v_g                                    (APC8)
```

has the same lamp covariance, while its actor defects contain precisely
those of `v`.  For a mixed lamp--actor word with nonidentity actor grade,
the normalized trace factors through `tr(v_g)=o(1)`; at identity actor grade,
the regular lamp factor kills every nontrivial lamp word.  Hence all fixed
canonical mixed-word tests remain compatible with the full multiplicity
cocycle in `(APC3)`.

## Minimal additional datum

The exact datum which would force monomial behavior is an actor-normalized
Cartan algebra on the copy factor.  Namely, if the residual space carries a
rank-one PVM `(E_j)` and every `C_g` normalizes its diagonal algebra, then
each `C_g` is monomial in the common basis.  Once a coherent finite actor
table on these atoms exists, the cylinder-resolved stabilizer trace identities
of `finite-cylinder-mixed-traces-kill-normalizer-holonomy` extract a
`1-o(1)` pure permutation core and remove the phases.

A fixed finite family of binary copy labels is insufficient.  If `r`
commuting involutions are named, their joint PVM has at most `2^r` atoms.
On a multiplicity space of dimension tending to infinity, one atom has
dimension at least `m/2^r`; an arbitrary Fourier unitary on that atom
commutes with all the labels and remains a fixed positive normalized-HS
distance from every monomial in the chosen basis.  If that atom has rank
`M` in total dimension `m`, the squared distance is at least

```text
2(M-sqrt(M))/m >= 2^(1-r)-o(1).                         (APC9)
```

Thus the added relation
must be genuinely self-similar: it must generate an unbounded, asymptotically
separating family of copy atoms (equivalently, an invariant copy Cartan), not
one more fixed `C2` clock.

The Fourier example concerns what the named labels force in their adapted
basis.  A later conjugacy inside a large unresolved atom might monomialize a
particular actor representation; proving that it does so jointly for every
actor word is exactly the original actor-classicalization problem.  Thus the
example is a no-go for bounded address relations, not an independent proof
that the pinned actor has a nonmonomial finite-dimensional representation.

Adding finitely many further regular A5 or C2 packets does not improve this
conclusion.  For finite packets `Q_1,...,Q_r` and any actor microstate `v`,
the exact tensor model

```text
H=(tensor_j ell^2(Q_j)) tensor H_v,
U_g=(tensor_j P_(alpha_(g,j))) tensor v_g              (APC10)
```

satisfies every packet covariance and actor product to exactly the accuracy
of `v`; all nonidentity actor-grade mixed traces are still killed by the
`v_g` factor.  The residual algebra still contains `B(H_v)`.  Hence a fixed
depth of self-similar regular packets only divides off more named regular
factors; arbitrary external amplification restores the entire cocycle.  Even
a windowwise tower has this issue unless a relation couples its tail to a
specific diagonal on `H_v`.  Recursive packet replication is therefore not
the missing extra relation.

There is a general amplification reason for this.  Every fixed ordinary
group-word relation is preserved by `rho -> rho tensor 1_M`, and every
projection obtained functorially from those word matrices is likewise
amplified by `1_M`.  Its generated algebra therefore has `M_M(C)` in its
commutant.  No fixed word relation can canonically name rank-one copy atoms
inside all amplifications.  The required Cartan is consequently an analytic
existence/selection statement about the actor cocycle, not another finite
lamp relator whose spectral projections automatically resolve multiplicity.

This identifies the logical status of the proposed extra relation.  An
actor-normalized asymptotically separating copy PVM is already the finite
probability carrier on which the partial site maps acquire coherent boundary
completions.  Extracting it from arbitrary wreath microstates is precisely
the action-soficity/invariant-Cartan gate.  It is a minimal sufficient
interface, but not a weaker consequence of fixed-window A5 or C2
exactification.

DERIVATION
canonical-a5-partial-commutant-normal-form-proof

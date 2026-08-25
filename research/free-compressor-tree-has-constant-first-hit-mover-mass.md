---
rg: 2
id: free-compressor-tree-has-constant-first-hit-mover-mass
kind: claim
title: The free compressor tree has constant aggregate first-hit mover mass, but no common Reynolds density
distinct_from:
  opposite-transvections-are-free-but-finite-lamp-windows-close: That proves the free positive-monoid boundary and bounded-window congruence models; this constructs stabilizer-sensitive dyadic exit projections on the whole binary tree and computes their exact aggregate displacement.
  selector-baumslag-orbits-overlap-or-prepay: That treats one stationary binary orbit and obtains a geometric first-hit ledger; this uses binary branching to compensate the geometric loss exactly at each level.
  property-t-hs-positive-density-commutant-no-growth: That excludes a positive normalized-adjoint-density child-only spectral sector; this shows why the depth-N tree supplies only finitely many adjoint vectors, despite carrying constant physical Hilbert mass.
  aggregate-leaf-bessel-fails-after-prefix-transport: That gives the exact fixed-error Bessel/frame criterion and a canonical one-compressor property-(T) countermodel; this constructs the physical dyadic leaves and states the full two-compressor estimate that remains open.
---

**ESTABLISHED FINITE-DEPTH TREE CALCULATION.**  Work in the canonical binary
Bernoulli wreath of the Kun--Thom pair, and let

```text
A=I+E_12,                    B=I+E_21
```

be the opposite positive transvections.  For a positive word `v`, write

```text
x_v=v Gamma,                H_v=v Gamma v^(-1),
p_v=(1-l_(x_v))/2,                                      (FCT1)
```

where `l_x` is the binary lamp at the site `x`.  Freeness of the positive
monoid makes the sites `x_v` distinct.  Put

```text
e_(v,A)=p_v,                e_(v,B)=1-p_v.
```

If `w=s_1...s_n`, with prefixes `v_k=s_1...s_k` and `v_0=1`, define the
dyadic prefix and its leaf exit by

```text
Z_w=product_(k=1)^n e_(v_(k-1),s_k),
X_w=Z_w p_w.                                            (FCT2)
```

At every fixed depth `n`, the `Z_w`, `|w|=n`, are pairwise orthogonal and
sum to one.  The leaf coordinate does not occur in its prefix, so the
canonical Bernoulli trace gives

```text
tau(Z_w)=2^(-n),              tau(X_w)=2^(-(n+1)).      (FCT3)
```

This is the binary-tree compensation absent from a one-dimensional
first-hit ladder: although each leaf pays `2^(-n)`, there are `2^n` leaves.

The exits are genuinely stabilizer-sensitive.  Strictness lets us choose,
once and for all,

```text
r_S in Gamma \ S Gamma S^(-1),             S in {A,B}.
```

For the last edge `w=vS`, put

```text
gamma_w=v r_S v^(-1) in H_v \ H_w.                     (FCT4)
```

Since `H_w<=H_u` for every prefix `u` of `w`, every factor of `X_w`
commutes with `H_w`.  Moreover `gamma_w` fixes all the prefix sites in
`Z_w`, but moves `x_w` to the distinct site `gamma_w x_w`.  Independence of
the two leaf lamps therefore gives

```text
tau(X_w gamma_w X_w gamma_w^(-1))=2^(-(n+2)),
||gamma_w X_w gamma_w^(-1)-X_w||_2^2=2^(-(n+1)).        (FCT5)
```

Summing over the level proves the depth-independent identity

```text
sum_(|w|=n)||gamma_w X_w gamma_w^(-1)-X_w||_2^2=1/2.   (FCT6)
```

Thus the free boundary **can** be converted into pairwise orthogonal
first-hit exits without losing aggregate physical mass.  First-hit capacity
is not the remaining obstruction on this branch.

## The missing Reynolds inequality

The calculation does not yet imply an HS floor for an approximate ordinary
group representation.  Each `X_w` is one vector of the normalized adjoint
Hilbert space `L^2(M_d)`.  Even if all `2^n` vectors are retained exactly,
their span has normalized adjoint rank at most

```text
2^n/d^2.                                                (FCT7)
```

For fixed presentation depth `n`, this tends to zero as `d` tends to
infinity.  The theorem
`property-t-hs-positive-density-commutant-no-growth` controls normalized
**adjoint dimension**, not the physical ranks `tau(X_w)d`; consequently it
does not bound the left side of `(FCT6)`.  Conjugating the leaves back to a
common last-edge subgroup does not repair this: the different prefix
cylinders cease to be orthogonal after the leaf-dependent conjugations.

Taking `n` of order `log d` would make `(FCT7)` macroscopic, but that changes
the tested words with the matrix dimension.  Canonical microstate
convergence is only uniform on each fixed finite word menu, and the word
telescoping and spectral-comparison constants also depend on `n`.  There is
no dimension-versus-radius bound in the definition of hyperlinearity.

Accordingly the exact remaining row is the depth-uniform estimate

```text
sum_(|w|=n)||[phi(gamma_w),X_w]||_2^2
       <= C E(phi)+o_n(1),                               (FCT8)
```

with `C` independent of `n`, or an equivalent recovery of one common
positive-density adjoint/lamp algebra.  Exact finite-dimensional actor
representations satisfy the zero-error version because
`H_w<H_v` are conjugate copies and finite-dimensional commutant no-growth
gives `pi(H_w)'=pi(H_v)'`.  Proving `(FCT8)` for approximate actor tuples is
precisely the unresolved actor-exactification/Cartan step, not a consequence
of the existing property-`(T)` spectral-count theorem.

The cardinality-free estimate for one fixed relator error does not close this
gap. `aggregate-leaf-bessel-fails-after-prefix-transport` proves
`sum_w||E X_w||_2^2<=||E||_2^2`, but normalizing
`H_v=v Gamma v^(-1)` back to a common Kazhdan copy replaces `E` by the
leaf-dependent conjugates `vEv^(-1)`. Their transported supports need not be
orthogonal: a rank-one wall of mass `1/N` can rotate into `N` leaves and have
aggregate mass one. A uniform transported-frame bound would suffice, but is
new structure. Canonical one-compressor wreath microstates already refute
compressed-to-full promotion from property `(T)` for a single positive-mass
lamp projection; only simultaneous incompatible compressor relations can
possibly repair it.

## Exact row missed by congruence windows

The bounded congruence models from
`opposite-transvections-are-free-but-finite-lamp-windows-close` realize the
positive prefix cylinders, but fail `(FCT5)` exactly.  In every finite
quotient the image of `Gamma` is normal.  Hence

```text
q(gamma_w) q(w) q(Gamma)=q(w) q(Gamma),
```

so the two leaf lamps in `(FCT5)` are identified and the displayed mover
energy is zero, rather than `2^(-(n+1))`.  This is a concrete audit of the
missing row: positive-cone covariance authenticates `(FCT2)--(FCT3)`, while
the `Gamma`-moved compressed-site correlation is exactly the additional
datum needed for `(FCT5)--(FCT6)`.  No claim is made that these congruence
models satisfy that additional datum.

`fct8-left-lift-and-rotated-defect-firewall` audits the most tempting way to
bridge `(FCT6)` and `(FCT8)`.  The rank-one projector onto `C X_w` has
pointwise child-fixed range but only `1/d^2` adjoint trace.  Left
multiplication `L_(X_w)` has the desired trace `tau(X_w)` and preserves the
mover norm exactly, but its range is merely invariant under the child
adjoint action, not pointwise fixed.  Hence the tracial self-copy theorem
does not apply.  An exact block-permutation construction further shows that
barely summing conjugates of one relator defect across the orthogonal leaves
costs at least `2^n`.  Any depth-uniform estimate must use genuinely joint
prefix-unitary/lamp information beyond these automatic lifts.

DERIVATION
free-compressor-tree-first-hit-and-rank-audit

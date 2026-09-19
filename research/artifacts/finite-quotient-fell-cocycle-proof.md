# Finite-quotient Fell untwisting: convention and error audit

This artifact fixes the only convention-sensitive point in
`finite-quotient-fell-untwisting-leaves-kernel-cocycle` and supplies the
finite-window perturbation estimate used there.

## Exact calculation

Let `q:G -> Q` be a finite quotient, let `s:Q -> G` satisfy `q(s(a))=a`, and
let `pi:G -> U(H)` be unitary.  We use the left regular representation

```text
lambda_Q(x) delta_a = delta_(x a).
```

On `ell^2(Q) tensor H` define

```text
R_g = lambda_Q(q(g)) tensor pi(g),
T(delta_a tensor xi) = delta_a tensor pi(s(a)^(-1))xi.
```

Every fibre operator in `T` is unitary, so `T` is unitary and

```text
T^*(delta_a tensor xi) = delta_a tensor pi(s(a))xi.
```

It follows, with no omitted reindexing, that

```text
T R_g T^*(delta_a tensor xi)
 = T R_g(delta_a tensor pi(s(a))xi)
 = T(delta_(q(g)a) tensor pi(g s(a))xi)
 = delta_(q(g)a) tensor pi(s(q(g)a)^(-1) g s(a))xi.     (1)
```

Set `c(g,a)=s(q(g)a)^(-1) g s(a)`.  The section equation yields

```text
q(c(g,a))=(q(g)a)^(-1)q(g)a=1,                         (2)
```

so `c(g,a)` belongs to `ker(q)`.  Moreover,

```text
c(g,q(h)a)c(h,a)
 = s(q(g)q(h)a)^(-1) g s(q(h)a)
     s(q(h)a)^(-1) h s(a)
 = s(q(gh)a)^(-1) gh s(a)
 = c(gh,a).                                             (3)
```

Equations (1)--(3) prove that the finite quotient absorbs only the quotient
coordinate.  The fibre retains the represented kernel cocycle.  On the block
from `a` to `q(g)a`, the transformed operator is the identity precisely when
`pi(c(g,a))=1`.  If `pi=rho o q`, (2) kills every block cocycle; absent such a
condition, the change of basis gives no cancellation of `pi|ker(q)`.

## Fixed-window approximate estimate

Let `u:G -> U(d)` be any unitary-valued map, and use the same block-diagonal
change of basis with `u(s(a)^(-1))`.  If inverse words are evaluated by
adjoints, its transformed `(g,a)` block is exactly

```text
u(x)u(y)u(z),
x=s(q(g)a)^(-1), y=g, z=s(a).
```

For any bi-invariant metric `d` on `U(d)`, two applications of the triangle
inequality give

```text
d(u(x)u(y)u(z),u(xyz))
 <= d(u(x)u(y),u(xy))
    + d(u(xy)u(z),u(xyz)).                              (4)
```

Indeed, insert `u(xy)u(z)` and use right invariance on the first difference.
For finite sets `E subset G` and `A subset Q`, the right side of (4) ranges
over at most `2|E||A|` multiplication tests.  Hence convergence of those
finitely many defects implies uniform convergence of every transformed block
in the window `E times A`.  Normalized Hilbert--Schmidt distance is
bi-invariant, so (4) applies to the metric used by the claim.

This is the full perturbative content: it controls the error in reading the
kernel cocycle.  It does not assert that the exact values `u(c(g,a))` are
trivial, amenable, or permutation-valued.

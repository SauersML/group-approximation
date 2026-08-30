---
rg: 2
title: STW LXXXII order-zero spectral-subdivision theorem and depth-floor audit (2026-08-30)
kind: artifact
---

# Constructive theorem

Let `phi:F->B` be a cpc order-zero map with `F` finite dimensional.  Given
positive multiplier contractions `c_i` summing to one and nearly commuting
with `phi(F)`, the cutdowns

```text
theta_i(x)=c_i^(1/2)phi(x)c_i^(1/2)
```

are cpc and approximately order zero.  Their orthogonality defect is
bounded by `sup ||[c_i,phi(y)]||`, while their sum differs from `phi` by at
most the sum of the square-root commutator bounds.

These approximate maps can be repaired to exact cpc order-zero maps inside
the same hereditary band algebras.  The uniform repair theorem follows by
an ultraproduct contradiction: the limiting map is order zero, hence a
*-homomorphism from the cone `C_0((0,1]) tensor F`; projectivity of the cone
over finite-dimensional `F` lifts it to the product.  This is the same
projectivity input used in Brake--Winter's Toeplitz analysis, and the
order-zero/cone correspondence is Winter--Zacharias,
[arXiv:0903.3290](https://arxiv.org/abs/0903.3290).

Taking `c_i=g_i(h)` for a finite continuous partition of unity and a
quasicentral positive contraction `h` therefore gives a structure-free
spectral subdivision theorem for each individual outgoing colour.  If
same-labelled bands have disjoint scalar supports, their hereditary target
algebras are orthogonal, so they recombine into exact global order-zero
colours.

# Exact hypothesis ledger

- Finite dimensionality of `F` is used twice: projectivity of its cone and
  conversion of pointwise coordinate convergence into map-norm convergence.
- Quasicentrality is required only relative to the finite-dimensional range
  `phi(F)` and only for the finitely many cut functions and their square
  roots.
- The repair occurs inside each hereditary algebra
  `closure(c_i^(1/2)Bc_i^(1/2))`; it does not lose band orthogonality.
- No nuclearity, stability, essentiality, Busby injectivity/fullness, or
  projectional approximate unit is assumed.

# The scalar depth-floor no-go

The constructive theorem does not solve LXXXII.  If `N` original colours
are each independently subdivided by scalar functions whose sum is one,
then at every spectral point at least one band from every original colour
is active.  Hence the combined scalar-band cover has depth at least `N`.
The same conclusion holds for approximate partitions whose sums remain
uniformly positive.

Thus independently banding the `(p+1)+(q+1)` endpoint colours recovers no
better depth than their sum.  It cannot reach `max(p,q)+1` merely through
interval colouring.  A successful universal proof must additionally use
operator support orthogonality between different endpoint colours, allow
bands to vanish where the corresponding operator support vanishes, or
replace/couple colours rather than subdividing each independently.

# Refined remaining hinge

The local spectral/order-zero subdivision problem is now solved for each
finite-dimensional outgoing colour.  The remaining obstruction is global:
construct a **support-sensitive coupled subdivision** of all endpoint
colours whose total active depth is the endpoint maximum plus one.  The
scalar depth-floor theorem proves that independent partitions of unity
cannot do this.

There is now an exact positive theorem once the coupled partition is given.
Let every original colour have its own quasicentral operator-valued partition
of unity and require pieces with the same new label to have orthogonal
supports across different originals.  Cone projectivity repairs each
cutdown inside its hereditary support, after which same-labelled pieces sum
to one cpc order-zero map.  The missing global step is therefore construction
of these coupled partitions from arbitrary ideal--quotient geometry, not
order-zero repair or colour assembly after their existence.

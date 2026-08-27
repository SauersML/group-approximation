---
rg: 2
id: private-matching-free-product-separates-pauli-signs
kind: claim
title: A free-product shift places every private Pauli matching with separated signs
distinct_from:
  relative-c-sixth-pauli-incidence-labeling: that tries to place a dense degree-reduced mixed table and must control threshold rectangles; this uses the private random sampler, whose mixed incidence is a matching and has no mixed contour.
  fp-cayley-expanders-give-bounded-occurrence-edges: that embeds growing equality expanders into bounded Cayley balls; this needs no mixed equality clouds and uses one literal shift orbit.
  oligomorphic-gl-has-unbounded-stabilizer-fillings: that compares contextual pair transports with fixed global question sections; this assigns every private pair one contextual translate and never compares its endpoints to a second mixed occurrence.
---

Let `(b_t)_(t>=0)` be any binary sequence.  In the free address group

```text
A=F(s,p_0,p_1)
```

place the X endpoint of pair `t` at

```text
g_t=s^t
```

and its Z endpoint at

```text
h_t=s^t p_(b_t).                                             (PMF1)
```

Then:

```text
g_t^(-1)h_t=p_(b_t),
{p_0} intersect {p_1}=empty,                                (PMF2)
```

all `g_t` are distinct, and all `h_t` are distinct.  Thus the two sign
double cosets are separated (with trivial equality peripherals), every mixed
edge has one of two fixed offsets, and the mixed occurrence graph is a
matching with no contour at all.

After adjoining involutions `x,z,J`, the occurrence words

```text
x_t=s^t x s^(-t),
z_t=s^t p_(b_t) z p_(b_t)^(-1)s^(-t)                         (PMF3)
```

satisfy

```text
[x_t,z_t]=s^t [x,p_(b_t) z p_(b_t)^(-1)] s^(-t).             (PMF4)
```

Hence every sampled sign check is a conjugate of one of the two prototype
relators

```text
[x,p_0 z p_0^(-1)]=1,
[x,p_1 z p_1^(-1)]=J,                                      (PMF5)
```

with relator area one independently of `t`.  The standard coset-Clifford
representation for the A-invariant pairing which is one on `(g,gp_1)` and
zero on `(g,gp_0)` keeps `J` nontrivial.  Therefore the entire mixed/sign
part of `relative-coset-pauli-incidence-compiler` is complete without
graphical small cancellation, covers, or Higman embedding.

Applied to `private-random-weyl-sampler-forces-growing-matrix-dimension`, the
binary sequence and vector labels are recursive by
`private-weyl-samplers-admit-recursive-selection`.  This does not solve the
remaining same-basis problem.  One must still force the shifted
words `(PMF3)` to decode as the exact additive values labeled by the sampled
vectors `a_t,b_t`, with a uniform normalized-HS modulus.  That is exactly
`same-basis-rounding-interface-for-sparse-weyl-sampler`.

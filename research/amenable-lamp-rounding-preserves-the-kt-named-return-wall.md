---
rg: 2
id: amenable-lamp-rounding-preserves-the-kt-named-return-wall
kind: claim
title: Amenable lamp rounding preserves the Kun--Thom named-return wall
artifacts:
  - research/bcjm-rounding-preserves-the-cyclic-parity-proof.md
distinct_from:
  amenable-hyperlinear-to-sofic-same-dimension-citation: That imports the amenable-group theorem; this tracks the external actor covariance through its output on the specific Kun--Thom parity.
  elementary-abelian-regular-normalizers-have-diffuse-fibers: That gives a general exact Fourier multiplicity countermodel; this proves that every classicalization of a hypothetical canonical Kun--Thom microstate retains the named h-return displacement.
  kt-cyclic-parity-is-an-exact-quasiregular-return-correspondence: That computes the wall in the exact group factor; this transfers it quantitatively to the permutation-valued lamp restriction of an arbitrary trace-faithful matrix microstate.
---

**ESTABLISHED RELATIVE ROUNDING BOUNDARY; THE ROOT REMAINS OPEN.**

Let

~~~text
W=(direct_sum_(G/Gamma) C_2) rtimes G
~~~

be the pinned Kun--Thom binary wreath. Keep the cyclic parity notation

~~~text
P={Gamma,C^(-1)Gamma,C^(-2)Gamma},
v=product_(x in P) z_x,
q=(1+v)/2,
h=e_12(x_2/x_1),
w=h v h^(-1).
~~~

Thus every element of `Gamma` fixes `v`, while `w!=v`; the canonical
lamp trace vanishes on `v,w,vw`.

Suppose hypothetically that

~~~text
theta_n:W -> U(d_n)
~~~

is a trace-faithful hyperlinear approximation. Apply
Burton--Chaudkhari--Juschenko--Muliarchyk, arXiv:2311.09202v2, Theorem 1.1,
to the amenable lamp restriction, with increasing finite test sets. After
diagonalization there are permutation-valued lamp approximations

~~~text
beta_n:direct_sum_(G/Gamma) C_2 -> Sym(d_n)
~~~

such that, for every fixed lamp word `a`,

~~~text
||beta_n(a)-theta_n(a)||_2 -> 0.                         (BLR1)
~~~

Put

~~~text
p_n=(1+beta_n(v))/2,
r_n=(1+beta_n(w))/2,
U_(g,n)=theta_n(g).
~~~

Then `(p_n)` and `(r_n)` are projections in the tracial matrix
ultraproduct. They satisfy

~~~text
||[p_n,U_(s,n)]||_2 -> 0              for every s in Gamma,      (BLR2)

||[p_n,U_(h,n)]||_2 -> 1/sqrt(2),                            (BLR3)

||U_(h,n)p_nU_(h,n)^*-r_n||_2 -> 0.                           (BLR4)
~~~

The conclusion is independent of every choice made by the amenable rounding
theorem. In particular, one may repair its restriction to the fixed finite
group `<v,w>` to an exact permutation action at `o_2(1)` cost; then
`p_n,r_n` are literal half-set projections and the same limits hold.

Thus the Burton--Chaudkhari--Juschenko--Muliarchyk theorem is perfectly
compatible with the external actor covariance on each named row, but it
preserves rather than collapses the pointed Kun--Thom obstruction. Its
random-basis construction turns the lamp wall into a classical half-set
wall. It supplies no reason that the approximate actor return `h` should
lie in the finite-dimensional image of `Gamma`, and hence no reason for
`(BLR3)` to vanish.

Any successful use of amenable classicalization must add a theorem which
acts on the external actor or its multiplicity cocycle and contradicts the
simultaneous limits `(BLR2)--(BLR4)`. That is exactly the remaining
actor-exactification gate, not an omitted equivariance estimate in
arXiv:2311.09202.

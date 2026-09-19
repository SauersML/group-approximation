---
rg: 2
id: common-corner-literal-contexts-stop-at-bass-serre
kind: claim
title: Literal context marginals share one finite corner locally but cannot be completed by finite Bass--Serre gluing
artifacts:
  - research/artifacts/common-corner-literal-context-audit-2026-08-21.md
distinct_from:
  every-boolean-predicate-has-a-character-free-finite-type-block: that constructs one selected finite type separately for each predicate; this tensors all of those types into one common projection and keeps every local marginal a literal group involution.
  all-bcs-contexts-share-one-hyperoctahedral-signed-type: that equalizes the local packet type and atom count for later piecewise transport; this proves a simpler simultaneous common-corner literalization and then isolates why identifying its literal marginals through finite amalgams cannot work.
  root-block-piecewise-transport-cannot-host-nonce-bcs: that excludes an atlas contained in one finite matrix block; this excludes an atlas in the generally infinite corner of every finite graph-of-finite-groups fundamental group.
  monomial-central-sign-has-types-or-affine-returns: that classifies literal returns made universal by one central sign; this permits arbitrary predicates after selecting one primitive type and proves that the obstruction begins only at cross-context compatibility.
---

**ESTABLISHED.**  There is no local literalization obstruction.  Given a
finite BCS with nonempty allowed sets `R_c`, for every context choose the
finite group, irreducible type, and commuting literal involutions

```text
(K_c,rho_c,(d_(c,x))_(x in U_c))                       (LCL1)
```

from `every-boolean-predicate-has-a-character-free-finite-type-block`.  Put

```text
K=product_c K_c,       rho=tensor_c rho_c,
q=z_rho=product_c z_(rho_c) in C[K].                   (LCL2)
```

Embed `d_(c,x)` in the `c`-th factor of `K`.  Then every `d_(c,x)` is a
literal group involution commuting with `q`, and its compression is the
corner involution `q d_(c,x)`.  For each fixed context, the joint spectrum
on the common corner is exactly `R_c`; the other tensor factors merely
amplify every allowed atom.  Thus one projection and literal group elements
simultaneously realize all context diagonal algebras.  What is missing is
only equality of two copies of a shared variable.

That equality cannot be supplied by a finite graph of finite groups.  More
generally, let `Pi` be the fundamental group of a finite graph of finite
groups, let `0!=q in C[Pi]` be a projection, and suppose literal group
elements `g_x in Pi` have the following properties:

```text
u_x=q g_x q is a self-adjoint unitary in q C[Pi] q;     (LCL3)

the u_x commute in every context and every forbidden
joint spectral projection is zero.                     (LCL4)
```

Then `(u_x)` is a unital star representation of the BCS algebra in
`q C[Pi] q`.  Since `Pi` is virtually free, it is hyperlinear and its
canonical group trace is Connes embeddable.  The normalized canonical trace
on the nonzero corner `q L(Pi) q`, pulled back along this representation, is
a Connes-embeddable tracial state of the BCS algebra.  Therefore `(LCL3)--
(LCL4)` are impossible for the fixed no-CE-trace BCS.

There is also no hidden compression freedom in `(LCL3)`.  If `u` is a group
unitary and `q u q` is unitary relative to `q`, then

```text
q u^* q u q=q
  implies ((1-q)u q)^*((1-q)u q)=0,
```

so `(1-q)u q=0`.  Applying the same argument to `u^*` gives
`u q=q u`; hence `q u q=q u`.  A single literal compressed marginal must
stabilize the corner exactly.

Consequently tensoring selected predicate types solves the entire local
problem, while ordinary amalgams, HNN edges over finite packet subgroups,
and any other finite Bass--Serre network cannot solve the overlap problem --
even if its stable letters preserve `q` and even though the resulting corner
is allowed to be infinite-dimensional.  The first successful compatibility
cell must leave the class of finite graphs of finite groups (or use a
genuinely non-Bass--Serre two-cell), and block escape must use a multi-piece
corner unitary rather than a single compressed group element.

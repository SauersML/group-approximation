---
rg: 2
id: fd-mark-stability-mf-invisibility-proof
kind: route
title: Lift a corona homomorphism coordinatewise and repair the approximants at the mark alone
target: fd-mark-stability-forces-mf-invisibility
requires: []
---

Let `Theta : G -> U(Q)` be an arbitrary homomorphism into the unitary group
of the norm matrix corona `Q=prod_n M_(d_n)/sum_n M_(d_n)`.

**Unitary coordinate lifts exist.**  Pick any lift `x=(x_n)` in
`prod_n M_(d_n)` of `Theta(g)`.  Then `x^*x-1` and `xx^*-1` lie in
`sum_n M_(d_n)`, so `||x_n^*x_n-1||->0`; for all large `n` the matrix `x_n`
is invertible, and its polar part `phi_n(g)=x_n|x_n|^(-1)` is unitary with
`||phi_n(g)-x_n||->0`.  Set `phi_n(g)=1` at the finitely many remaining
coordinates.  This uses only that each `M_(d_n)` is a finite matrix algebra,
where an invertible has a unitary polar part.

**The lifts are a point-norm asymptotic homomorphism.**  Because `Theta` is
a homomorphism, `phi_n(g)phi_n(h)-phi_n(gh)` represents `0` in `Q` for each
fixed pair, i.e. lies in `sum_n M_(d_n)`, i.e.

```text
||phi_n(g)phi_n(h)-phi_n(gh)||_op -> 0     for each fixed g,h in G.
```

No uniformity over `G` is claimed, and by `corona-defect-is-not-uniform`
none is available; the hypothesis `(MRK1)` is stated pointwise for exactly
this reason.

**Repair at the mark.**  fd-stability at `w` supplies genuine homomorphisms
`pi_n : G -> U(d_n)` with `||phi_n(w)-pi_n(w)||_op -> 0`.  Each `pi_n` is a
finite-dimensional unitary representation of `G`, and `w in Rad_fd(G)`, so

```text
pi_n(w)=I     for every n.
```

Therefore `||phi_n(w)-I||_op -> 0`, which says precisely that
`(phi_n(w))_n - (I)_n` lies in `sum_n M_(d_n)`, i.e. `Theta(w)=1`.

Since `Theta` was arbitrary, `w in Rad_MF(G)`, which is `(MRK2)`.

For the globalization: `Rad_MF(G)` is an intersection of kernels of
homomorphisms out of `G`, hence a normal subgroup, so it contains the normal
closure of any subset it contains.  If a set of such marks normally
generates `G`, then `Rad_MF(G)=G` and every corona homomorphism of `G` is
trivial.

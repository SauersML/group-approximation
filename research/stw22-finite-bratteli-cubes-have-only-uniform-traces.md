---
rg: 2
id: stw22-finite-bratteli-cubes-have-only-uniform-traces
kind: claim
title: Closed subfields of finite Bratteli cubes have only uniform traces
distinct_from:
  stw22-matrix-to-hyperfinite-field-trace-continuity: that theorem treats one convergent sequence and one hyperfinite endpoint; the present theorem takes arbitrary closed subfields of finite tensor products, producing every finite Cantor--Bendixson height and rooted patterns of matrix and hyperfinite fibres.
  stw22-derived-set-gap-trace-reduction: that theorem has one constant hyperfinite fibre over a scattered base and uses convex Hilbert-space extension; the present theorem has genuinely changing matrix and hyperfinite fibres and constructs the required derived-subset lift by conditional expectations along the Bratteli coordinates.
artifacts:
  - research/artifacts/stw22-finite-bratteli-cube-audit-2026-08-30.md
---

Fix `d>=1`.  For each `1<=i<=d`, let `U_i` be an
infinite-dimensional UHF algebra with unique trace and choose a dense
increasing chain of unital full matrix subalgebras

```text
F_(i,1) subset F_(i,2) subset ... subset U_i.
```

Put `X_i={infinity,1,2,...}` and form the changing-fibre algebra

```text
A_i={ (a_infinity,a_1,a_2,...):
        a_infinity in U_i, a_n in F_(i,n),
        ||a_n-a_infinity|| -> 0 }.
```

For the minimal tensor product

```text
A=A_1 tensor ... tensor A_d,       X=X_1 x ... x X_d,
```

let `K` be any nonempty closed subset of `X` and let

```text
A_K=A/closure(C_0(X\K)A).
```

Then the following hold.

1. `A_K` is separable, unital, and nuclear, and its extreme trace boundary
   is canonically `K`.
2. Write `R_i=pi_(tau_i)(U_i)''`, `R=bar-tensor_i R_i`, and

   ```text
   N_(i,n)=F_(i,n),       N_(i,infinity)=R_i,
   N_x=bar-tensor_i N_(i,x_i) subset R.
   ```

   The uniform tracial completion of `A_K` is canonically

   ```text
   M_K={a:K -> R: sup_x ||a(x)||<infinity,
                  a(x) in N_x for every x,
                  x |-> a(x) is continuous in ||.||_2}.
   ```
3. Every tracial state on `M_K` is uniquely

   ```text
   a |-> integral_K tau_x(a(x)) dmu(x)
   ```

   for a probability measure `mu` on `K`.  In particular every trace on
   `M_K` is continuous for the uniform `2`-norm.

Thus STW Problem XXII has a positive answer for this changing-fibre class
and every one of its closed subfields.  Every such `K` is scattered of
Cantor--Bendixson height at most `d+1`; closed subsets allow finite rooted
Bratteli patterns rather than only the rectangular cube.  A fibre is a full
matrix factor when every coordinate of `x` is finite and is a hyperfinite `II_1` factor
as soon as one coordinate is `infinity`.  For the full field `K=X` and
`d>=2`, there are infinitely many hyperfinite fibres arranged on
intersecting boundary faces; this field is neither a trivial factor field
nor locally trivial.

For the full field `K=X`, the top norm/`2`-norm fibre gap is nonzero.
Indeed, if `x_top=(infinity,...,infinity)`, rank-one projections supported at the
diagonal points `(n,...,n)` have norm one and `2`-norm tending to zero.
Nevertheless every fibre gap is bounded-trace-free.

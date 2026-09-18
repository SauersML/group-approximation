---
rg: 2
id: hyperlinear-base-amenable-telescope-proof
kind: route
title: Telescope one canonical base microstate through the joint Følner blocks
target: hyperlinear-base-amenable-cells-retain-coefficients
requires:
  - amenable-multi-compressors-have-a-joint-hs-telescope
---

Write `b=sum_(g in K) c_g g` with `K` finite.  Fix `n`, put `F=F_n`, and let

```text
W_F = union_(p in F) alpha_p( (W u K u K^(-1))^(3) ),
```

where `X^(3)` is the set of products of at most three elements of `X`.
`W_F` is finite.  By hyperlinearity choose `rho:Lambda->U(d)` with
`rho(1)=1`, `||rho(uv)-rho(u)rho(v)||_2<delta` for `u,v in W_F`, and
`|tr rho(u)|<delta` for `u in W_F\{1}`.

Define, exactly as in `(AMC2)` of
`amenable-multi-compressors-have-a-joint-hs-telescope` but with the map
`rho` in place of a representation,

```text
H_F = direct_sum_(p in F) C^d,     Pi(g)|_(H_p) = rho(alpha_p(g)).
```

**Covariance.**  Use the block permutations `T_s:H_(ps)->H_p` of `(AMC3)`.
On a good block (`p,ps in F`)

```text
T_s Pi(g) T_s^(-1)|_(H_p) = rho(alpha_(ps)(g)) = rho(alpha_p(alpha_s(g))) = Pi(alpha_s(g))|_(H_p),
```

an identity of maps, so it needs no multiplicativity of `rho`.  This gives
`(HBA4)` and the bound `2 sqrt(|Fs triangle F|/|F|)`.  The semigroup
relation clause is word-for-word the block-permutation argument of
`(AMC3)`--`(AMC5)`, which never looks inside the blocks.

**Approximate homomorphism and canonical trace.**  For `g,h in W` each
block has `rho(alpha_p(gh))=rho(alpha_p(g)alpha_p(h))`, within `delta` of
`rho(alpha_p g)rho(alpha_p h)` since both factors lie in `W_F`; average the
squares over blocks.  For `g in W\{1}`, injectivity of `alpha_p` gives
`alpha_p(g)!=1`, so `|tr Pi(g)|<delta`.

**Coefficient norm.**  On block `p`,

```text
||rho(alpha_p b)||_2^2 = sum_(g,h in K) conj(c_h) c_g tr( rho(alpha_p h)^* rho(alpha_p g) ).
```

Since `rho(u^(-1))rho(u)` is within `delta` of `rho(1)=1` and `rho` is
unitary-valued, `||rho(u)^*-rho(u^(-1))||_2<delta`; then
`rho(u^(-1))rho(v)` is within `delta` of `rho(u^(-1)v)`.  With
`u=alpha_p h`, `v=alpha_p g` all these elements lie in `W_F`, and
`u^(-1)v=alpha_p(h^(-1)g)` is `1` iff `g=h`.  Hence each trace term is within
`3 delta` of `delta_(g,h)`, and
`| ||rho(alpha_p b)||_2^2 - sum|c_g|^2 | <= 3 delta (sum|c_g|)^2`.
Averaging over blocks and letting `delta->0`, `n->infinity` gives `(HBA3)`,
because `||lambda_Lambda(b)||_2^2=sum|c_g|^2`.  Packet traces and the
bounded-type specialization are the cases `b=z` and `b=z(1-a)` together with
`(RAT11)` of `rf-amenable-two-cell-retains-coefficient` (a regular
representation computation which uses no residual finiteness).

**Contrapositive.**  If `Lambda` were hyperlinear, the microstates above have
cell energy `E_cell->0` while `||b(U)||_2->||lambda(b)||_2>0`, contradicting
the payment inequality.

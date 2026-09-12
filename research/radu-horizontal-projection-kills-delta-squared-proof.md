---
rg: 2
id: radu-horizontal-projection-kills-delta-squared-proof
kind: route
title: Read the vertical letters as transducers on reduced horizontal words
target: radu-horizontal-projection-kills-delta-squared
requires:
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
---

**Square rule.**  Every relator of `(RE1)` has the form `h v h' v'` with `h,h'`
horizontal and `v,v'` vertical.  Rewriting as `h v = v' h'` gives the
complete table

```text
(a,x)->(x,a)  (a,y)->(y,a)  (a,z)->(z,b)  (b,x)->(x,b)  (b,y)->(y,c)
(b,z)->(z,a)  (c,x)->(z,c)  (c,y)->(y,b)  (c,z)->(x,c)
```

(pairs `(h,v) -> (v',h')`).  For instance `cxcz = 1` gives `cx = zc` and
`zc = cx`.  Inverting involutive words, `v h = h' v'`.

**Action on cosets.**  `Gamma_R` acts simply transitively on vertices of the
product, so the vertices of `T_h` are the cosets `gV` and `V` is the root
stabilizer.  The cosets are represented by reduced words `h_1...h_n` in
`a,b,c`.  For a vertical letter `v`, repeated use of `v h = h' v'` gives
`v h_1...h_n = h_1'...h_n' v_n`, so `v` sends the coset of `h_1...h_n` to the
coset of the output word.

**Transducers.**  From the table:

* `y` reading `a,b,c` outputs `a,c,b` and stays `y`.
* `x` reading `a,b` outputs `a,b` and stays `x`; reading `c` it outputs `c`
  and becomes `z`.
* `z` reading `a,b` outputs `b,a` and stays `z`; reading `c` it outputs `c`
  and becomes `x`.

So `x` leaves the letters before the first `c`, between the second and
third, and so on, unchanged, and swaps `a,b` in the complementary blocks;
`z` does the reverse.  Neither moves any letter `c`, so the block
decomposition is preserved.  Hence `x` and `z` commute on `T_h`, their
product is the global substitution `a <-> b`, and `(xz)^2` fixes every
vertex.

**Kernel.**  `Lambda_v` is a normal subgroup contained in `V`, since elements
fixing the root lie in `V`.  Each of `x,y,z` moves some vertex (for example
`x` sends `cba` to `cab`), so `Lambda_v` contains no conjugate of a
generator.  By the Kurosh subgroup theorem every finite subgroup of
`V = C_2*C_2*C_2` is conjugate into a factor, so `Lambda_v` is torsion-free,
hence free.  It contains `(xz)^4`; it contains `u = y(xz)^2y` by normality;
and it contains `[u, xz] = u (xz) u^(-1) (xz)^(-1)`, because `u` and
`(xz)u^(-1)(xz)^(-1)` both lie in `Lambda_v`.

**Pullbacks.**  An action pulled back from `Gamma_R/Lambda_v` makes `(xz)^2`
act as the identity, and so the mark as well.

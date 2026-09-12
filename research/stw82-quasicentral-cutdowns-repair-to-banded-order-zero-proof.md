---
rg: 2
id: stw82-quasicentral-cutdowns-repair-to-banded-order-zero-proof
kind: route
title: Repair approximately order-zero cutdowns using projectivity of the finite-dimensional cone
target: stw82-quasicentral-cutdowns-repair-to-banded-order-zero
requires: []
---

We first record the uniform stability input.  For every finite-dimensional
`F` and `rho>0`, there is `eta>0` such that any cpc map
`theta:F->C` satisfying

```text
norm(theta(x)theta(y))<eta                              (S5)
```

for all orthogonal positive contractions `x,y in F` is within `rho`, in
map norm, of a cpc order-zero map `theta':F->C`.

Here is a proof, including uniformity in the target `C`.  If this failed,
there would be targets `C_n` and cpc maps `theta_n` with orthogonality
defect tending to zero but staying `rho` away from every order-zero map.
The induced map

```text
theta:F -> product_n C_n / directSum_n C_n
```

is cpc order zero.  By the Winter--Zacharias correspondence it gives a
*-homomorphism from `C_0((0,1]) tensor F` to the quotient.  The cone over a
finite-dimensional C*-algebra is projective, so this homomorphism lifts to
the product.  Its coordinate maps are cpc order zero and converge in map
norm to `theta_n` because `F` is finite dimensional, a contradiction.

Now define the cpc cutdown maps

```text
theta_i(x)=c_i^(1/2) phi(x) c_i^(1/2) in B_i.          (S6)
```

If `x,y` are orthogonal positive contractions, order zero of `phi` gives

```text
theta_i(x)theta_i(y)
 =c_i^(1/2) phi(x)[c_i,phi(y)]c_i^(1/2),               (S7)
```

so its norm is at most the first commutator bound in (S2).  Apply (S5)
inside the target algebra `B_i`, with `rho` smaller than
`epsilon/(2m)`, to obtain cpc order-zero maps `psi_i:F->B_i` close to
`theta_i`.

The partition of unity controls reconstruction.  For `x` in the unit ball,

```text
sum_i theta_i(x)-phi(x)
 =sum_i c_i^(1/2)[phi(x),c_i^(1/2)],                   (S8)
```

whose norm is at most `m delta`.  Choose `delta` below both the stability
threshold in (S5) and `epsilon/(2m)`.  Adding the perturbation errors proves
(S4).

Finally, `c_i c_j=0` implies `B_i B_j=0`.  Maps assigned the same class
therefore have orthogonal ranges, and their direct sum is cpc order zero.
For `c_i=g_i(h)`, quasicentrality passes from `h` to each of the finitely
many continuous functions `g_i` and `g_i^(1/2)`, giving (S2).

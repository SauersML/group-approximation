---
rg: 2
id: two-site-rigidity-of-lamp-witnesses-proof
kind: route
title: Conjugate the marked pair onto the error pair and telescope in the square root
target: two-site-rigidity-of-lamp-witnesses
requires: []
---

## Direct proof

Throughout, `ell` is a bi-invariant length on a group `K`: conjugation
invariant, symmetric, vanishing only at `1`.

**1.**  Two-transitivity of the conjugation action on `Y_n` gives, for any
`p!=q` and `p'!=q'`, an element `k` with `k p = p'` and `k q = q'` as sites.
Conjugation permutes the lamps accordingly, so
`k (a_p a_q) k^(-1) = a_(p') a_(q')`, and invariance gives
`ell_n(a_p a_q)=ell_n(a_(p') a_(q'))`.  Call the common value `lambda_n`.
The mark has `sigma(w)=a_(j(o)) a_(j(h Gamma))`, which is a two-site element
once `j(o) != j(h Gamma)` — and if those two sites coincided then
`sigma(w)=1`, contradicting the separation.  So `lambda_n >= c`.

**2.**  Write `e = sigma(g) sigma(a_u) sigma(g)^(-1) sigma(a_(gu))^(-1)`.
Because the `sigma(g)` normalize the lamp subgroup by permuting sites,
`sigma(g)sigma(a_u)sigma(g)^(-1) = a_(pi_n(g) j_n(u))`, so
`e = a_(pi_n(g) j_n(u)) a_(j_n(gu))`.  If the two sites differ, `e` is a
two-site element and `ell_n(e)=lambda_n >= c`.

On the other hand `g a_u g^(-1) a_(gu)^(-1) = 1` holds in `W`, so `e` is the
discrepancy of `sigma` along a word of length four in the window.  Now
`sqrt(ell_n)` satisfies the triangle inequality: conditional negative
definiteness of the kernel `ell_n(a^(-1)b)` means it equals
`||f(a)-f(b)||^2` for some map `f` into a Hilbert space, so
`sqrt(ell_n)(a^(-1)b)=||f(a)-f(b)||` is a pseudometric, and it is bi-invariant
because `ell_n` is.  Telescoping the four multiplications, each contributing
at most `sqrt(delta)`, gives `sqrt(ell_n(e)) <= 3 sqrt(delta)`, hence
`ell_n(e) <= 9 delta -> 0`.  This contradicts `ell_n(e) >= c` unless the two
sites agree, which is the asserted exact covariance.

**3.**  `w = a_o (g a_o g^(-1))` for any `g` with `g o = h Gamma`.  Applying
the triangle inequality for `sqrt(ell_n)` to this product and using
conjugation invariance,

```text
sqrt(ell_n(sigma(w))) <= 2 sqrt(ell_n(sigma(a_o))) + O(sqrt(delta)),
```

so `ell_n(sigma(a_o)) >= c/4` in the limit.  All lamps are conjugate, so this
holds for every lamp.

## Scope

Step 1 and step 3 need only bi-invariance and, for step 3, the conditional
negative definiteness that makes `sqrt(ell_n)` a pseudometric — so step 3
applies to exactly the witnesses the Hilbert embeddability question is about,
while a general weakly sofic witness has the triangle inequality outright and
gets the better constant `c/2`.

What is *not* proved here: that no such witness exists.  Exact covariance on
a finite window is cheap to arrange on its own — take the site set to be the
window and extend the partial permutations arbitrarily — so step 2 is a
constraint on the shape of a witness, not a refutation.

**The refutation route I flagged here is now closed, negatively.**  It was
that the character-gap corollary of `hilbert-embeddable-length-hyperlinearity`
might apply to the acting part, which by step 2 carries the whole defect, and
force an exact local homomorphism.  `lamp-character-orbit-separation` settles
it: splitting the cone by whether an irreducible is inflated from the acting
quotient, Clifford theory bounds the non-inflated part from below **only on
the lamp subgroup**, and step 2 says there is no defect there.  So the two
theorems are consistent and their combination yields no obstruction at all.
The gap I recorded — that `K_n` has no character gap because inflated
characters die on the lamps — turned out to be a decomposition rather than a
defect in the argument, and the argument still does not close.  Recording
that as a negative rather than leaving the direction looking promising is the
point of this paragraph.

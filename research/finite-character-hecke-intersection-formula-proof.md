---
rg: 2
id: finite-character-hecke-intersection-formula-proof
kind: proof
title: Proof of the finite character Hecke intersection formula
proves:
  - finite-character-hecke-intersection-formula
---

Expand

```text
x=e_(H,chi) g e_(K,psi)
 =1/(|H||K|) sum_(h,k)
   overline(chi(h) psi(k)) h g k.                     (FCP1)
```

Two pairs `(h,k)` and `(h',k')` contribute to the same group basis vector
exactly when

```text
a=h'^(-1)h=g k' k^(-1) g^(-1) in I.                  (FCP2)
```

Every fibre of the map `(h,k)|->h g k` therefore has cardinality `|I|`.
After fixing one pair in a fibre, the coefficient sum over that fibre is a
unit-modulus scalar times

```text
1/(|H||K|) sum_(a in I)
  overline(chi(a)) psi(g^(-1) a g).                   (FCP3)
```

The sum in `(FCP3)` is the character sum of
`overline(chi|I) psi^g|I`.  It is `|I|` when the two restricted characters
agree and zero otherwise.  There are `|H||K|/|I|` fibres.  Since the group
basis is orthonormal in `ell^2(G)`, this gives

```text
||x||_2^2
 =(|H||K|/|I|) (|I|/(|H||K|))^2
 =|I|/(|H||K|)                                        (FCP4)
```

in the compatible case, and zero in the incompatible case.  This proves
`(FCH3)--(FCH4)`.

For `(FCH5)`, unitary invariance of the canonical `2`-norm gives

```text
||p_i p_j||_2
 =||e_(H_i,chi_i) (g_i^(-1)g_j) e_(H_j,chi_j)||_2.    (FCP5)
```

Apply `(FCH3)` to `H_i,H_j,g_i^(-1)g_j`.  Conjugating the resulting
intersection by `g_i` gives `(FCH6)`, and its order is unchanged, giving
`(FCH7)`.

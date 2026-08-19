# Character rigidity cannot simply be spliced into embedding universality

Date: 2026-08-13

## 1. The tempting argument

Chifan--Drimbe--Ioana prove that, for every separable tracial von Neumann
algebra `M` and every acylindrically hyperbolic group `H`, there are a
`II_1` factor `Q` containing `M` and a homomorphism

```text
pi:H -> U(Q),                 pi(H)''=Q.               (CRE1)
```

Take `M` non-Connes-embeddable.  Then `Q` is non-Connes-embeddable.  If the
factor character

```text
chi(g)=tau_Q(pi(g))                                     (CRE2)
```

were forced to be the regular character of the image group `pi(H)`, one
would obtain

```text
Q isomorphic L(pi(H)),                                  (CRE3)
```

and `pi(H)` would be a nonhyperlinear group.

## 2. Exact missing hypothesis

The needed property is not Kazhdan property `(T)`, absence of scalar
characters, or acylindrical hyperbolicity.  It is the following strong
factor-character rigidity:

> every diffuse finite-factor representation of `H` is regular after
> passing to its image.

Higher-rank arithmetic lattices have results of this kind.  They are not
acylindrically hyperbolic, and Chifan--Drimbe--Ioana explicitly contrast
their rigidity with `(CRE1)`.

Conversely, `(CRE1)` shows why choosing a property-`(T)` hyperbolic source
does not help.  The source may be a cocompact lattice in `Sp(n,1)`, hence
hyperbolic, property `(T)`, and sofic.  Nevertheless it has representations
whose generated factors contain an arbitrary prescribed non-CE algebra.
Thus property `(T)` plus negative curvature does not force `(CRE2)` to be
regular.

The phrase “no nontrivial characters” in the wreath-like group input of the
construction concerns one-dimensional group characters.  It must not be
read as classification of normalized positive-definite conjugation-invariant
functions.

## 3. Quotients do not repair the argument

The construction obtains the relevant wreath-like group as a quotient of
the chosen acylindrically hyperbolic source.  Writing `K=ker(pi)` only gives

```text
Lambda=H/K <= U(Q),             Lambda''=Q.             (CRE4)
```

It does not identify the character `(CRE2)` with the canonical regular
character of `Lambda`.  Hyperlinearity is not known to pass to arbitrary
quotients, and a non-CE character on a hyperlinear group is possible.  In
fact a free group can generate any separable finite factor through a
nonregular character while its regular group factor remains CE.

Therefore neither `(CRE1)` nor property `(T)` of `Q` proves that `Lambda`
is nonhyperlinear.  Turning `(CRE4)` into `(CRE3)` is precisely the open
group-factor embedding-universality problem identified in Remark 1.1 of the
source.

## 4. Valid conditional endpoint

The following implication is sound and isolates what a future theorem would
need:

```text
embedding-universal representation of H
+ factor-character rigidity of H (after kernels)
    ==> an explicit nonhyperlinear quotient of H.       (CRE5)
```

No currently cited group satisfies both inputs.  The character-rigidity
splice is therefore not a shortcut around the Clifford, Iwahori, or Atlas
matrix gates.

## Reference

- I. Chifan, D. Drimbe, and A. Ioana, *Embedding universality for II1
  factors with property (T)*, arXiv:2205.07442, especially Theorem A(1),
  Remark 1.1, and the comparison following Remark 1.2.

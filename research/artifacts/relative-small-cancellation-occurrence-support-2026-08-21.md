# Relative small-cancellation support for the occurrence compiler

**Audit date:** 2026-08-21

This audit checked primary free-product, relative-small-cancellation, and
Higman-embedding sources for the exact separation properties needed by
`colored-cayley-pauli-incidence-separation`.

## 1. Free-product and graphical Greendlinger theorems

Steenbock, *Rips--Segev torsion-free groups without the unique product
property*, arXiv:1307.0981v2, contains the needed primary pins:

- Definition of free-product `C_*'(lambda)` at pp. 4--5;
- Theorem 1.1, the free-product Greendlinger estimate for `lambda<=1/6`;
- Lemma 1.3, its graphical `Gr_*'(lambda)` version using maximal regions;
- Theorem 1.7, injection of each graphical component into the quotient Cayley
  graph under `Gr_*'(1/6)`; and
- the observation before the graphical definitions that a finite labeled graph
  over a finitely presented free product gives a finite presentation.

These results justify `relative-c-sixth-protects-sign-double-cosets`.  A sign
collision has a freely reduced relative boundary of at most four syllables.
If every new relator has at least eight syllables, the Greendlinger exterior arc
has more than four and cannot fit on that boundary.

The graphical theorem additionally preserves the named vertices inside each
graphical component.  It does **not**, without extra hypotheses, say that all
cosets of arbitrary finitely generated subgroups remain distinct.  For the
occurrence compiler, equality groups should therefore be actual free factors,
peripheral groups, or have their entire selected coset orbits included in the
embedded graphical component.

## 2. Osin's protected relative ball

Osin, *Small cancellations over relatively hyperbolic groups and embedding
theorems*, arXiv:math/0411039v3, Lemma 5.1, is the cleanest general theorem.
For every relative radius `N`, its small-cancellation constants can be chosen
so that the quotient remains relatively hyperbolic and the natural quotient
map is injective on the entire relative ball of radius `N`.

Taking `H_X,H_Z` as peripherals and `N=4` preserves all sign boundaries

```text
h_X p_0 h_Z p_1^(-1).
```

This works for infinitely many choices of `h_X,h_Z` at once because each
peripheral element is one relative letter.  It is stronger and cleaner than a
separate double-coset theorem.

For a finite game instance, any finite list of cloud-coset boundaries can also
be protected by increasing `N`.  For one group containing unbounded instances,
a fixed-radius theorem does not automatically preserve arbitrarily long
address differences.  One needs graphical-component injection, a graded
construction scheduling larger protected radii, or fresh occurrence factors.

## 3. Short Pauli rectangles remain the construction gate

Neither theorem makes the natural length-at-most-eight Pauli rectangles satisfy
a long-relator hypothesis automatically.  They must satisfy the exact relative
piece condition at the threshold, or be absorbed into a base address group
which already:

1. contains the bounded rectangle templates;
2. is relatively hyperbolic with respect to the equality groups, or is itself
   a suitable free product/graphical base; and
3. separates the two sign double cosets.

After that base is constructed, Osin protects the relative radius-four sign
boundary while sufficiently long new occurrence relators are added.  Thus the
precise theorem-level input is available; the remaining task is the base
address packet/threshold labeling plus global cloud-coset bookkeeping.

## 4. Finite presentation after the separated source

Wagner, *Malnormal Subgroups of Finitely Presented Groups*,
arXiv:2404.00841v2 (revised 2026-03-04), Theorem A proves that every finitely
generated recursively presented group has a quasi-isometric malnormal
congruence-extension embedding into a finitely presented group.  Corollary B
handles countable groups equipped with a computable length function.

Injectivity alone preserves all equalities/non-equalities among source
elements, hence the selected source cosets and double cosets.  Quasi-isometry
controls source word lengths, while the finite offset set already gives a
fixed target word-length bound even without it.  CEP supplies the stronger
normal-closure identity

```text
G intersect <<S>>_A = <<S>>_G.
```

Therefore Higman embedding is not the remaining separation obstruction.  It
can be postponed until after a recursively presented occurrence address group
with the desired coset data has been built.

## Exact usable hypothesis package

A terminal construction may cite the audited theorems if it produces:

```text
(B1) a recursively presented base B with peripheral/free-factor H_X,H_Z;
(B2) short Pauli rectangle templates already valid in B, or a threshold
     Gr_*'(1/6) labeling in which every length-eight rectangle is unique;
(B3) H_X P_0 H_Z disjoint from H_X P_1 H_Z in B;
(B4) all later relators satisfy either free-product Gr_*'(1/6) with
     relative length >=8, or Osin's C(epsilon,mu,lambda,c,rho) condition
     for protected radius 4;
(B5) selected cloud cosets are protected componentwise or by a scheduled
     protected-radius construction; and
(B6) the finite local edge types use one fixed finite offset set.
```

Then sign separation survives the small-cancellation quotient, and Wagner's
embedding yields a finitely presented ambient group without losing any of the
separation data.


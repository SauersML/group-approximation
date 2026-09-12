---
rg: 2
title: Factorization property under nonsplit amenable extensions (2026-09-05)
kind: artifact
---

# Statement

If `1 -> N -> G -> Q -> 1` is an extension of countable discrete groups,
`Q` is amenable and `N` has Kirchberg's factorization property, then `G`
has Kirchberg's factorization property.  Proof:
`factorization-amenable-extension-induced-compression-proof`.

# Relation to what the graph already had

- `factorization-property-closed-under-amenable-semidirect-products`
  covers split extensions through crossed products and
  `amenable-crossed-products-preserve-invariant-amenable-traces`.
  A nonsplit extension gives no action of `Q` on `C*(N)`; its full group
  algebra is a twisted crossed product, so that route does not apply
  verbatim.  The proof here avoids crossed products entirely: it induces a
  Stinespring dilation of a Hilbert--Schmidt model of `N` up to `G` and
  compresses to a Folner window times the Stinespring subspace.
- `literal-fp-via-folner-rf-core` is the case `G = K rtimes Z` with the
  dilation replaced by a finite quotient representation of a finitely
  generated subgroup of `K`.  The general proof reduces to it there.
- Wiersma (arXiv:1709.09272, Corollary 5.5) proves residual permanence:
  if `G/N_alpha` has the property for a decreasing family with trivial
  intersection, so does `G`.  Extensions are a different permanence and are
  not treated there.

# Checks on the proof

- Induced representation: with a section `s` and `p : G -> Q`, the formula
  `pi(g)(delta_x tensor xi) = delta_(p(g)x) tensor sigma(s(p(g)x)^(-1) g s(x)) xi`
  is a unitary representation because `s(p(g)x)^(-1) g s(x)` lies in `N` and
  satisfies the cocycle identity `c(gg',x) = c(g,p(g')x) c(g',x)`.
- Compression by `P = 1_Phi tensor VV^*` is u.c.p. on `C*(G)`; its
  `(y,x)`-block for `g` is `V^* sigma(c(g,x)) V = psi(c(g,x))` when
  `y = p(g)x in Phi` and zero otherwise.
- The Hilbert--Schmidt defect estimate uses that distinct `x` give distinct
  block columns, so squared norms add, and that a block of operator norm at
  most one has normalized Hilbert--Schmidt norm at most one in its own
  `k`-dimensional block; the normalization by `|Phi| k` and the block count
  give `eps^2 + 2 eps`.
- Trace: only fixed points `p(g)x = x` contribute to the diagonal, which
  forces `g in N`; there `c(g,x)` is a conjugate of `g`, nontrivial exactly
  when `g` is.

# What it does and does not give

- It enlarges the class of groups on which STW Problem X(1) fails: every
  amenable extension of the literal group `E`, and every factorization
  overgroup of `E`, has an amenable non-quasidiagonal canonical trace,
  because the canonical trace restricts to the canonical trace of `E` and
  quasidiagonality of traces passes to subalgebras.
- It says nothing about exact algebras
  (`amenable-traces-on-exact-cstar-algebras-are-quasidiagonal`): all these
  groups are nonamenable, so their full group algebras are nonexact.
- The quasidiagonal analogue fails (`Z`-extensions can destroy
  quasidiagonality of the canonical trace), so the permanence is specific to
  Hilbert--Schmidt models.

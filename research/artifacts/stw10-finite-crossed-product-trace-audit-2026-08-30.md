# STW Problem X(1): finite crossed-product trace audit (2026-08-30)

## Graph audit and novelty

The complete local X(1) graph was searched before adding this theorem.  The
existing nodes cover directed dense unions, locally liftable quotients, GNS
kernels under exactness, ideal-supported central components, and reduction
to factorial witnesses.  None treats crossed products or covariance of the
matrix trace models.

The closest result elsewhere in the graph is
`stw08-finite-group-crossed-products-preserve-af-embeddability`.  That result
starts with an embedding `A->E` into an AF algebra and transports the entire
crossed product into `M_|G|(E)`; its traced statement requires that the trace
already extend across this AF embedding.  The new X(1) theorem starts only
with the u.c.p. models for a specified trace.  It constructs new u.c.p.
models entry by entry, so it applies even when no AF embedding of `A` is
given.

The Rokhlin corollary is a full property theorem, not merely a statement
about one chosen trace: approximate Rokhlin projections force every trace
on the crossed product to vanish on all nonidentity Fourier coefficients.
It therefore gives a new unconditional class-building operation for Problem
X(1).

## Finite-dimensional estimate audit

For `m=|G|`, apply a trace model `phi:A->M_k` entrywise to the regular
covariant matrix representation in `M_m(A)`.  An entry of a product defect is
a sum of at most `m` defects of `phi`.  In operator norm one may use

```text
||X|| <= m max_(r,s) ||X_(r,s)||.
```

For normalized Hilbert--Schmidt norms, the exact identity is

```text
||X||_(2,M_m(M_k))^2
  = (1/m) sum_(r,s) ||X_(r,s)||_(2,M_k)^2.
```

Thus the constants depend only on the fixed finite group and tend to zero
with the original defect.  The normalized matrix trace is zero on a
nonidentity permutation diagonal and is the average of the orbit traces on
the identity coefficient.  Invariance of `tau` is precisely what identifies
this average with `tau`.

## Boundaries

For a general finite action, the theorem covers canonical traces
`tau compose E`; arbitrary crossed-product traces can have nonzero Fourier
coefficients.  The Rokhlin hypothesis is used only to eliminate those
coefficients.  The proof does not infer operator-norm multiplicativity from
Hilbert--Schmidt multiplicativity: the same construction is run separately
in the two norms.  The universal X(1) root remains open.

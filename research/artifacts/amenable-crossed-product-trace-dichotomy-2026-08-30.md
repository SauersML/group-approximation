# Amenable crossed-product trace dichotomy (2026-08-30)

## Results

This note records three consequences of one finite-propagation calculation.

1. If a countable amenable group acts on a separable unital C-star algebra and
   preserves an amenable trace, the induced canonical trace on the maximal
   crossed product is amenable.
2. Kirchberg's factorization property is therefore closed under arbitrary
   semidirect products by countable amenable groups.
3. Quasidiagonality does not share this permanence: the literal split group
   `E=K rtimes Z` has locally residually finite `K`; the canonical trace of
   `C*_(max)(K)` is quasidiagonal, whereas the induced canonical trace of
   `C*_(max)(E)` is amenable and nonquasidiagonal.

No Lean code is asserted or added.

## Finite-propagation ucp calculation

Let `B=A rtimes_(alpha,max) Q`, let `q_r` be the regular quotient, and
compress its regular covariant representation to a finite Folner set
`F subset Q`:

```text
kappa_F(x)=P_F Lambda(q_r(x))P_F in M_F(A).
```

For a fixed finite Fourier packet, the matrices have propagation in one
finite set `S subset Q`.  If `phi:A->M_k` is a u.c.p. amenable-trace model
on every entry and entry-product, put
`Phi=(id tensor phi)kappa_F`.  There are two multiplicative errors.

### Boundary error

```text
kappa_F(xy)-kappa_F(x)kappa_F(y)
 =P_F Lambda(x)(1-P_F)Lambda(y)P_F.
```

After `id tensor phi`, this has at most
`|partial_S F|k`-dimensional initial support and operator norm at most
`||x||||y||`.  Consequently

```text
||boundary||_(2,tr)
 <=||x||||y|| sqrt(|partial_S F|/|F|).
```

Amenability of `Q` makes this tend to zero.

### Entrywise ucp error

Every output block is a bounded-length sum of terms
`phi(ab)-phi(a)phi(b)`, and finite propagation leaves only `O(|F|)`
nonzero blocks.  With normalized traces on both matrix levels, an entrywise
defect at most `delta` therefore gives total defect at most `C delta`,
where `C` depends only on the fixed Fourier packet, not on `F` or `k`.
Choose the amenable-trace model after `F), with `delta` arbitrarily small.

The diagonal of a nonidentity Fourier shift is zero.  The identity coefficient
has diagonal entries `alpha_(s^-1)(a)`; invariance of the trace makes their
average equal to `tau(a)`.  This proves the crossed-product theorem.

## Locally residual finite base

For a finite group-ring packet in a locally residually finite group `K`,
put all coefficients in one finitely generated residually finite subgroup
`H`.  A finite quotient of `H` separates the packet.  Its regular
representation gives the exact trace and exact multiplication there.
The full group C-star inclusion `C*_(max)(H) subset C*_(max)(K)` is
isometric by induced representations, so Arveson extends that finite quotient
representation to one u.c.p. map on `C*_(max)(K)`.  The resulting
operator-norm trace models prove quasidiagonality of the canonical trace.

## Red-team audit

- **Full versus reduced:** regular compression is precomposed with the
  full-to-reduced quotient.  The canonical expectation and induced trace
  factor through it.  No equality is used in the general theorem.
- **Matrix amplification:** `id_(M_F) tensor phi` is u.c.p.; entrywise
  nonmultiplicativity is counted explicitly rather than silently discarded.
- **Rank after a cp map:** the boundary estimate uses zero block columns, which
  entrywise application preserves.  It does not claim that an arbitrary cp
  map preserves rank.
- **Order of choices:** first choose a Folner set, then include every resulting
  orbit coefficient in the finite packet for `phi).  Dimensions may depend
  on `F); normalized boundary rank cancels the matrix size.
- **Why QD does not follow:** the boundary has small normalized rank, not small
  operator norm.  The literal group proves this distinction is realized.
- **Why LEF alone is not used:** the base theorem assumes every finitely
  generated subgroup is residually finite, so its partial finite model is an
  honest representation of a full subgroup C-star algebra and Arveson
  extension applies.  Bare LEF does not supply that positivity domain.

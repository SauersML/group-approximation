---
rg: 2
id: serre-class-from-unimodular-integral-realizability
kind: claim
title: Expected root spectral measures of unimodular integer-weighted networks obey every Serre inequality
distinct_from:
  integral-group-ring-spectra-are-integral-limits: that asks for integer-matrix approximation of group-ring spectra; this asks for the Serre inequalities themselves on the larger class of unimodular integral networks, with no approximation in the statement
  determinant-conjecture-iff-serre-class-spectra: that is the exact reformulation at one group; this is a network-level statement that implies it for every group at once
  root-measures-of-integer-matrices-can-violate-serre: that shows the inequalities fail at a single root without averaging; this asks whether unimodular averaging restores them in general
---

**OPEN.**

**Statement.** Let `(Gr, o)` be a unimodular random rooted network with integer
symmetric edge weights `w(u,v) in Z`, loops allowed, and weighted degree
`sum_v |w(u,v)| <= D` almost surely. Let `A` be its weighted adjacency operator
and `mu = E[ <E_A(.) delta_o, delta_o> ]` the expected root spectral measure.
Then for every nonzero `Q in Z[x]`,

```text
integral_(Q != 0) log|Q| d mu >= 0.
```

It is enough to treat `Q = x`. The operator `Q(A)` is again the adjacency
operator of a unimodular integral network on the same vertex set: its weights
are integer path sums of length at most `deg Q`, and its degree is bounded.

**Why it implies the determinant conjecture.** Take a self-adjoint
`A in M_n(Z[G])`.
- **Network:** vertex set `G x {1..n}`, weights `w((g,i),(h,j)) = A_ij(g^-1 h)`, root `(e,i)` with `i` uniform.
- **Hypotheses:** left translation by `G` preserves the network and acts transitively on each fibre, so the root distribution is unimodular by mass transport. The weights are integers and the degree is bounded.
- **Measure:** the expected root measure is `mu_A / n`.
With `determinant-conjecture-iff-serre-class-spectra` this gives `det >= 1` for
every group (route `determinant-via-unimodular-integral-networks`).

**Known case: sofic networks.** Suppose `(Gr, o)` is a Benjamini–Schramm limit of
finite integral networks with degree at most `D`.
- **Finite approximants:** the uniformly rooted root measure is the normalized trace
  measure of a finite symmetric integer matrix of norm at most `D`.
- **Limit:** `integral-spectral-limits-satisfy-serre-inequalities` then gives the
  claim at the limit.

## Attempts

- **Measure-level invariants of trace measures (dead).** Any invariant preserved by
  positive-preserving integer combinations admits `mu = 23 nu - sigma`
  (`euler-integral-measure-violates-serre-inequality`,
  `necklace-realizable-measures-can-violate-serre`). Such an invariant would prove too much.
- **Integral realizability at finitely many roots (dead).**
  `root-measures-of-integer-matrices-can-violate-serre`: integer coordinates
  without unimodular averaging admit Serre violators, even atomless ones. So a
  proof must use unimodularity, not only integrality.
- **Integral approximation (covers sofic networks only).**
  - It gives the sofic case above.
  - It cannot be the whole proof, because nonsofic unimodular networks exist:
    Bowen–Chapman–Lubotzky–Vidick refuted the Aldous–Lyons conjecture.
  - Cayley networks of nonsofic groups, such as `openai-leavitt-unit-nonsofic`, are not limits of finite networks.
- **Mass transport plus integrality, with no approximation (not built).**
  - The finite proof uses that the product of the nonzero eigenvalues of an integer matrix is a nonzero integer, i.e. a global determinant. An infinite network has no such object.
  - A replacement would be a Fuglede–Kadison-type determinant for unimodular networks, defined through the mass transport principle, together with a Jensen-type or multiplicativity formula that forces integrality.
  - Neither is established. Nothing on main produces an integer from a unimodular network without a finite approximant.

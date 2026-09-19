---
rg: 2
id: generator-column-pauli-test-globalizes-but-does-not-pin-sites
kind: claim
title: The generator-column Pauli test globally exactifies but does not pin the tape sites
distinct_from:
  lin-code-space-pauli-test-has-only-logarithmic-weyl-rank: that refutes Lin's literal proper-code-space sampler; this analyzes de la Salle's correct spanning generator-column sampler and records both its uniform positive theorem and its remaining gauge.
  clifford-hs-defect-becomes-adversarial-site-noise: that asks for a sparse bad-site interpretation compatible with a named computation tape; this proves dimension-free global Clifford exactification but shows why it does not imply that stronger fixed-frame conclusion.
---

Let `H=F_2^n`.  Let `mu,nu` be the uniform measures on the generator-matrix
columns supplied by two binary codes of dimension `n`, and suppose their
inverse spectral-gap constants are at most `c,c'`.  De la Salle's game
(arXiv:2204.07084v2, Proposition 3.8 and Corollary 3.9 in the source labels)
has the following dimension-independent consequence.  If a synchronous
strategy has loss `epsilon`, its full Pauli representations satisfy

```text
E_(a in H, chi in H^) ||U_X(a)U_Z(chi)
  -(-1)^(a.chi)U_Z(chi)U_X(a)||_2^2
    <= 1320 c c' epsilon.                                  (GCP1)
```

The central-extension average Gowers--Hatami theorem then gives an
amplified corner `P`, a partial isometry `w`, and exact Weyl representations
`U'_X,U'_Z` such that, for `W=X,Z`,

```text
E_g ||U_W(g)-w^*U'_W(g)w||_2^2
    < 39,600,000 c c' epsilon,                             (GCP2)

tau(P) <= 1+21,120 c c' epsilon.                          (GCP3)
```

Fourier Parseval converts `(GCP2)` to the same bound for the sum of squared
distances of the corresponding PVM atoms.  Exact Weyl representation theory
identifies the corrected corner with

```text
M_(2^n)(C) tensor N,                                      (GCP4)
```

with the two distinguished PVMs equal to the standard all-`X` and all-`Z`
Pauli PVMs tensored with `1_N`.  For asymptotically good explicit codes,
`c,c'=O(1)`, so `(GCP1)--(GCP4)` are genuinely uniform in `n`.  This is the
simultaneous coherent tensor-factor recovery that a collection of separate
site tests does not provide.

It is not a fixed-tape adversarial-site theorem.  Even at zero loss, choose
the ideal `n`-qubit packet and put

```text
Q=Z_1 Z_2 ... Z_n,             W_theta=exp(i theta Q),
X_i^(theta)=W_theta X_i W_theta^*,       Z_i^(theta)=Z_i.  (GCP5)
```

For `theta=pi/8`, all Weyl laws and every generator-column test are still
exact, because `(GCP5)` is one simultaneous unitary conjugacy.  Relative to
the original named site frame,

```text
X_i^(theta)=cos(2 theta)X_i+i sin(2 theta)QX_i,            (GCP6)
```

so every `X_i` contains a nonzero Pauli string supported on all `n` sites.
No proper bad-site set `B` makes the original observables outside `B` equal
to the original site Paulis: `(GCP6)` differs from `X_i` for every
`i notin B`, forcing `B={1,...,n}`.  Nevertheless the global correction
`W_theta^*` repairs all sites at once.  Thus a perfect test can have dense
named-site error and zero global-factor error.

The same escape can mix the packet with its multiplicity reservoir.  In
`M_(2^n) tensor N`, replace `Q` in `(GCP5)` by `Q tensor h` for a
self-adjoint involution `h in N`.  The test is again perfect, while the
recovered Pauli factor is conjugated into an arbitrary position relative to
external computation or mark words.  De la Salle's `w` is allowed to absorb
that conjugacy and therefore gives no estimate for those external words.

For a code of length `K=Theta(n)`, the corrected support has `K` columns, so
its random column index uses `O(log n)` bits and the resulting game has
`O(KK')=O(n^2)` question contexts.  This algorithmic succinctness is not an
ordinary finite-presentation compiler.  A group presentation cannot average
over a random index; it needs fixed words which expose the selected columns
and their incidence.  Neither explicit Justesen encoding in `poly(n)` time
nor `(GCP1)` bounds the relator area of those words.  A self-similar compiler
would still have to realize the generator-column sampler and pin the global
correction `w` to the computation words with dimension-independent cost.
That is exactly `uniform-halting-pauli-word-oracle`, not a consequence of
the code spectral gap.

There are now two exact continuations.  `single-anchor-cannot-pin-pauli-gauge`
shows that one external observable cannot remove the conjugacy and that the
full generator-column family gives the optimal Pauli-word adjoint anchor.
`lin-introspection-payload-is-global-gauge-covariant` shows that Lin's native
payload does not need such an anchor at all: every computation PVM is carried
through the same extraction isometry.  On that route the sole surviving gate
is bounded-area group-word realization of the sampled dense columns.

The complete product of the two column measures is essential to the stated
Poincare transfer.  `sparse-generator-column-sampling-has-bilinear-kernel`
shows that every sub-sampler with fewer than `n^2` pairs misses a nonzero
bilinear twist.  The corresponding exact Weyl packet has zero sampled defect
but full-product defect at least `1/(cc')`.  Hence an expander or high-girth
bipartite graph cannot simply replace the complete product in `(GCP1)`.
Sparse dimension soundness, if available, must instead prove growing affine
minimum completion rank for the sampled signs.

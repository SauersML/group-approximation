---
rg: 2
id: sl3-one-over-forty-two-packet-is-external-or-folded
kind: claim
title: A finite one-over-forty-two SL3 packet atom is either external or folded
distinct_from:
  sl3-raw-weyl-rectangle-pins-only-equal-rank-corners: That isolates trace 1/42 as the rank needed for raw loop transfer; this proves that the natural finite-character and finite-quotient sources of that rank cannot supply a nonfolded covariant shell atom.
  finite-character-idempotents-have-exact-hnn-transport: That transports a matched character idempotent after adjoining finite-edge stable letters; this rules out an internal arithmetic idempotent of the required trace and shows why an exact external quotient packet folds.
  balanced-raw-lamp-orbit-cannot-approximate-shell-pvm: That gives a rank-capacity floor for the unrefined lamp orbit; this audits the proposed 21-fold refinement intended to remove that floor.
---

# A finite one-over-forty-two SL3 packet atom is external or folded

Put

```text
C=SL_3(Z),       A=SL_3(Z[1/2]).                        (OFP1)
```

There are two natural ways to seek the trace-`1/42` source isolated by
`sl3-raw-weyl-rectangle-pins-only-equal-rank-corners`.  Neither gives a
nonfolded arithmetic shell.

## No internal finite-subgroup character atom

Every finite subgroup `K` of `A` has order at most `24`.  Indeed
`A<SL_3(Q)`, and every finite rational matrix group preserves a full lattice:
take the sum of the finitely many lattices `k Z^3`, clear denominators, and
choose a lattice basis.  Thus `K` is rationally conjugate into `SL_3(Z)`.
Tahara's classification of finite subgroups of `GL_3(Z)` proves directly
that every finite subgroup of `SL_3(Z)` has order at most `24` (and every
finite subgroup of `GL_3(Z)` has order at most `48`): [K. Tahara, *On the
finite subgroups of GL(3,Z)*](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/99F7848C6566702A760E6B99B69F3948/S002776300001415Xa.pdf/on-the-finite-subgroups-of-gl-3-z.pdf).

For every projection `q in C[K]`, its canonical trace is

```text
tau(q)=rank(lambda_K(q))/|K|.                            (OFP2)
```

Thus `tau(q)=1/42` would imply `42 rank(lambda_K(q))=|K|`, impossible when
`|K|<=24`.  In particular no finite-subgroup character idempotent inside the
arithmetic group algebra has the required canonical trace.

## Every exact finite quotient packet folds

Let `sigma:A->U(H_f)` be any exact finite-dimensional representation and let
`e` be a nonzero projection intended as the base atom of an `A/C`-covariant
shell.  Well-defined coset covariance requires

```text
e in sigma(C)'.                                         (OFP3)
```

Finite-dimensional co-density of `(C,A)` gives

```text
sigma(C)'=sigma(A)',                                    (OFP4)
```

so `e` is fixed by all of `A`.  Hence

```text
sigma(a)e sigma(a)^*=e                 (a in A),         (OFP5)
```

and its purported 42 shell translates all coincide.  If they are also
required to be pairwise orthogonal, `(OFP5)` forces `e=0`.

This applies directly to the proposed refinement of a trace-half raw lamp by
a 21-atom packet.  If one packet atom `e` of trace `1/21` is `C`-fixed, then

```text
E=P tensor e,             tau(E)=1/42                   (OFP6)
```

does preserve the raw lamp's `C`-centrality, but `(OFP5)` makes the packet
factor invariant under the denominator as well.  Every refined raw branch
lies under the same support `1 tensor e`; 42 orthogonal trace-`1/42`
branches would have total trace `1` inside a projection of trace `1/21`, an
impossibility.

If instead the 21 atoms are permuted nontrivially by `C`, a chosen atom is
not `C`-fixed.  Then it does not define a projection indexed by `A/C`, and
the section correction in `a_i=b_i d_i` changes the atom by
`sigma(d_i)e sigma(d_i)^*`.  The commutator term needed in
`raw-denominator-incidence-kills-off-diagonal-shell-orbit` is no longer zero.
Thus the moving packet has abandoned exactly the raw-section interface it was
meant to rank-match.

The conclusion is scoped to exact finite packet authentication.  It does not
exclude a uniformly noncorrectable approximate `A`-packet; doing so is the
original normalized-Hilbert--Schmidt outlier problem.  It proves that a
finite character idempotent, a 21-atom finite quotient refinement, or any
other exact finite `A/C` system of imprimitivity cannot close the rank seam.
The remaining source must be genuinely matrix-coordinate and approximate,
or must come from a non-finite packet whose denominator orbit is not folded
by `(OFP4)`.

The first non-finite replacement is now fenced too.
`fixed-spherical-polynomials-have-no-42nd-projection` proves
that the reduced spherical spectrum is connected, so every fixed Hecke
polynomial which is a projection in the regular model is constant.  A
trace-`1/42` Borel cutoff exists only at unbounded spectral depth, where a
new uniform section-defect estimate is required.

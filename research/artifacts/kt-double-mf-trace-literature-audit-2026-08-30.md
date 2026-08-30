# Kun--Thom double: MF-trace and reduced-amalgam literature audit

Date: 2026-08-30

This audit fixes the exact status of
`reduced-amalgam-canonical-trace-is-mf` for the binary Kun--Thom pair.

## 1. The target is an MF trace, not a quasidiagonal trace

Shulman's MF-trace definition, as used in *Sections and cones*, consists of
pointwise bounded maps to matrices which are asymptotically linear,
self-adjoint, and multiplicative in operator norm, and whose normalized
traces converge to the prescribed trace.  The maps are not required to be
u.c.p., exactly linear, or asymptotically isometric.

The previous target text required u.c.p. maps and asymptotic isometry.  The
u.c.p. clause is quasidiagonal-trace strength; the isometry clause also makes
the ambient full C-star algebra MF.  Both were unintended strengthenings and
have been removed.  The five limits in `(RAT1)` now match the formal
`ShulmanTrace.IsMFTrace` predicate in
`GroupApproximation/Analysis/ShulmanTraceClasses.lean`.

## 2. Shulman v2 is trace-blind

Primary source:

- Tatiana Shulman, *The MF property for amalgamated free products*,
  [arXiv:2603.13564v2](https://arxiv.org/abs/2603.13564v2), especially
  Theorem 10 and the current v2 table of contents.

Theorem 10 says that `A *_C A` is MF when `A` is separable MF.  Current v2
contains no section on MF traces and no theorem selecting hyperlinear traces
on a symmetric amalgam.  Search engines still expose the withdrawn v1 text,
whose abstract and Corollary 15 asserted an HS-stable trace upgrade; the
version-specific v2 abstract, HTML, PDF, and source omit that assertion.
Consequently the unversioned search result must not be cited.

For the Kun--Thom double, the theorem is applied to the auxiliary profinite
regular completion `A=C*(rho(G))`.  It makes the auxiliary amalgam MF and
embeds the abstract group double there.  It does not prove that the full
group algebra `C*(G *_Gamma G)` is MF, and it does not select the canonical
group trace.

## 3. Gao gives the exact Hilbert--Schmidt boundary

Primary source:

- Weichen Gao, with an appendix by Marius Junge and David Gao,
  *Relative Embeddability of von Neumann Algebras and Amalgamated Free
  Products*, [arXiv:2012.07940v3](https://arxiv.org/abs/2012.07940v3),
  Appendix Theorem 7.1.

For finite von Neumann algebras `N subset M` and a finite factor `N_1`, the
appendix proves that `RE/N_1` implies embeddability of `M *_N M` into
`(R tensor N_1)^omega`; the converse holds when `M` contains a unitary `u`
with `E_N(u^k)=0` for every nonzero integer `k`.

For the Kun--Thom inclusion `N=L(Gamma) subset M=L(G)`, choose an
infinite-order `A in SL_d(Z)` and `u=lambda((1,A))`.  The projection
`G->SL_d(Z)` is trivial on `Gamma`, so `(1,A)^k` is outside `Gamma` for every
`k!=0`, and therefore `E_N(u^k)=0`.  Taking `N_1=C` yields

```text
G *_Gamma G is hyperlinear
  iff L(Gamma) subset L(G) is relatively embeddable over C.
```

This is an exact equivalence for the fixed candidate.  Gao's introduction
also explicitly records the general non-hyperfinite amalgamation problem as
open.  Brown--Dykema--Jung permanence over a hyperfinite edge does not apply:
`Gamma` is an infinite Kazhdan group and hence nonamenable.

## 4. Relation to reduced MF

For `q=2`, the polynomial subgroup has trivial core in `G`.  The Bass--Serre
action of `D=G *_Gamma G` is therefore faithful, minimal, and
non-elementary, which forces the amenable radical of `D` to be trivial.
The Breuillard--Kalantar--Kennedy--Ozawa theorem then gives a unique tracial
state on `C*_r(D)`, namely the canonical trace.

Every separable unital monotracial MF algebra has its unique trace as an MF
trace: take an MF norm-corona embedding, compose with a matrix ultralimit
trace, and extract an ordinary diagonal subsequence.  Hence

```text
C*_r(D) MF  ==>  canonical trace on C*(D) is MF.
```

The reverse implication is not formal.  An MF-trace model need only make its
GNS kernel trace-null; that ideal may survive in operator norm on
vanishing-rank corners.  Thus the Cairn node is not equivalent to closure of
MF under reduced amalgamated free products.  Reduced MF is one stronger
sufficient certificate; the exact known CE-level reformulation is Gao's
`RE/C` condition above.

## 5. Current strong-convergence boundary

Checked again against the current arXiv abstract pages on 2026-08-30.

Gao--Kunnawalkam Elayavalli--Manzoor--Patchell,
arXiv:2603.24502v5, Corollary 1.2, proves reduced-norm MF for a double
`G *_H G` when `G` is MF and `H` is separable in `G`.  The version remains
v5, dated 12 April 2026.  The Kun--Thom edge has the opposite property: the
strict exterior return belongs to the image of `Gamma` in every finite
quotient of `G`, so `Gamma` is not separable.  The stronger blockwise form of
this failure is `kt-finite-image-relative-edge-models-are-impossible`.

Gao--Kunnawalkam Elayavalli--Mj, arXiv:2607.29571v1, remains at v1, dated
31 July 2026.  Its extension results make exact/equivariant finite-dimensional
base models the input to strong crossed-product assembly.  For the split
Kun--Thom double, `finite-dimensional-nielsen-cocycle-models-kill-mark`
proves that every such exact equivariant model kills one fixed free-radical
generator.  Hence it cannot strongly converge to the reduced regular model.

The surviving operator-norm problem is therefore not an unnamed permanence
gap.  It is the genuinely asymptotic affine Nielsen package isolated in
`kt-strong-nielsen-covariant-microstates`: the actor and covariance laws may
be exact only in the norm corona, never at the finite stages.  No theorem in
either current source supplies those approximate base models for the
nonseparable Kun--Thom action.

## Verdict

The canonical MF-trace and reduced-MF nodes remain genuinely open.  The exact
narrower results banked by this audit are the binary unique-trace theorem,
the generic monotracial-MF trace-selection lemma, the Gao relative-
embeddability equivalence, and the affine Nielsen strong-microstate reduction.
No cited permanence theorem settles the nonamenable, nonseparable Kun--Thom
edge.

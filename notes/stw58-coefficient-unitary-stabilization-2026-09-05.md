# STW LVIII: coefficient-dependent unitary stabilization

Date: 2026-09-05. Working proof notes, with published consequences
separated from unresolved attempts. This is not a new Cairn target.

## An all-degree case from exact divisibility of the unit

**Proposition (prior-art consequence).** Let `B` be a unital separable
simple stably finite pure C*-algebra with a nonempty space `QT(B)`
of normalized lower semicontinuous 2-quasitraces. Suppose that for every integer
`N` there are an integer `n>=max(N,2)` and `g in K0(B)` such that

`n g = [1_B]`.

Then `B` is K-stable: for every `m>=1` and `k>=0`, the canonical
stabilization map

`pi_k U(M_m(B)) -> K_(k+1)(B)`

is an isomorphism. No central matrix embeddings, real-rank-zero
hypothesis, nuclearity, or Z-stability are assumed.

Here and below stable K-theory of matrix algebras is identified by
the standard corner Morita maps, not by tensor amplification.

**Proof.** Lin's simple-pure dichotomy gives `sr(B)=1`, since the
purely infinite alternative is excluded by stable finiteness. Every
nonzero projection corner of `B tensor K` therefore also has stable
rank one. Purity gives strict comparison by normalized quasitraces.

Write `g=[r]-[s]` for projections in finite matrices over `B`. For
every normalized quasitrace `tau`, extended in the usual unnormalized
way to matrices, the displayed divisibility relation gives

`tau(r)-tau(s)=1/n>0`.

Strict comparison gives `s precsim r`; since these are projections,
the comparison is realized by a partial isometry. Its orthogonal
complement in `r` is a projection representing `g`. Denote this
projection by `p_0`. Since `tau(p_0)=1/n<1=tau(1_B)` for every
normalized quasitrace, strict comparison again gives
`p_0 precsim 1_B`. Thus `g` has a representative `p in B`.

The equality `n[p]=[1_B]` initially lies in K0. Stable rank one gives
cancellation of projections, so it is an actual Murray--von Neumann
equivalence between `diag(p,...,p)` (n copies) and `1_B`. Equivalently,
the Hilbert B-module `B` is isomorphic to `(pB)^n`. Taking adjointable
endomorphisms gives a unital algebra isomorphism

`B ~= M_n(pBp)`.

The assumption `QT(B) nonempty` is explicit: positivity of a K0 class
has not been inferred from a vacuous family of inequalities. These
notes do not invoke an unstated quasitrace-existence theorem to remove
that assumption. Equivalently, the proof works under stable rank one,
strict comparison by a nonempty normalized quasitrace space, and the
displayed divisibility of the unit; simplicity and purity are the
stated mechanism supplying the first two regularity properties.

The corner `pBp` has stable rank one. As `n` can be arbitrarily large,
this is precisely Rieffel's *tsr-bounded divisibility* with constant
one, in Definitions 4.1--4.2 of his 1987 paper. Theorem 4.13 proves
the stated canonical all-degree stabilization result. The unitary and
general linear versions agree by polar deformation retraction. QED.

One can avoid treating Theorem 4.13 as a black box. Its mechanism is
as follows. For a fixed finite-dimensional compact parameter space
`X`, the stable rank of `C(X,pBp)` has a bound depending only on
`X`, uniformly over the corners just constructed. Proposition 4.11
obtains such a bound by embedding `X` into a finite torus, bounding
stable rank for each trivial Z-crossed product, and passing to the
restriction quotient. The matrix estimate for connected stable rank,
Theorem 4.7, then gives

`csr(C(X,B)) <= 2`.

Indeed the matrix size `n` can exceed the uniform corner bound. This
holds for every finite-dimensional `X`; no single `n` is required to
work simultaneously for all parameter dimensions. In particular it
holds for every torus. The last-column fibration and Theorem 3.3
therefore make every matrix stabilization map on every homotopy group
an isomorphism. A given stably null coefficient-dependent sphere map
can thus be contracted inside its original unitary group.

The essential point is that `B ~= M_n(pBp)` rewrites **all** entries
of the sphere family and its stable nullhomotopy in an exact matrix
algebra. Its matrix units do not have to commute with those entries.
This is stronger than placing an unrelated finite-dimensional algebra
somewhere inside `B`.

## Why soft divisibility has not supplied the same construction

Almost divisibility supplies `x in Cu(B)` with

`n x <= [1_B] <= (n+1)x`.

It need not supply a compact `x`, an equality `n x=[1_B]`, or a
projection whose corner endomorphisms provide the exact matrix
decomposition above. The distinction is unavoidable even in a model
with known K-stability: the Jiang--Su algebra has
`K0(Z)=Z`, with unit equal to one, so the additional K0 divisibility
hypothesis fails for every `n>=2`.

The Rordam--Winter finite prime dimension-drop theorem does supply a
unital map `Z_(n,n+1) -> B` from the Cu inequalities and stable rank
one. It does not identify `B` with a matrix algebra over a corner.
In particular the off-diagonal coefficient entries of a stable
nullhomotopy cannot be transported through this map by the
endomorphism-algebra argument above. The scalar-family calculation
already recorded in the LXXVI artifact uses only scalar entries, for
which this coefficient issue disappears.

The next substantive step would need a continuously varying
coefficient compression through the noncompact modules representing
`x`, together with an exact unitary repair on their complement. No
such construction has been proved here. Trace-small complements
cannot simply be discarded: their norm can remain one.

## A citation boundary in degree one

Sarkowicz's published *Unitary groups, K-theory, and traces* asserts
that stable rank one implies the canonical isomorphism
`pi_1 U(B) -> K0(B)` (introduction, equation (1.2) and the paragraph
after it; also Section 3), citing Rieffel's 1987 paper. The preprint
*G-kernels and Crossed Modules*, footnote 7, similarly asserts
surjectivity and cites Rieffel's Theorem 3.3.

I inspected all theorem-bearing pages of that original paper. Its
Theorem 2.10 proves the degree-zero K1 statement for stable rank one.
Its Theorem 3.3 instead assumes a **uniform** bound on
`csr(C(T^j,B))` for every `j>=0`; Theorem 4.13 obtains that bound
from tsr-bounded divisibility. Neither displayed theorem directly
states the asserted degree-one consequence of stable rank one alone.

This is a citation-verification gap in this audit, not a claim that
the published degree-one assertion is false. Until an applicable
primary proof or a complete derivation is located, these notes do
not promote it to a new LVIII closure result.

## Primary sources and current-literature check

- H. Lin, *Strict comparison and stable rank one*, J. Funct. Anal.
  289 (2025), 111065, Theorem 3.6:
  https://doi.org/10.1016/j.jfa.2025.111065 .
- M. A. Rieffel, *The homotopy groups of the unitary groups of
  non-commutative tori*, J. Operator Theory 17 (1987), 237--254:
  https://jot.theta.ro/jot/archive/1987-017-002/1987-017-002-005.pdf .
  Relevant original pages: Theorem 2.10 on 243; Theorem 3.3 on 244;
  Definitions 4.1--4.2 on 245; Theorem 4.7 on 246--247;
  Proposition 4.11 on 247--248; Theorem 4.13 on 248.
- P. Sarkowicz, *Unitary groups, K-theory, and traces*, Glasgow
  Math. J. 66 (2024): https://doi.org/10.1017/S0017089523000447 .
- S. Giron Pacheco, M. Izumi, U. Pennig, *G-kernels and Crossed
  Modules*, footnote 7:
  https://api.newton.ac.uk/website/v0/events/preprints/NI24027 .
- A. Seth and E. Vilalta, *Continuous functions over a pure
  C*-algebra*: https://arxiv.org/html/2602.14809v1 . Its introduction
  announces forthcoming work of Evington, Hua, Schafhauser, Seth,
  and White, rather than proving the needed K-stability theorem.
- Hua's current publication list still lists the established
  Z-stable theorem; the present search found no publicly available
  replacement proving the announced pure-algebra theorem:
  https://sites.google.com/view/shanshan-hua/publications .

The exact-divisibility proposition is explicitly a consequence of
published prior art. The general coefficient-dependent LVIII target
is still unresolved by this investigation.

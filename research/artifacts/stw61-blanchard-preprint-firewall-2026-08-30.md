# STW LXI: the 2016 Blanchard preprint is not a verified closure

## Result of the freshness check

STW Problem LXI must remain open as of 30 August 2026.

The current authoritative problem source is Schafhauser--Tikuisis--White,
*Nuclear C\*-algebras: 99 problems*,
[arXiv:2506.10902v2](https://arxiv.org/abs/2506.10902).  Problem LXI asks
whether every unital properly infinite C\*-algebra is `K_1`-injective.  The
April 2026 addendum solves the neighboring KK-uniqueness problem by a route
which the authors explicitly say does not touch LXI.

A title/abstract search produces a superficially decisive older source:

* Etienne Blanchard, *A properly infinite C\*-algebra which is not
  `K_1`-injective*,
  [arXiv:1606.04773v1](https://arxiv.org/abs/1606.04773), submitted
  15 June 2016.

Its abstract and Proposition 2(6) claim that

```text
T_2 *_[C] T_2
```

is a unital properly infinite algebra which is not `K_1`-injective.  If the
argument were valid, it would refute LXI.  It is not safe to import as a
literature solution: the proof of the indispensable non-null-homotopy claim
uses a retraction incompatible with the crossed-product covariance relation.

## Finite-stage qualification

In Proposition 2(5), Step 1, the preprint takes finite-dimensional stages
`A_n` of the gauge-fixed UHF algebra `A`, invokes a finite-stage theorem to
assert that a unitary `w` is not in

```text
U_0(A_n *_[C] C*(Z)),
```

and then concludes that `w` is not in

```text
U_0(A *_[C] C*(Z))
```

"by passage to the limit since all the connecting maps ... are injective."
**Qualification added 5 September 2026:** injectivity of the
C\*-homomorphisms alone does not imply preservation of a unitary class.
However, if the same compatible unitary has been proved non-null at
every stage, its non-nullness in the limit does follow by finite-stage
detection of null-homotopies. The earlier version of this audit was too
broad in declaring Step 1 invalid without checking exactly which
compatible finite-stage classes its cited theorem detects.
An injective star homomorphism need not induce an injection on
`pi_0(U(-))`; a unitary which is not null-homotopic in one stage may become
null-homotopic after an injective embedding into a later stage.  A path in an
inductive limit can only be approximated at a later stage. Proving the
same witness non-null at each later stage suffices; injectivity on
all unstable unitary homotopy classes is not required.

The distinction is concrete.  There is a unital embedding

```text
C(T) -> O_2
```

(embed `C(T)` in the canonical diagonal through a continuous surjection from
the Cantor spectrum onto `T`).  The coordinate unitary is not null-homotopic
in `C(T)`, while its image is null-homotopic in `O_2`: `K_1(O_2)=0` and the
purely infinite simple algebra `O_2` is `K_1`-injective.  Thus even a unital
injective C\*-map can kill the exact invariant used in Step 1.

## Exact covariance defect in Step 2

There is a separate concrete obstruction in Proposition 2(5), Step 2.
It invokes evaluation of the crossed-product implementing unitary at
1 while retaining the coefficient algebra A-double-dot. If U implements
the dilation automorphism alpha-double-dot, covariance says

    U a U* = alpha-double-dot(a).

A retraction fixing the coefficient algebra and sending U to 1 would
force a=alpha-double-dot(a) for every a. But the dilation automorphism
is not the identity: for p=mu_0(1_A),

    alpha-double-dot(p) = mu_0(s_1 s_1*) < mu_0(1_A) = p.

The strict inequality follows from injectivity of mu_0 and the nonzero
complement of s_1s_1*. Evaluation on an independent free group factor
does not erase the crossed-product covariance relation. Thus the
retraction required by Step 2 is unavailable, independently of the
finite-stage issue.

Proposition 2(3) reduces the claimed
counterexample to Proposition 2(5), and Proposition 2(6) invokes (3) and
(5).  Therefore the preprint has not established its advertised
counterexample by the displayed proof.

This audit does **not** assert that the claimed unitary is null-homotopic,
nor that the opposite answer to LXI is true.  It records only that the
preprint does not supply a valid direct-proof route in Cairn.

## Current theorem boundary

The primary sources support the following exact status.

| Statement | Status/source boundary |
| --- | --- |
| Every unital properly infinite C\*-algebra is `K_1`-surjective | Cuntz; recalled immediately before STW Problem LXI |
| Every unital purely infinite simple C\*-algebra is `K_1`-injective | Cuntz; a proper subclass of the LXI hypothesis |
| It suffices to prove `K_1`-injectivity for `O_infinity *_[C] O_infinity` | Blanchard--Rohde--Rordam, Theorem 5.5; recalled by STW |
| The full LXI assertion | Open in STW v2 as of the 30 August 2026 check |
| `T_2 *_[C] T_2` is a counterexample | Claimed in arXiv:1606.04773v1, but the essential non-null-homotopy argument has the gap above |

The reduction source is Etienne Blanchard, Randi Rohde, and Mikael Rordam,
*Properly infinite `C(X)`-algebras and `K_1`-injectivity*, Journal of
Noncommutative Geometry 2 (2008), Theorem 5.5,
[DOI:10.4171/JNCG/21](https://doi.org/10.4171/JNCG/21).

## Repository consequence

Do not add a refuter to `stw99-problem-lxi-properly-infinite-k1-injective`
from arXiv:1606.04773.  Keep the root open and retain the
`O_infinity * O_infinity` reduction as its certified finite target.  The
preprint is useful only as a false-positive firewall until its
non-null-homotopy argument is repaired, including the covariance
obstruction above.

# STW LXII: the KK-uniqueness problem is solved (2026-08-30)

## Verdict

Gabor Szabo's 2026 preprint [*The uniqueness theorem for Kasparov
theory*](https://arxiv.org/abs/2601.23029) gives an affirmative answer to
STW Problem LXII in its full stated generality.  If `A` is separable, `B` is
sigma-unital and stable, and two absorbing representations

```text
phi, psi : A -> M(B)
```

form a Cuntz pair, then their class vanishes in `KK(A,B)` if and only if the
representations are strongly asymptotically unitarily equivalent.  Thus the
implementing path can be chosen in the minimal unitization `1+B` and can
start at the identity.

The source and theorem statements were checked on 2026-08-30.  This is an
arXiv preprint (arXiv:2601.23029, submitted 2026-01-30), not a
journal-final citation.

## Exact source match

Szabo formulates the non-equivariant statement as Question A in the
introduction and says that the first main goal of the paper is to answer it
affirmatively.  The abstract states the equivalence directly.  The proof is
carried by two numbered results.

1. Corollary 2.9: for a separable `A`, a sigma-unital stable `B`, and an
   absorbing representation `phi:A->M(B)`, the Paschke relative commutant

   ```text
   Q(B) intersect bar(phi)(A)'
   ```

   is `K_1`-injective.  The same holds in the weakly nuclear/nuclearly
   absorbing variant.
2. Theorem 4.6: the generalized equivariant `KK` class of an anchored Cuntz
   pair of absorbing cocycle representations vanishes exactly when the pair
   is strongly asymptotically unitarily equivalent.  Specializing to the
   trivial group gives the ordinary `KK`-uniqueness theorem.

The proof mechanism matches the formulation of STW LXII.  Absorption first
provides an asymptotic implementing path in `M(B)`.  Paschke duality
identifies the vanishing Cuntz-pair class with the zero `K_1` class of the
initial implementing unitary in the relative commutant.  Corollary 2.9 makes
that unitary homotopic to the identity, and the homotopy is concatenated with
the asymptotic path.  The resulting path lies in `U(1+B)`, starts at `1`, and
asymptotically conjugates the two representations.

Schafhauser--Tikuisis--White,
[*Nuclear C-star algebras: 99 problems*](https://arxiv.org/abs/2506.10902v2),
Addendum 17.1, independently records that Szabo's January 2026 paper gives a
positive answer to Problem LXII.

## Hypothesis audit

| STW LXII datum | Szabo result |
| --- | --- |
| `A` separable | Corollary 2.9 / trivial-group case of Theorem 4.6 |
| `B` sigma-unital and stable | Corollary 2.9 / strongly stable trivial action |
| `phi,psi` absorbing | Question A and Theorem 4.6 |
| `phi(a)-psi(a) in B` | the Cuntz-pair hypothesis |
| `[phi,psi]=0 in KK(A,B)` | exactly the vanishing hypothesis |
| path in `U(1+B)` beginning at `1` | strong asymptotic unitary equivalence |

No nuclearity, exactness, simplicity, unitality, UCT, or regularity hypothesis
is added.  The paper also proves nuclear, ideal-related, and equivariant
variants, but the Cairn claim below imports only the ordinary statement asked
by STW LXII.

## Boundary

This does **not** solve STW Problem LXI, which asks whether every unital
properly infinite C-star algebra is `K_1`-injective.  Szabo proves
`K_1`-injectivity for the particular Paschke-dual algebras arising from
absorbing representations by exploiting multiplier-algebra structure; both
Szabo and the STW addendum explicitly distinguish that result from the
unrestricted properly infinite question.

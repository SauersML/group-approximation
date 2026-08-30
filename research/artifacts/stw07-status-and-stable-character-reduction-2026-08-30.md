# STW Problem VII: status and stable-character reduction (2026-08-30)

## Primary-literature status

Problem VII remains open.  The screening inputs were:

- Schafhauser--Tikuisis--White, *Nuclear C*-algebras: 99 problems*,
  arXiv:2506.10902v2 (8 May 2026), which states the full separable nuclear
  stably finite problem as open.
- Tikuisis--White--Winter, *Quasidiagonality of nuclear C*-algebras*,
  arXiv:1509.08318, which proves quasidiagonality for faithful traces in the
  UCT class and in particular the simple stably finite UCT case.
- Gabe, *Traceless AF embeddings and unsuspended E-theory*,
  arXiv:1804.08095, whose Theorem C gives, for separable exact traceless
  algebras, equivalence of stable finiteness, quasidiagonality, and
  AF-embeddability.
- Moutzouris, *Extensions of quasidiagonal C*-algebras and controlling the
  K_0-map of embeddings*, arXiv:2112.03224v3, which proves substantial UCT
  extension cases but does not solve arbitrary nuclear extensions.

Searches through 2026-08-30 found no later primary source claiming the full
problem.  The nonnuclear analogue is false by the non-Connes-embeddable
factor mechanism recorded by STW.

## Exact stable-character normal form

The universal problem is equivalent to its apparently narrow subclass of
nonzero unital algebras `E` having a character `chi:E -> C` whose kernel is
a stable essential ideal.  Given any candidate `A`, take

```text
E=(A tensor K)~,
chi:E -> C.                                               (SC0)
```

Then `A` is quasidiagonal if and only if `E` is quasidiagonal.  The delicate
point is stable finiteness of `E`; it is proved in the associated route, not
assumed as a permanence slogan.

This normal form has two consequences for counterexample searches.

1. Complicated nonsplit Busby invariants are not necessary: every negative
   answer has a split scalar-quotient witness.
2. The evident trace `chi` is nonfaithful, so the normal form lies exactly
   beyond the faithful-trace theorem.  Its difficulty is concentrated in
   the stable kernel.

There is a further trace-theoretic sharpening.  A stable algebra has no
nonzero bounded trace, by the orthogonal-copy argument.  Hence the reduced
witness `E` has exactly one tracial state, its nonfaithful quotient character.
On the other hand its stable kernel cannot be traceless: Gabe's theorem
would then make the kernel AF-embeddable and hence make its unitization
quasidiagonal.  Thus any counterexample has a stable kernel supporting a
nontrivial lower-semicontinuous tracial weight, but every such nonzero weight
which detects a finite element is necessarily unbounded.

## Trust boundaries

The reduction uses standard permanence facts only: nuclearity and
separability under stabilization/unitization; quasidiagonality under matrix
amplification, injective inductive limits, C*-subalgebras, and unitization;
and the split exact sequence

```text
0 -> K_0(I) -> K_0(I~) -> Z -> 0.
```

The stable-finiteness argument is written explicitly.  The root remains
open: the reduction supplies no quasidiagonal approximation of an arbitrary
stable kernel.

## Norm-local positive mechanism

Quasidiagonality itself is norm-local.  If every finite subset of a unital
algebra is approximated by a quasidiagonal unital subalgebra, Arveson
extension carries a finite-dimensional approximation of the local algebra
to the ambient algebra.  Product and norm-recovery errors remain controlled
by contractivity.

Combining this with the two strongest solved cases gives a mixed local
positive class.  It is enough that each finite set be approximated by a
subalgebra which is either traceless, or is nuclear, UCT, and has a faithful
trace.  The ambient algebra need not have a faithful trace and the choice of
the two types may vary with the finite set.

This argument applies in particular to injective directed limits.  It does
not apply to arbitrary noninjective connecting maps: images are quotients,
and quasidiagonality is not quotient-permanent.

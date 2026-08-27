---
rg: 2
id: steinberg-hs-stability-equals-nonhyperlinearity
kind: claim
title: The Leavitt--Steinberg fork is an equivalence, not merely a dichotomy
distinct_from:
  leavitt-steinberg-hs-stability-fork: That records two implications, one per branch, and leaves open whether either converse holds; this closes both converses into a single equivalence, which is what makes the stable branch itself a nonhyperlinear group.
  leavitt-steinberg-hs-stable: That is the open branch selection; this says what selecting it would be worth.
  pointwise-hs-stability-from-no-hyperlinear-quotient: That is the general implication for arbitrary groups; this is its specialization to `U`, where quasisimplicity and minimal almost periodicity turn it into an equivalence.
artifacts:
  - notes/NOTEPAD.md
  - notes/NON_MF_TO_HYPERLINEAR_DIFFERENTIAL_AUDIT.md
---

For `L=L_(F_2)(1,2)`, `U=St_5(L)` and `Q=EL_4(L)`, the following are
equivalent.

1. `U` is normalized-HS stable, in the strict same-dimension sense.
2. `U` has no nontrivial hyperlinear quotient.
3. `Q` is nonhyperlinear.

**The statement to be careful about.**  Condition 3 is *not*
interchangeable with "`U` is nonhyperlinear".  Nonhyperlinearity of `U`
forbids only an **injective** homomorphism into a tracial matrix
ultraproduct, while condition 2 forbids every nontrivial one.  These differ
exactly where the unstable branch lives: a nontrivial noninjective
homomorphism has central kernel and makes a proper central quotient of `U`
hyperlinear while leaving `U` itself possibly nonhyperlinear.  Condition 3
is the strong end -- `Q` nonhyperlinear implies `U` nonhyperlinear by
central-quotient permanence, and not conversely -- so the equivalence must
be stated with `Q`.

**Why it matters.**  The fork alone leaves it open whether the stable branch
is a step toward a nonhyperlinear group or is one.  The equivalence settles
that: on the stable branch `Q` is an explicit nonhyperlinear group, and `U`
is another.  There is no intermediate saving to be had, and no route that
proves `leavitt-steinberg-hs-stable` can be cheaper than producing the first
nonhyperlinear group known.  Symmetrically, `U` would be the first infinite
Kazhdan group known to be HS-stable, since every Kazhdan group whose status
is settled is residually finite, hence sofic, hence hyperlinear, hence
unstable by Becker--Lubotzky.

Recorded in prose at `notes/NON_MF_TO_HYPERLINEAR_DIFFERENTIAL_AUDIT.md:78-103`
as `(DHA5)`/`(DHA6)`; this node supplies the converses that turn the two
implications there into one equivalence.

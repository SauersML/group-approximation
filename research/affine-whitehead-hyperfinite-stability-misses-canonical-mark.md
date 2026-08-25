---
rg: 2
id: affine-whitehead-hyperfinite-stability-misses-canonical-mark
kind: claim
title: Hyperfinite HS stability kills the affine Whitehead mark but excludes the canonical profile
distinct_from:
  steinberg-hyperfinite-hs-stable: That is the full binary Leavitt Steinberg cover; this treats the relative affine-Leavitt quotient and propagates its marked collapse through the finite Whitehead--Clifford graft.
  full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark: That proves collapse only in exact finite-dimensional representations; this identifies the largest currently certified class of approximate representations on which the collapse is robust.
  agent-aggregate-escape-kazhdan-root-no-upgrade: That gives a generic counterexample to property-T robustification; this audits every stability input actually available for the affine Whitehead presentation and its Slofstra solution-group host.
  marked-approximate-radical-survives-solution-group-embedding: That transfers an already established approximate radical; this proves that the audited stability theorems do not create the required source radical.
---

**ESTABLISHED, SOURCE-AUDITED 2026-08-24.**  Use the notation

```text
Gamma_A'=St_5(R_A)/<<W^4>>,
Gamma_FWA=D *_(<u>=<W>~=C_4) Gamma_A'
```

from `full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark`.
The strongest normalized-Hilbert--Schmidt stability theorem whose hypotheses
actually contain this construction gives the following marked conclusion:

```text
every hyperfinite asymptotic representation of Gamma_A' kills W,
every hyperfinite asymptotic representation of Gamma_FWA kills J.       (AWH1)
```

Indeed `Gamma_A'` has property `(T)`: `St_5(R_A)` has property `(T)` by
Ershov--Jaikin-Zapirain because `R_A` is a finitely generated unital
associative ring, and property `(T)` passes to the one-relator quotient.
For a von Neumann amenable character of a property-`(T)` group, the factorial
GNS representation is finite-dimensional.  Amenability makes
`pi tensor conjugate(pi)` have almost invariant vectors, property `(T)`
produces an invariant vector, and factoriality upgrades the resulting
finite-dimensional subrepresentation to a finite-dimensional GNS algebra.
Dogon--Vigdorovich, arXiv:2506.20843v2, Definition 6.1 and Theorem 6.2,
therefore show that `Gamma_A'` is hyperfinitely HS-stable.  Correct a
hyperfinite asymptotic representation to exact same-dimensional
representations.  The exact kernel-ideal theorem kills `W` in every such
representation, proving the first row of `(AWH1)`.  Restriction to the
affine vertex preserves hyperfiniteness, and the finite packet and odd rows
then propagate `W=1` to `J=1`, proving the second row.

This positive theorem does not touch the canonical approximation relevant to
hyperlinearity.  The group `Gamma_A'` is infinite and property `(T)`, hence
nonamenable.  Its regular von Neumann algebra is nonamenable.  The same is
true for `Gamma_FWA`, because it contains `Gamma_A'` and the subgroup von
Neumann algebra is an expected subalgebra.  Consequently any canonical
microstate sequence for either group has nonhyperfinite marked limit:

```text
canonical trace microstates, if they exist, are outside (AWH1).          (AWH2)
```

The remaining audited stability mechanisms miss for precise hypotheses.

1. **Strict or flexible normalized-HS stability.**  Neither is known for
   `Gamma_A'`.  Either one would already select the desired branch: canonical
   microstates would correct to exact finite-dimensional representations,
   which kill `W`, contradicting its regular trace.  Becker--Lubotzky's
   property-`(T)` theorem confirms the strict version has exactly this
   strength; it does not prove stability.  Dogon's flexible-stability results
   are conditional criteria and likewise do not establish it for this group.
2. **Hyperfinite/character stability.**  This is exactly `(AWH1)`, and its
   defining hypothesis fails in `(AWH2)`.  Connes embeddability of a limit is
   not amenability or hyperfiniteness of that limit.
3. **Cohomological stability.**  The de
   Chiffre--Glebsky--Lubotzky--Thom theorem uses the unnormalized Frobenius
   norm and its submultiplicativity.  It gives no dimension-uniform theorem
   in normalized HS norm.  Ordinary property `(T)`, robust `(T;FD)`, and
   `(TT)/T` give spectral gap, not perturbation to a representation.
4. **Higher-rank character rigidity.**  The Lavi--Levit theorem assumes a
   commutative Noetherian coefficient ring in stable range.  The relative
   Leavitt ring `R_A` is noncommutative and non-Noetherian: its active corner
   is isomorphic as a right module to two copies of itself, which is
   impossible in a nonzero one-sided Noetherian corner.  Thus this theorem
   cannot classify the nonamenable characters left by `(AWH2)`.  There is now
   also a structural obstruction, not only a source mismatch:
   `affine-whitehead-has-leavitt-quotient-character-face` constructs a
   surjection of `Gamma_A'` onto two ordinary-Leavitt elementary factors.
   Projection to one factor has infinite kernel, and pulling back the regular
   character of its simple central quotient gives an extremal character which
   is neither regular on `Gamma_A'` nor finite dimensional.  Thus the usual
   regular-or-finite-dimensional dichotomy is false for this group.  Even a
   CE-specific strengthening would already have to decide hyperlinearity of
   the ordinary Leavitt quotient.  The broader Lavi--Levit conclusion is
   induction from finite-dimensional data; the quotient-regular character is
   already induced from the trivial representation of its infinite-index
   kernel, so that conclusion would still not imply hyperfiniteness even if
   its ring hypotheses were ignored.
5. **Known normalized-HS stable classes.**  Finite groups, virtually free
   groups, the currently treated amenable/lamplighter families, and chordal
   graph products do not contain this infinite Kazhdan Steinberg quotient.
   Finite-packet rounding applies only to the `D` vertex, not to the affine
   vertex carrying `W`.
6. **Slofstra's solution-group embedding.**  It is an injective fixed-word
   compiler; the theorem supplies neither a retraction nor a perturbative
   equivalence.  Output
   microstates restrict to source microstates, which proves
   `marked-approximate-radical-survives-solution-group-embedding` once source
   collapse is already known.  Arbitrary source microstates need not extend
   to the wagon wheel, stability is not inherited upward by overgroups, and
   property `(T)` is not inherited by an ambient solution group.  The only
   general transfer theorem in Cairn for stability through a group map is
   descent to a **specified retract**; Slofstra's theorem supplies none.
7. **Unnormalized Frobenius-stable universal hosts.**  The
   Fournier-Facio embedding theorem has the wrong metric and cannot be
   substituted for a normalized-HS-stable solution-group host.
8. **Normal subgroups, finite index and relative `(T)`.**  The same Leavitt
   quotient has infinite kernel and infinite image, so `Gamma_A'` fails the
   normal-subgroup property; the quotient persists after removing the finite
   inactive direct factor and already kills the `W^4` correction.  Relative
   `(T)` cannot force a root algebra to be finite dimensional: the canonical
   hyperlinear model of `Z^3 rtimes SL_3(Z)` has diffuse `L(Z^3)` despite
   relative `(T)` of the pair.  These inputs supply spectral gap, not the
   missing nonhyperfinite lifting theorem.

Therefore no established stability theorem currently yields

```text
exact finite-dimensional invisibility of W
        => W is trivial in every normalized-HS asymptotic representation.
                                                                         (AWH3)
```

The missing input is specifically a nonhyperfinite marked correction theorem,
equivalently the affine root kernel-ideal estimate on canonical microstates.
Passing through Slofstra after proving that estimate is lossless; passing
through Slofstra before proving it creates no additional stability.

Proof and source audit:
`affine-whitehead-stability-hypothesis-audit`.

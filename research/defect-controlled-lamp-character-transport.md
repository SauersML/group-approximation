---
rg: 2
id: defect-controlled-lamp-character-transport
kind: claim
title: A defect-controlled character transport decoder for the Tarski lamplighter
artifacts:
  - research/artifacts/atomic-schreier-lamp-collapse-audit-2026-08-26.md
distinct_from:
  multiplicity-return-transducer: that asks a finitely presented group plus a finite transport network to return a Schur--Clifford multiplicity surplus at fixed packet scale, and its difficulty is clause 4, the fixed irreducible size; this asks only that an abelian lamp resolution be decodable with leakage linear in the defect, has no packets, no network and no fixed presentation, and its difficulty is the actor rather than the scale.
  hyperlinear-wreath-model: that asks to CONSTRUCT microstates for the Kun--Thom coset wreath; this asks for a decoding bound valid in every microstate of a different, regular-lamp candidate, and its truth would forbid microstates rather than build them.
  infinite-schreier-pvm-transport-kills-finite-mark: that is the established collapse estimate consuming a covariance bound as input; this is the open hypothesis that supplies such a bound from the relator defect of one specific candidate.
  affine-leavitt-global-active-module-exposure: that asks a finitely presented affine-Leavitt host to expose its last-column module with uniform actor energy, and its actor is a Steinberg group; this asks the same shape of question for the regular lamp module of a Tarski lamplighter, which is not finitely presented, and its difficulty is therefore the actor rather than the presentation.
  property-t-must-upgrade-global-augmentation-rounding: that asks how a Kazhdan semidirect presentation can expose a whole augmentation module with uniform defect; this has no Kazhdan input at all and replaces it with a Kesten gap, which is why the exposure obligation here carries a non-soficity price.
---

Let `A`, `S`, `M`, `Gamma = C_2 wr A`, `w = m_e m_a` and `Omega` be as in
`tarski-lamp-nonconstant-sector-has-amenable-stabilizers`, and let `T` be the
finite generating set `S union {m_e}` of `Gamma`.  For a map
`U : T -> U(d)` write `Def(U)` for its normalized-HS relator defect on a fixed
finite relator window `R` of `Gamma`.

**The hole.**  Produce `delta_0 > 0`, constants `C, C_s` and a decoder, all
independent of `d`, such that every `U` with `Def(U) <= delta_0` admits an
**exact** representation `rho : M -> U(d)` on the same space with

```text
|| rho(m) - U_m ||_2^2 <= C Def(U)   for every m in the window,     (DLT1)
L_s(rho, U_s) <= C_s Def(U)          for every s in S,              (DLT2)
```

`L_s` being the character-transport leakage `(CTL1)` of the joint spectral
resolution of `rho`.

**Where the difficulty is not.**  The analytic half is already established.
By `all-abelian-uniform-hs-rounding-gives-global-pvm` (Akhtiamov--Dogon), a map
on an arbitrary countable abelian group with **uniform all-pairs**
multiplicativity error `epsilon` is `omega(epsilon)`-close to an exact
representation in the same dimension, and for exponent two that representation
has one finite-support joint PVM.  So `(DLT1)` follows from uniform all-pairs
control of the lamps, and no cardinality-dependent diagonalization is needed.

**Where it is.**  Two obligations survive, and both are about the presentation
and the actor, not about linear algebra: exposing the whole lamp module with a
uniform all-pairs error (the input `(AUR1)` that the rounding theorem needs,
which evaluating one word per virtual lamp does not supply, because the van
Kampen areas are unbounded), and `(DLT2)` itself -- the statement that the
actor's failure to permute the decoded character atoms is paid for by relator
energy at a rate that does not degrade with dimension.

Written with the modulus `Def(U)` on the right, and not as "leakage tends to
zero along sufficiently accurate microstates".  The unmodulated form is
vacuously true whenever `Gamma` is not hyperlinear, hence logically equivalent
to the target, and is a restatement rather than a reduction.

## Attempts

- **Mandatory falsification test, and it is sharp.**  By
  `sofic-actor-refutes-lamp-character-transport`, this hole is FALSE for every
  sofic actor `A`.  So any purported proof that does not consume a
  non-soficity input about the specific actor is wrong, and the amenability of
  proper subgroups -- the only hypothesis the mechanism uses -- is available in
  sofic groups too.  Where it dies today: no non-soficity input exists for any
  Tarski monster, and the amenable-stabilizer hypothesis is precisely the
  hypothesis under which the known permanence theorems go the other way.
- **The rounding half is where property (T) actually was.**  In the
  (T)-compression architecture the Kazhdan gap converts almost-invariance into
  invariance for EVERY unitary representation, which is what supplies a bound
  of type `(DLT2)`.  The Kesten constant of
  `kesten-amenable-stabilizer-uniform-gap` constrains only quasi-regular
  representations, so it amplifies an existing atomic resolution and cannot
  produce one.  Replacing (T) in the amplifier therefore leaves this hole
  exactly as hard as it was; deferred until a mechanism for `(DLT2)` exists at
  all.  The same split is visible in the affine-Leavitt lane, where
  `infinite-schreier-pvm-transport-kills-finite-mark` is established and the
  exposure node is the open one.
- **The almost-commuting literature reaches only the abelian half.**  Rounding
  almost-commuting unitaries to commuting ones in normalized HS norm (Glebsky;
  Filonov--Kachkovskiy -- UNVERIFIED in this lane, used only as an attempt
  note) is about the lamps, that is about `(DLT1)`, which
  `all-abelian-uniform-hs-rounding-gives-global-pvm` already settles from a
  uniform hypothesis.  Neither says anything about the conjugation relations,
  and `(DLT2)` is a statement about them.
- **This hole can never be a finite template.**  A Tarski monster is a torsion
  group, so a finitely presented one would be a finitely presented infinite
  torsion group, and Ol'shanskii's construction is by an infinite presentation.
  Hence `Gamma` is not finitely presented and no fixed finite local test has it
  as its solution group.  Any reservoir- or LTC-shaped attack in the sense of
  `multiplicity-return-transducer` has to change the actor first, and this lane
  knows no infinite finitely presented group all of whose proper subgroups are
  amenable.

---
rg: 2
id: de-la-salle-pauli-game-starts-after-the-same-pvm-gate
kind: claim
title: De la Salle's Pauli game starts after the repeated-LDPC same-PVM gate
distinct_from:
  generator-column-pauli-test-globalizes-but-does-not-pin-sites: that records the global Weyl exactification, constants, and external-frame gauge; this audits Theorem 3.11 against the newer repeated-LDPC parity-plus-commutation seam and identifies the primitive answer PVM as the hidden same-basis oracle.
  quadratic-repetition-supports-complete-commutation-overlay: that compiles the exact pairwise commutation table with bounded occurrence; this proves why the approximate compiled table is not an admissible input to Theorem 3.11.
  repeated-good-ldpc-coordinates-give-private-weyl-sampler: that constructs the scalar private sampler and leaves operator rounding open; this checks whether de la Salle supplies that operator rounding and finds that its hypotheses already assume it.
---

Primary-source audit: Mikael de la Salle, *Spectral gap and stability for
groups and non-local games*, arXiv:2204.07084v2 (19 September 2025),
Proposition 3.8, Corollary 3.9, Definition 3.3, and Theorem 3.11.

Theorem 3.11 does give a uniform **joint** Pauli-factor conclusion.  For each
`N` it constructs a synchronous game with `O(N^2)` questions and two
distinguished questions `P^X,P^Z`, each having answer set `F_2^N`.  A strategy
of loss `epsilon` is `O(epsilon)`-close, in the flexible sense of Definition
3.3, to one on

```text
M_(2^N)(C) tensor N,                                    (DSP1)
```

where the distinguished answer PVMs are the standard all-X and all-Z Pauli
PVMs tensored with `1`.  The closeness permits an amplification projection
and a partial isometry with `O(epsilon)` missing/excess trace; it is not a
strict same-dimension rounding theorem.

But the theorem assumes the repeated-LDPC same-PVM conclusion at its input.
Indeed, a `2^N`-answer PVM `(P_chi)_(chi in F_2^N)` is equivalent by Fourier
transform to an **exact** representation

```text
U(a)=sum_chi (-1)^(a dot chi)P_chi,
U(a+b)=U(a)U(b)                                           (DSP2)
```

of `F_2^N`.  Proposition 3.8 begins with the two exact representations
coming from the primitive PVMs `P^X,P^Z`.  Its two good binary codes are used
only to choose column measures with constant inverse spectral-gap constants.
They do not test or round a contextual family of local parity PVMs into
`(DSP2)`.  Corollary 2.5 globalizes the sampled mixed Weyl energy only because
`(DSP2)` already holds on both sides.

This pinpoints the answer-alphabet issue.  Exponential presentation size is
not forced at **zero defect**: one `F_2^N` PVM can be encoded by `N` commuting
involutions.  Moreover,
`quadratic-repetition-supports-complete-commutation-overlay` copies each
coordinate `Theta(N)` times, connects copies by bounded-degree equality
graphs, and assigns one copy to every logical pair.  This gives an
`O(N^2)`-size, bounded-occurrence, perfect-completeness abstract relator
encoding of the isolated exact PVM semantics.  Sign-safe placement together
with the mixed X/Z words remains a separate compiler condition.

The obstruction is quantitative.  A near-representation of that compiled
presentation supplies only approximate copy agreement, approximate LDPC
parities, and small average pair-commutator energy.  It supplies no PVM and
hence no exact homomorphism `(DSP2)` to which Proposition 3.8 or Corollary 2.5
can be applied.  Replacing the replicated coordinates by one primitive PVM
is exactly `same-basis-rounding-interface-for-sparse-weyl-sampler` (in its
new repeated-LDPC form).  Invoking Theorem 3.11 before proving that replacement
is circular.

The circularity is substantive rather than a missing constant:
`sparse-clifford-cycles-refute-average-commutator-rounding` gives reflection
tuples with complete-pair commutator energy tending to zero but constant
distance from every commuting tuple.  Thus the complete commutation overlay
alone cannot manufacture the primitive PVM.  Any successful use of Theorem
3.11 here must first prove a joint estimate using the replicated LDPC parity
constraints together with the overlay.

There is a second bounded-occurrence mismatch in the literal game.  The
single questions `P^X,P^Z` each carry fixed positive probability and expose
one common exponential answer PVM to all `O(N^2)` auxiliary contexts.  After
Fourier compression this is a high-degree common oracle.  Splitting it into
bounded-degree coordinate occurrences and synchronizing the copies is
precisely the agreement/rounding operation above; the game theorem treats
that synchronization as free because a synchronous strategy assigns one PVM
to each question.

Therefore Theorem 3.11 is reusable **after** same-basis authentication: it
then supplies dimension-independent mixed Weyl globalization and a flexible
Pauli corner.  It does not prove the presently needed joint
LDPC-parity-plus-commutation rounding, cannot be inserted upstream of that
gate, and does not by itself give a same-Hilbert group-relator compiler.

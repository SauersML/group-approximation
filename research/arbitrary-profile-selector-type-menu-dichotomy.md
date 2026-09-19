---
rg: 2
id: arbitrary-profile-selector-type-menu-dichotomy
kind: claim
title: Arbitrary-profile selector overlap is either root-valued or pointwise type-fixed
distinct_from:
  binary-native-selector-atom-hecke-dichotomy: that computes a canonical-trace subgroup-intersection coefficient for one chosen character; this gives the exact representation-level normalizer formula and audits every marked character type without regular multiplicities.
  binary-leavitt-arbitrary-profile-native-cross-gram: that must authenticate the two actual unequal-scale selector occurrences and their mixed Pauli gauges; this isolates the complete finite-type test after such literal occurrence words have been supplied.
  canonical-cross-gram-does-not-close-arbitrary-mf-active-profile: that records the canonical-versus-arbitrary quantifier mismatch; this proves the sharp pointwise replacement and gives an exact finite countertype whenever it fails.
---

**ESTABLISHED ARBITRARY-PROFILE TYPE-MENU AUDIT.**  Let

```text
H=<z> times Z~=(C_2)^10
```

be the marked character packet from
`binary-native-selector-atom-hecke-dichotomy`, and let `u` normalize `H`
and centralize `z`.  For a character `chi` of `H`, write

```text
e_chi=|H|^(-1) sum_(h in H) chi(h)h,
chi^u(h)=chi(u^(-1)hu).                                (ATM1)
```

In **every** finite-dimensional unitary representation `pi`, with any
normalized trace profile, one has

```text
pi(e_chi)pi(u)pi(e_chi)pi(u)^*pi(e_chi)
 = pi(e_chi),                 if chi^u=chi,
 = 0,                         if chi^u!=chi.           (ATM2)
```

Consequently, if literal selector occurrences have the form

```text
S_i=pi(g_i)pi(e_chi),          u=g_1^(-1)g_2,          (ATM3)
```

then their cross-Gram square has trace exactly `tr(pi(e_chi))` or zero
according to the two cases in `(ATM2)`.  There is no Plancherel weight and
no canonical group trace in this formula.  Amplification and arbitrary
multiplicity reservoirs do not alter it.

The all-profile criterion is therefore pointwise.  The normalizer-atom
method gives a positive estimate on every marked type which can carry mass
only if

```text
chi^u=chi for every chi with chi(z)=-1.                (ATM4)
```

For this elementary abelian packet, `(ATM4)` is equivalent to `u`
centralizing `H` pointwise.  If the induced automorphism of `H` is
nontrivial, there is a marked character `chi` moved by `u`, and the finite
semidirect-product orbit representation on that character orbit has

```text
pi(z)=-1,       tr(pi(e_chi))>0,
tr(S_1^*S_2S_2^*S_1)=0.                               (ATM5)
```

Thus a regular-character average cannot be repaired for one relative word
by taking the minimum over types: the minimum is literally zero as soon as
that normalizer action moves one marked type.  This is a local packet
countermodel, not automatically a representation of the full
binary-Leavitt Steinberg group.  Any full-presentation proof using that
nontrivial action must exhibit an additional occurrence relation which
excludes the orbit type or quantitatively charges its mass.

## Finite-menu criterion

A genuine menu of relative words is stronger than one word.  Let
`u_1,...,u_m` normalize `H` and centralize `z`, and put

```text
X_-={chi:chi(z)=-1},
F_j={chi in X_-:chi^(u_j)=chi}.                         (ATM6)
```

If the compiler may choose one of these literal occurrence pairs and cut
to its fixed character atoms, let `A=<Ad(u_1),...,Ad(u_m)>` act on `X_-`.
For the abstract simultaneous normalizer packet `H semidirect A`, the sharp
arbitrary-profile criterion using only this action table is

```text
every A-orbit O in X_- meets union_(j=1)^m F_j.         (ATM7)
```

Indeed, a representation of the simultaneous packet has constant character
multiplicity on each `A`-orbit.  If `(ATM7)` holds, on every orbit some menu
word has fixed-atom mass at least `1/|O|` of that orbit.  Summing first over
the finitely many pairs `(O,j)` and then taking the heaviest pair gives a
fixed positive fraction depending only on this finite action table.  If
`(ATM7)` fails, the orbit representation of a missed orbit has zero
same-atom Gram for every word in the menu.

The stronger, simpler covering test

```text
X_-=union_(j=1)^m F_j                                  (ATM7a)
```

is sufficient and gives the better pigeonhole fraction `1/m`, but is not
necessary: an uncovered character may share an orbit with a covered one.

Finite coverage is algebraically possible, so the one-word zero type is not
by itself a no-go for an adaptive menu.  Write `H=<z,e_1,...,e_9>` and choose
a nonzero functional `f` annihilating `z,e_1`.  The two involutions

```text
alpha_0(x)=x+f(x)e_1,
alpha_1(x)=x+f(x)(e_1+z)                               (ATM8)
```

fix `z`.  On marked characters their fixed sets are respectively
`chi(e_1)=+1` and `chi(e_1)=-1`, so these two nontrivial actions satisfy
the strong cover `(ATM7a)`.  Thus the right audit question is the actual
action table of authenticated selector words, not merely whether each
individual candidate action moves a type.

For the finite symmetry actions discussed as candidates in the binary
selector packet, the answer is negative even if all nonidentity actions are
allowed as a menu.  Reversal, the two adjacent swaps, and their three-cycles
act by simultaneous row/column permutations on the nine signs `C_ij`.  The
marked character

```text
chi_*(z)=-1,       chi_*(C_32)=-1,
chi_*(C_ij)=+1 for (i,j)!=(3,2)                        (ATM9)
```

is fixed by no nonidentity simultaneous permutation: a permutation fixing
this sign matrix must fix the ordered pair `(3,2)`, hence all three indices.
Every character in its six-element `S_3` orbit also has trivial stabilizer,
so that entire orbit misses all five fixed sets.  Therefore the menu of all
five nonidentity elements of this `S_3` action fails the sharp criterion
`(ATM7)`, not merely the stronger cover `(ATM7a)`.  This is a countermodel to
the `H semidirect S_3` action-table argument, not to extra relations which
the full binary-Leavitt occurrence words might impose.  An identity action
would cover trivially, but no actual unequal-scale selector relative word
with that action has been authenticated.  Indeed, the candidate `S_3`
actions themselves have not been authenticated as a complete menu of native
occurrence pairs.  Nor has the repository supplied a different pair of
relative normalizers realizing a cover such as `(ATM8)`.

There is a separate established sufficient branch around this pointwise
normalizer test.  If the **actual** selector contractions are restrictions
of full word unitaries to the marked projection and their relative word
conjugates `z` to a fixed nonzero root in a disjoint root position, then
`root-valued-relative-transport-forces-cross-gram` gives the arbitrary-profile
bound

```text
tr(S_1^*S_2S_2^*S_1)>=(1/4)tr(P).                    (ATM10)
```

The direct root-overlap theorem is already uniform enough; no finite-type
enumeration remains in that branch.  Its sole unresolved input is literal
occurrence typing: the coefficient triangles and the Morita rectangular
model do not prove that the two analytic unequal-scale transports are the
two restrictions whose relative word has the asserted root conjugacy.

Hence the finite audit leaves two sharp, noninterchangeable proof targets
for `binary-leavitt-arbitrary-profile-native-cross-gram`:

1. authenticate the root-valued relative identity for the two actual
   stabilized selector occurrences; or
2. authenticate a finite menu satisfying the orbit criterion `(ATM7)` and show
   that its typewise choice preserves the two native selector meanings and
   mixed Pauli gauges (a single word is the special pointwise-trivial case),
   or use a genuinely finite-matrix relation which pays every uncovered
   orbit type.

Individual root-density floors, regular Hecke fractions, and scalar
restriction multiplicities prove neither target.  No Property `(T)`,
Kazhdan projection, canonical trace, or literature input is used.

DERIVATION
arbitrary-profile-selector-type-menu-proof

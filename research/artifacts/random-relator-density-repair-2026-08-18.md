# 2026-08-18 — Random-relator lane: cubulation no-go and the balanced-density repair

**Status:** source-verified research audit. No nonhyperlinear group is claimed here.

This note tightens the random-relator route to `non-hyperlinear-group`.  The
important outcome is two-sided:

1. a tempting preservation event is actually impossible for the goal;
2. there is a repaired random model which keeps the unitary small-ball
   mechanism available without entering that no-go region.

The lane remains completely separate from the repository's property-(T)
compression, Leavitt/Pauli, commutant, Cartan, toric-game and spherical
matching mechanisms.

## 1. The C'(1/6) preservation event is fatal, not helpful

The first version of the random-relator programme suggested using a classical
small-cancellation event to guarantee that a short free ball survives the
quotient.  At the strongest familiar threshold, this cannot possibly produce
a nonhyperlinear group.

Martin--Steenbock, arXiv:1409.3678, prove that a quotient of a free product of
finitely many cubulable groups by a finite family satisfying the classical
`C'(1/6)` condition is cubulable.  Apply this with the free group

```text
F_k = Z * ... * Z.
```

A finite classical `C'(1/6)` presentation is word-hyperbolic.  Agol--Groves--
Manning, arXiv:1204.2810, prove that cubulated hyperbolic groups are virtually
special; the Haglund--Wise consequences recalled there make them linear.
Hence such a group is residually finite, therefore sofic, therefore
hyperlinear.

So the implication is absolute:

```text
finite C'(1/6) presentation
        => hyperbolic + cubulated
        => virtually special / linear
        => residually finite
        => sofic
        => hyperlinear.
```

This is not merely a warning about random groups.  Any route whose final
presentation is certified by classical `C'(1/6)` has already certified the
opposite of the root target.

There is a matching density-model boundary.  Ollivier--Wise prove that an
ordinary Gromov random group at density `<1/6` acts freely and cocompactly on a
CAT(0) cube complex.  Kozma--Lubotzky, arXiv:1810.01529, explicitly contrast
their fixed-degree representation theorem with the fact that density `<1/6`
random groups have faithful rational linear representations.  Thus the
random-presentation search should not spend effort below this threshold.

## 2. Why balanced relators are still the right unitary input

Avni--Glazer--Larsen, arXiv:2402.11108, prove a dimension-uniform small-ball
theorem for every fixed nontrivial word map on `SU(n)`: for each nontrivial
word `w` there are `alpha(w),rho(w)>0`, independent of `n`, such that any
Hilbert--Schmidt ball `B` of radius at most `rho(w)` times the diameter obeys

```text
Pr[w(V_1,...,V_k) in B] <= Haar_SU(n)(B)^alpha(w)
```

for independent Haar `V_i in SU(n)`.

Our microstate space is `U(n)^k`, and naively normalising determinants is not
safe in normalized Hilbert--Schmidt metric: the determinant can wind by an
order-one phase under a small normalized-HS perturbation.  The correct repair
is algebraic rather than analytic.

If `w` has zero exponent sum in every generator, equivalently
`w in [F_k,F_k]`, then

```text
w(z_1 U_1,...,z_k U_k)=w(U_1,...,U_k)
```

for arbitrary scalar phases `z_i`.  The multiplication map
`U(1) x SU(n) -> U(n)` pushes product Haar measure to Haar measure.  Therefore
for balanced words the `U(n)` Haar word distribution is exactly the same
`SU(n)` word distribution to which the Avni--Glazer--Larsen estimate applies.
No determinant correction of a microstate is required.

For a finite probability distribution `mu` supported on nontrivial balanced
words, take the minimum of the finitely many AGL exponents and radii.  Writing

```text
p_(n,r)(U)=Pr_(w~mu)[ d_2(w(U),1) <= r ],
beta_n(r)=Haar_SU(n){V : d_2(V,1)<=r},
```

Fubini gives the useful averaged estimate

```text
Integral_(U(n)^k) p_(n,r)(U) dU <= beta_n(r)^alpha.
```

Consequently Markov gives

```text
Haar{U : p_(n,r)(U) >= q} <= q^(-1) beta_n(r)^alpha.
```

This is the first genuinely dimension-uniform analytic bound in the
random-relator lane.  It is only an average/high-return-locus theorem, not yet
the net summability needed by `random-relator-net-killing-criterion`.

## 3. Balanced conditioning is not exponentially sparse

The requirement `w in [F_k,F_k]` does not destroy the exponential supply of
long relators.  Rivin, arXiv:math/9911076, computes the distribution of
cyclically reduced free-group words under abelianization, including a limiting
distribution.  In particular, along the parity-admissible lengths the
proportion with zero abelianization is only polynomially small in the word
length, rather than exponentially small.

Thus the balanced cyclic words have the same exponential growth rate
`2k-1` as all cyclically reduced words.  This observation is exactly what is
needed for a **balanced density model**: conditioning on zero abelianization
changes polynomial factors but not the exponential density parameter.

For fixed-size tuples it gives an especially clean transfer.  Bassino--
Nicaud--Weil, arXiv:1507.01088, prove that classical small-cancellation failure
for uniformly sampled cyclically reduced relators is exponentially rare.
Since the event that each of a fixed number of relators has zero abelianization
costs only a polynomial factor, conditioning a fixed tuple to be balanced
preserves exponential genericity of their small-cancellation conclusions.
This fact is mathematically correct but, by Section 1, **must not** be used at
`C'(1/6)` to target nonhyperlinearity.

## 4. The repaired model: balanced positive density above 1/6

The appropriate preservation event should be the density-model/macroscopic
one rather than classical `C'(1/6)`.

Fix `k>=2` and a density

```text
1/6 < d < 1/2.
```

For an admissible length `L`, let `C_L^0` be the cyclically reduced length-`L`
words with zero abelianization, and sample about

```text
(2k-1)^(d L)
```

relators from `C_L^0`.

Because `|C_L^0|` differs from the full cyclic-word sphere only by a
subexponential factor, this is still density `d` at the exponential scale.
Every relator is phase-safe for AGL, but the presentation is no longer inside
the classical cubulation certificate that forces hyperlinearity.

The best preservation theorem to import would be a conditioned analogue of
Ollivier's sharp density-model isoperimetric inequality (arXiv:math/0409226):
ordinary random groups at density `d<1/2` have a linear isoperimetric constant
controlled by `1-2d`.  Such a theorem gives exactly what the microstate
annihilation argument needs — an injective short free ball — without proving
virtual specialness.

A particularly clean experimental window is

```text
3/14 < d < 1/4.
```

For the ordinary density model, Montee (arXiv:2106.14931) constructs a
nontrivial CAT(0)-cube action below `3/14`, while Ashcroft
(arXiv:2206.14616) proves absence of property (T) below `1/4`.  The balanced
model already has an infinite abelian quotient, so property (T) is impossible
anyway; the point of this window is simply to stay well outside the known
proper-cubulation/linear regime while retaining a strong density gap below
`1/2`.

Nothing in this note asserts that the standard random-group theorems transfer
automatically under zero-abelianization conditioning.  That transfer is a new,
sharply formulated theorem target.  The plausible route is to prove that the
conditioned cyclic-word process retains the same exponential prefix/heavy-
overlap estimates: fixing a prefix contributes its abelianization vector, and
the suffix must return to the opposite vector; Rivin/local-limit estimates say
that this changes probabilities only by polynomial factors away from the final
`o(L)` letters.  Density arguments whose good/bad counts are separated by an
exponential margin should then survive.

## 5. AGL high-return packing: exact reduction and exact limitation

The AGL estimate can be converted into a packing inequality without any
unproved representation theory.  Suppose every relator in the support has
length at most `L`.  Word evaluation is `L`-Lipschitz in the max normalized-HS
metric on generator tuples.  Hence if

```text
p_(n,r)(U) >= q
```

and `max_i d_2(U_i,V_i)<=eta`, then

```text
p_(n,r+L eta)(V) >= q.
```

If `{U^a}` is an `eta`-separated family in the high-return locus, the
`eta/2` tuple-balls are disjoint and lie in the enlarged high-return locus.
Let `v_n(eta)` be Haar measure of one `eta`-ball in `U(n)`.  Then

```text
# {U^a}
 <= q^(-1) beta_n(r+L eta)^alpha / v_n(eta/2)^k.
```

This is a real packing theorem, but it also explains why the AGL estimate
alone is unlikely to close the route.  Both numerator and denominator live on
`n^2`-dimensional compact Lie groups.  The denominator pays for all `k`
generators, whereas a one-word AGL estimate only pays one target-group volume.
The remaining breakthrough must therefore exploit **structure of high-return
tuples**, simultaneous-conjugacy quotient entropy, or a genuinely multiword
small-ball theorem whose effective codimension grows with the number of
independent random relators.

That is a much smaller and more geometric gate than the previous vague phrase
"random words should anti-concentrate".

## 6. Fixed-dimension evidence and the dimension-escape diagnosis

Kozma--Lubotzky, arXiv:1810.01529, prove that for every fixed representation
degree `s`, a positive-density random group has no nontrivial degree-`s`
representation over any field with overwhelming probability.  Their
quantitative intermediate estimate has the number of random relators grow
with the fixed degree, so it does not directly give an all-dimensions theorem.

For this programme that is exactly the right diagnosis: any surviving
approximate unitary model has to escape to increasing matrix dimension.  The
open analytic gate is therefore a **uniform tubular-volume theorem for the
high-dimensional approximate representation strata**, not another fixed-size
classification.

A natural technical bridge is real-algebraic tubular-volume theory: word
relations are bounded-degree polynomial equations in matrix entries, and
Martin Lotz (arXiv:1210.3742) gives codimension-sensitive volume bounds for
tubular neighborhoods of real algebraic varieties.  To use this here one must
supply a codimension statement uniform in matrix size after removing the
scalar/repeated-block strata.  This is recorded as a future attack, not a
premise.

## 7. What changed in Cairn

The useful state after this audit is:

- classical `C'(1/6)` is recorded as a **proved dead zone** for the root;
- balanced words are retained as the right way to import AGL from `SU(n)` to
  the `U(n)` microstate setting;
- the preservation target is moved to a balanced positive-density/macroscopic
  isoperimetry theorem above density `1/6`;
- the analytic target is reduced to high-return-set / multiword tubular
  packing after the explicit AGL average bound.

This is stronger than merely adding another random-group idea: it removes a
large false-positive region and pins two precise theorems whose conjunction
would make the probabilistic method viable.

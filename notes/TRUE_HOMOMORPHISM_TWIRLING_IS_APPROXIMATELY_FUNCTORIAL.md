# Homomorphism twirling is approximately functorial

Date: 2026-08-14

## 1. Outcome

The Leavitt compressors act on finite additive packets by injective, proper
linear maps.  Their dual maps are therefore many-to-one, so the automorphism
version of finite Fourier normalizer rounding does not apply.  Nevertheless,
properness causes no loss at the level of intrinsic spectral paths.

For every homomorphism of finite abelian groups, Fourier averaging is the
orthogonal projection onto the corresponding exact intertwiner space.  The
squared covariance defect is exactly twice the discarded Hilbert--Schmidt
mass.  Moreover, these repaired intertwiners compose up to a dimension-free
error.  If all three covariance defects are at most `eta`, then the repaired
two-step path differs from the repaired composite by at most

```text
2 sqrt(2) eta.                                       (HAF1)
```

There is no factor depending on a group order, an index, or the number of
extension characters.  When the second arrow is repaired on its whole
source group, the spectral expansion of the repaired composite has one
canonical intermediate character on every path.  Thus one never needs to
choose representatives of the many-to-one dual fibers.

This is a rigorous synchronization lemma, not the missing nonhyperlinearity
theorem.  An arbitrary exact commutant gauge remains an exact intertwiner and
survives twirling.  The unresolved step is now narrower: prove that the two
four-root realizations define the same intrinsic repaired path (and that
these paths are the coefficients of the multiplication implementer).  The
present result removes only the false extra requirement that the compressor
act bijectively on character labels.

## 2. Fourier projection for an arbitrary homomorphism

Let `F,G` be finite abelian groups, let

```text
alpha:F -> G                                           (HAF2)
```

be a homomorphism, and let `rho` and `sigma` be unitary
representations of `F` and `G` on finite-dimensional tracial Hilbert spaces.
For an operator `X` between the representation spaces, put

```text
Q_alpha(X)
 = (1/|F|) sum_(a in F) sigma(alpha(a))* X rho(a).     (HAF3)
```

If `P_chi` and `R_psi` are the spectral projections of `rho` and `sigma`,
character orthogonality gives the exact block formula

```text
Q_alpha(X)
 =sum_(chi=psi o alpha) R_psi X P_chi.                (HAF4)
```

Consequently `Q_alpha` is the Hilbert--Schmidt orthogonal projection onto

```text
X rho(a)=sigma(alpha(a))X,       a in F.              (HAF5)
```

Define the root-mean-square covariance defect

```text
e_alpha(X)^2
 =(1/|F|) sum_(a in F)
     ||X rho(a)-sigma(alpha(a))X||_2^2.               (HAF6)
```

The spectral blocks are orthogonal in Hilbert--Schmidt space, so

```text
e_alpha(X)^2
 =2 sum_(chi != psi o alpha)||R_psi X P_chi||_2^2
 =2||X-Q_alpha(X)||_2^2.                              (HAF7)
```

This extends `(RPC65)--(RPC68)` and the twisted formula `(FAT23)` from
automorphisms to arbitrary homomorphisms.  Injectivity or surjectivity is not
used.  In particular, the proper Leavitt corner maps have the same sharp
`1/sqrt(2)` repair constant as bijections.

The averaging in `(HAF3)` is also contractive in operator norm.  Thus if
`X` is a contraction, so is `Q_alpha(X)`; no polar decomposition or equality
of character multiplicities is needed for the path estimates below.

## 3. Dimension-free approximate functoriality

Let

```text
F --alpha--> G --beta--> H                            (HAF8)
```

be homomorphisms of finite abelian groups.  Let `rho,sigma,theta` be
representations of `F,G,H`, and let `X,Y` be contractions with the indicated
source and target spaces.  Besides `e_alpha(X)` and `e_beta(Y)`, write

```text
e_(beta|alpha)(Y)^2
 =(1/|F|) sum_(a in F)
   ||Y sigma(alpha(a))-theta(beta(alpha(a)))Y||_2^2.  (HAF9)
```

The pointwise telescope

```text
YX rho(a)-theta(beta(alpha(a)))YX
 =Y[X rho(a)-sigma(alpha(a))X]
  +[Y sigma(alpha(a))-theta(beta(alpha(a)))Y]X        (HAF10)
```

and Minkowski's inequality give

```text
e_(beta alpha)(YX)
 <=e_alpha(X)+e_(beta|alpha)(Y).                      (HAF11)
```

Let

```text
X_0=Q_alpha(X),
Y_0=Q_beta(Y),
Z_0=Q_(beta alpha)(YX).                               (HAF12)
```

Using `(HAF7)`, contractivity, and a two-factor telescope,

```text
||Y_0 X_0-Z_0||_2
 <=[e_beta(Y)+e_alpha(X)+e_(beta alpha)(YX)]/sqrt(2)
 <=[e_beta(Y)+2e_alpha(X)+e_(beta|alpha)(Y)]/sqrt(2). (HAF13)
```

Therefore, if the full first-arrow, full second-arrow, and restricted
second-arrow defects are all at most `eta`, then

```text
||Y_0 X_0-Z_0||_2 <=2 sqrt(2) eta,                   (HAF14)
```

which is `(HAF1)`.  In the intended group-microstate application, every
element of each selected finite additive packet is included in the tested
packet.  A uniform word error bounds both the full and restricted RMS
defects directly, so no subgroup-index comparison is needed.

## 4. The intrinsic path expansion

Let `S_zeta` be the spectral projections of `theta`.  Full repair of the
second arrow gives

```text
Y_0=sum_(psi=zeta o beta) S_zeta Y R_psi,
X_0=sum_(chi=psi o alpha) R_psi X P_chi.              (HAF15)
```

Multiplying the two expansions yields

```text
Y_0 X_0
 =sum_(chi=zeta o beta o alpha)
   S_zeta Y R_(zeta o beta) X P_chi.                 (HAF16)
```

For each terminal character `zeta`, the intermediate character is
canonically `zeta o beta`.  The many-to-one map

```text
dual(G) -> dual(F),       psi |-> psi o alpha         (HAF17)
```

creates several terminal paths above the same source character, but it does
not create a choice inside any path.  Formula `(HAF16)` is therefore the
correct gauge-covariant replacement for choosing extension-character
representatives by hand.

Iterating `(HAF13)` gives the analogous statement for every fixed-depth
compressor tree, with error linear in the number of edges and independent
of all fiber cardinalities.  The binary Leavitt obstruction uses fixed
depth, so this iteration introduces no growing-depth loss.

## 5. Exact interface with four-root multiplication

The finite unitriangular envelope supplies all additive root packets and all
bounded products in one exact finite representation.  Apply `(HAF3)` to the
actual microstate words representing the raw and comb compressor arrows.
Equations `(HAF13)--(HAF16)` then give canonical, approximately functorial
spectral path contractions.  This closes the purely Fourier part of the
synchronization problem:

```text
proper compressor
 -> intrinsic incidence twirl
 -> canonical composable path blocks
 -> no extension-fiber representative choice.       (HAF18)
```

What is not proved is the multiplication comparison

```text
intrinsic path block for (ab)c
   = intrinsic path block for a(bc),                 (HAF19)
```

with the blocks identified as coefficients of one approximately unitary
bi-corepresentation.  The abstract four-root group words are close with the
uniform `30 delta` bound, but passing from those whole unitaries to the
specific blocks in `(HAF16)` must still be justified.  This is exactly the
coproduct-identification gate in
`TRUE_COPRODUCT_DEFECT_PINS_COMMUTANT_GAUGE.md`.

The limitation is real.  Multiplying an exact intertwiner by an arbitrary
unitary in the relevant commutant leaves `(HAF5)` exact, so Fourier twirling
alone cannot pin that gauge.  Once `(HAF19)` is promoted to the genuine
coproduct defect of the repaired implementer, the gauge-pinning theorem
classicalizes it and the existing robust `1/36` endpoint applies.

## 6. Status

This note proves that non-bijective character transport is not itself the
finite-multiplicity obstruction.  The remaining statement is no longer
"synchronize arbitrary extension fibers."  It is the following concrete
coefficient theorem:

> Assemble the intrinsic twirled path blocks `(HAF16)` into the actual
> repaired coefficient implementer and identify its dual coproduct defect
> with the averaged four-root associativity energy.

That theorem, followed by approximate bi-corepresentation classicalization
and the already formalized paired-quotient floor, would finish the proposed
nonhyperlinearity proof.  It has not yet been proved.

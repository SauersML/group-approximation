# Shadow--Kleene Saturation: from one tracial bug to a full MF radical

**Date:** 2026-08-22

## Executive theorem

For a countable group `G`, let

```text
S(G) = R_{infinity->2}(G)
```

be the subgroup of elements killed in the normalized Hilbert--Schmidt
ultraproduct attached to every operator-norm almost representation of `G`.
Call a nonidentity element of `S(G)` a **shadow bug**.

If a finitely generated recursively presented group contains one shadow bug,
then there is a 2-generated finitely presented acylindrically hyperbolic
property-(T) group `Q` with

```text
normMFResidual Q = top.
```

Every norm-matrix-corona homomorphism out of `Q` is therefore trivial, every
nontrivial quotient of `Q` again has full MF residual, and every homomorphism
from `Q` to an operator-MF group is trivial.  If the shadow-bug source is
already finitely presented, torsion-free, and acylindrically hyperbolic, the
output may also be chosen torsion-free.

The architecture is

```text
one shadow word
  -> normal closure
  -> Higman finite-presentation envelope
  -> free-product AH envelope
  -> Hull normal-closure router
  -> Kazhdan moving-corner detector
  -> full MF radical.
```

The input is genuinely weaker than non-MF.  The route
`mf-vs-tracial-radical-strict-gap` gives an operator-MF group with a
nontrivial element of `S(G)`.

## 1. The shadow residual

An operator-norm almost representation is a sequence

```text
phi_n : G -> U(d_n)
```

whose multiplicative defect tends to zero in operator norm on every fixed
pair.  Since normalized HS norm is bounded above by operator norm, it induces
an honest homomorphism `rho_phi,U` into a normalized-HS ultraproduct for every
ultrafilter extending the cofinite filter.  Define

```text
S(G) = intersection ker(rho_phi,U).
```

It is a normal subgroup.  More strongly, for every homomorphism `f:G->H`,

```text
f(S(G)) <= S(H).
```

Indeed, an operator-norm almost representation of `H` restricts along `f`.
Injectivity is needed only to ensure that a nonidentity word stays
nonidentity.  Consequently

```text
w in S(G)  =>  <<w>>^G <= S(G).
```

These statements and the saturation endpoint are kernel-checked in
`GroupApproximation/Sofic/OpToHSShadowResidual.lean`.

## 2. The Kazhdan detector

The checked theorem

```text
normalKazhdan_le_normMFResidual_of_hyperlinear_killed
```

says that if a normal property-(T) subgroup `K` is contained in an
op-to-HS-killed subgroup, then `K <= normMFResidual G`.  Applied to the
subgroup `S(G)` it gives

```text
K normal in G, K has (T), K <= S(G)
  => K <= normMFResidual G.
```

The reason is rank renormalization.  A norm-corona witness may move only a
vanishing-rank subspace.  The Kazhdan Laplacian cuts out its moving
projection; normality makes that projection ambient-invariant; compression
and polar correction give another operator-norm almost representation; and
normalizing by the moving rank makes a fixed Kazhdan generator survive in
HS norm.  This contradicts membership in `S(G)`.

Thus

```text
G has (T), S(G)=G  =>  normMFResidual G=G.
```

No central element, finite order, Clifford representation, or spectral cut
of a marked involution is used.

## 3. One-word saturation in the finitely presented AH case

Let `E` be finitely presented and acylindrically hyperbolic, and suppose

```text
1 != w in S(E),
N = <<w>>^E
```

is suitable.  Take a fixed finitely presented non-elementary hyperbolic
Kazhdan group `H_T`.  Hull's relative common-quotient theorem may be run with
two reservoir elements `h_1,h_2` chosen inside `N`.  Protect `w`, and route
every finite generator `x_i` of `E` by a relation

```text
x_i = W_i(h_1,h_2).
```

The common quotient `q:E->Q<-H_T` then has

```text
q(w) != 1,
q(N) = Q,
Q = <q(h_1),q(h_2)>.
```

It is finitely presented and acylindrically hyperbolic, and has property (T)
as a quotient of `H_T`.  If both inputs are torsion-free, Hull's torsion
clause makes `Q` torsion-free.

Functoriality gives

```text
Q = q(N) <= q(S(E)) <= S(Q).
```

Hence `S(Q)=Q`, and the detector gives

```text
normMFResidual Q = Q.
```

## 4. From one recursively presented word

Let `G` be finitely generated and recursively presented with
`1 != w in S(G)`.  Effective Higman embedding gives an injection `G->H` with
`H` finitely presented.  The bug remains nontrivial and shadow-killed in
`H`.  Put

```text
E = H * F_2.
```

This is finitely presented and non-elementary acylindrically hyperbolic, with
trivial finite radical.  The word remains a shadow bug.  Its normal closure
is infinite: if `a` is a free generator, the conjugates
`a^n w a^-n` are distinct by free-product normal form.  An infinite normal
subgroup is s-normal and non-elementary; trivial finite radical makes it a
suitable Hull reservoir.  Section 3 now applies.

This proves the one-shadow-word theorem without demanding property (T),
finite presentation, acylindrical hyperbolicity, or non-MF at the source.

## 5. Shadow--Kleene theorem

Suppose a total compiler sends a machine index `e` to a finite alphabet,
uniformly recursively enumerable relators, and a word `w_e` in the resulting
group `Gamma_e`, with

```text
HALT(e)    => w_e != 1,
NONHALT(e) => w_e in S(Gamma_e).
```

By Kleene recursion, build a machine which knows its own compiled pair and
halts exactly when proof enumeration finds `w=1`.  It cannot halt: a proof
would say `w=1`, while the HALT clause says `w!=1`.  If `w` were trivial, a
finite derivation would eventually be enumerated, so nonhalting also proves
`w!=1`.  The NONHALT clause then supplies a nontrivial shadow bug.  Section 4
compiles it into a finitely presented full-MF-radical group.

The fixed-point machine reads no matrices, dimensions, approximation errors,
thresholds, rates, or runtimes.  It searches proofs only.  The remaining open
computational target is therefore

```text
reverse-kleene-op-to-hs-shadow-word:
  HALT => algebraic survival,
  NONHALT => op-to-HS shadow erasure.
```

This is strictly weaker than the threshold-free hyperlinear target, because
only HS shadows arising from operator-norm almost representations must erase
the word.

## 6. Explicit unconditional HNN seed

Use the pre-quotient double-HNN skeleton.  Let `P` be finitely presented,
torsion-free, and Kazhdan, with

```text
P_1 x P_2 x S <= P,
```

where `P_i` is isomorphic to `P` and `S` is infinite, finitely presented,
nonabelian, simple, and torsion-free.  Form

```text
E = <P,u_1,u_2 | u_i P u_i^-1 = P_i>.
```

This group is finitely presented, torsion-free, and acylindrically
hyperbolic.  Choose `s,x in S` with `[s,x]!=1`, and set

```text
t = u_1,
c = u_1^-1 s u_1,
w = [s,x].
```

The direct-product relation gives `[c,P]=1`, while `t c t^-1=s`.  Britton's
lemma embeds `P`, so `w!=1` in `E`.  Kazhdan transport of asymptotic
commutants makes `s` commute with all of `P` in every normalized-HS shadow
of an operator-norm almost representation.  Therefore `[s,x]` vanishes:

```text
1 != w in S(E).
```

Lean records this extraction from `FournierFacioDefectData` as

```text
witness_commutator_mem_opToHSShadowResidual
exists_nontrivial_opToHSShadowBug.
```

Apply the torsion-free version of Section 3 to the normal closure of this
single word.  The output is 2-generated, finitely presented, torsion-free,
acylindrically hyperbolic, Kazhdan, nontrivial, and has full MF residual.

## 7. Hereditary and finite-challenge consequences

Full MF residual passes to quotients: a corona representation of a quotient
pulls back, and surjectivity makes it trivial.  Hence every nontrivial
quotient is non-MF and every homomorphism to an MF group is trivial.  In
particular there are no nontrivial finite-dimensional unitary images, finite
quotients, or residually finite quotients.

If `Q=<a,b | R>` and `v!=1` in `Q`, then the finite conditions

```text
r(a,b)=1 for r in R,
v(a,b)!=1
```

define a nonempty clopen cylinder of 2-marked quotients, all with full MF
radical.

Hull may protect any finite ball of the source while routing the normal
closure onto the output.  Thus for each radius one gets a full-radical
quotient agreeing with the source on that ball.  The non-MF payload can be
placed beyond an arbitrarily large finite observation horizon.

## Trust boundary

Kernel checked:

* `GroupApproximation/Sofic/NormalKazhdanHyperlinearKilled.lean` -- the
  moving-corner detector;
* `GroupApproximation/Sofic/OpToHSShadowResidual.lean` -- the shadow subgroup,
  functoriality, normal closure, one-word saturation endpoint, the logical
  Shadow--Kleene fixed-point contradiction and bug/endpoint equivalence, and
  explicit HNN bug extraction;
* `GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean` -- routed
  full-radical and quotient consequences.

Published/external existence boundary:

* Higman/Mikaelian effective embedding;
* Osin's s-normal non-elementarity theorem;
* Hull's suitable-subgroup routing and torsion clauses;
* the Fournier--Facio input groups and double-HNN skeleton.

The compression-free computational compiler satisfying the Shadow--Kleene
NONHALT clause remains open.

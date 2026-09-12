# An approximate bi-corepresentation has almost commuting coefficients

Date: 2026-08-14

## 1. Outcome

The uniform multiplication-table classicalizer does not require exact
coordinate homomorphisms `beta` and `gamma`.  It only requires one unitary
which is approximately multiplicative for the primal and dual coproducts.

Let `(A,Delta)` be a finite Kac algebra, let `(Ahat,Deltahat)` be its finite
dual, and let `C` be a finite tracial algebra.  For a unitary

```text
V in Ahat tensor C tensor A                               (ABC1)
```

put

```text
delta_L = ||(Deltahat tensor id tensor id)V
             -V_134 V_234||_2,
delta_R = ||(id tensor id tensor Delta)V
             -V_123 V_124||_2.                           (ABC2)
```

Then

```text
||V_234 V_135-V_135 V_234||_2
  <=3(delta_L+delta_R).                                  (ABC3)
```

The constant is independent of `dim(A)`, `dim(C)`, and the order of an
underlying finite group.  In normalized orthonormal coefficient bases,
Parseval turns the square of `(ABC3)` into an averaged coefficient
commutator bound

```text
mean ||[v_(i,j),v_(k,l)]||_2^2
  <=9(delta_L+delta_R)^2.                               (ABC4)
```

Thus a sequence of finite table sizes may grow arbitrarily: if the two total
coproduct defects tend to zero, its coefficient transport becomes classical
at the exact total-error scale used by the edge-PVM endpoint.

This is still a reduction, not a proof of nonhyperlinearity.  The remaining
atlas theorem is now the construction of `V_n` and the direct estimate
`delta_(L,n)+delta_(R,n)->0` from the fixed cross-root microstate relators.

## 2. Five-leg proof

The two coproduct maps act on disjoint tensor legs, commute, preserve the
normalized trace, and are star-homomorphisms.  Put

```text
T=(Deltahat tensor id tensor Delta)V.                   (ABC5)
```

Apply `Deltahat` to the second relation in `(ABC2)`.  This first costs
`delta_R`.  Apply the first relation in `(ABC2)` to each of the two resulting
`V` factors; a two-factor unitary telescope costs another `2 delta_L`.
Therefore

```text
||T-V_134 V_234 V_135 V_235||_2
  <=delta_R+2 delta_L.                                  (ABC6)
```

In the opposite order, applying `Delta` to the first relation and then the
second relation to both factors gives

```text
||T-V_134 V_135 V_234 V_235||_2
  <=delta_L+2 delta_R.                                  (ABC7)
```

Compare `(ABC6)` and `(ABC7)`, then cancel the common outer unitaries
`V_134` and `V_235`.  The result is

```text
(delta_R+2 delta_L)+(delta_L+2 delta_R)
 =3(delta_L+delta_R),                                  (ABC8)
```

which proves `(ABC3)`.

The final bi-invariant metric step is formalized source-first as
`middle_swap_distance_le_three_mul_add` in
`GroupApproximation/Leavitt/RawWordReynoldsGap.lean`.  No build was run.

## 3. Relation to exact quantum automorphisms

At `delta_L=delta_R=0`, `(ABC3)` is equation (3.1) in the
Kasprzak--Sołtan--Woronowicz proof.  Slicing the four outer legs says that
all coefficients of `V` commute.  For an ordinary finite group table, these
coefficients are the entries of the multiplication-coherent magic
transport.  Their joint products are the PVM over ordinary automorphisms
described in `TRUE_MULTIPLICATION_TABLE_QUANTUM_CLASSICALIZATION.md`.

The earlier exact-homomorphism formulation is a sufficient way to construct
`V`: if

```text
V=(id tensor beta)W,
V'=(gamma tensor id)W,
||V-V'||_2=epsilon,                                    (ABC9)
```

then `delta_L=0` and `delta_R<=3 epsilon`, recovering the previous
`9 epsilon` bound.  The new formulation is strictly better for the atlas:
both coproduct identities may be approximate, and there is no need to round
either side to a homomorphism before classicalization.

## 4. Why this matches the live normalized-HS scale

The paired-transport obstruction is already averaged over all source and
target labels.  It does not require a worst-entry estimate.  Likewise,
`(ABC2)` uses one normalized tensor `L2` norm for the complete multiplication
table, and `(ABC4)` controls the normalized mean of all coefficient
commutators.  No union bound over `|A|^4` occurs.

This avoids three previous losses:

1. no minimum spectral gap between individual characters;
2. no maximum over a growing family of table entries; and
3. no stability modulus for a growing universal quantum-automorphism
   presentation.

Finite PVM coarsening and tree gluing are also total-error statements, so
the downstream argument stays on this averaged scale.

## 5. Exact atlas interface

The relative raw/comb implementer should define `V_n` after the finite
additive character packets are exactified.  The two equations in `(ABC2)`
have distinct meanings:

- `delta_L` measures coherence with addition/character restriction on one
  root chart;
- `delta_R` measures coherence with the dual coefficient multiplication
  read through the cross-root Steinberg commutators.

Local additive automorphism completion controls only the first type and is
known to admit finite atomic countermodels.  The second type is precisely
where the multiplication module enters.  The new target is therefore not a
generic commutant-lifting assertion:

> construct one finite-coordinate unitary `V_n` whose two complete
> coproduct defects are bounded, in normalized tensor Hilbert--Schmidt norm,
> by a dimension-free function of the fixed atlas relator defect.

If this estimate is obtained, `(ABC4)` supplies asymptotically commuting
transport coefficients, their joint spectral PVM gives the deterministic
whole-map decoder, and the already formalized tree gluing plus robust
`1/36` floor closes the contradiction.

## Primary source

- P. Kasprzak, P. M. Sołtan, and S. L. Woronowicz,
  *Quantum automorphism groups of finite quantum groups are classical*,
  [arXiv:1410.1404](https://arxiv.org/abs/1410.1404), Theorem 3.1 and equation
  (3.1).  The estimate above is the normalized-`L2` perturbation of their two
  exact five-leg expansions.

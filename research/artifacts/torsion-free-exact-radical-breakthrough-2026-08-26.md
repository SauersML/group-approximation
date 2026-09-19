# Torsion-free exact-radical breakthrough pass, 2026-08-26

## Target and honest status

The target remains

```text
G finitely presented, torsion-free and sofic,
1 != K normal G with property (T),
Rad_MF(G)=K,                         G/K ~= Z.
```

The split-cyclic assembly and exact-radical proof are already unconditional.
This pass did **not** produce the missing sofic group.  It did produce a
strictly smaller terminal permutation problem, quantitative exclusions
inside that problem, an exact finite-presentation characterization for the
alternative infinitely presented-kernel route, and three new structural
no-go results.  Those results prevent several apparently promising searches
from being repeated.

## 1. The Titz--Witzel gate drops first to seven, then to five relators

The previous exact gate used three generators `x,y,z`, the eight auxiliary
words `A,B,C,D,E,F,S,H`, seven square relators, and five coupling relators.
Only two square relators are essential.  Freely,

```text
B=zEz^(-1),             H=yEy^(-1),             F=x^(-1)Hx.
```

Hence `B^2,F^2,H^2` follow from `E^2`.  From

```text
AEDF=1,                 DFEH=1,                 DSFE=1
```

one obtains

```text
D=EA^(-1)F,             H=EAE,                  S=FAF.
```

Since `E,F,H` are involutions, these identities imply `A^2=S^2=1`.
Therefore five of the original twelve relators are redundant.

The useful Nielsen variables are

```text
(c,e,r)=(C,E,z),
Y=r^2e^(-1),            X=Y^(-2)c.
```

The substitutions are literal free-group inverses:

```text
c=y^2x,                 e=y^(-1)z^2,             r=z,
y=Y,                    x=X,                     z=r.
```

They transport the separating word exactly as `y^8 <-> Y^8`.  Thus the
smallest Titz--Witzel lattice has an exact three-generator, seven-relator
presentation.  The finite-permutation gate may take `c` and `e` to be honest
involutions at every stage, leaving only five approximate equations coupling
two matchings and one arbitrary permutation.

This is a genuine Tietze reduction, not a computational conjecture.  The
dependency-free checker
`research/artifacts/titz-witzel-seven-relator-free-word-check.py` verifies
the free-word transcription and both substitutions; the normal-closure
derivation is written in `titz-witzel-seven-relator-gate-proof`.

### 1.1 Final two-generator form

The seven-relator form admits a second exact elimination.  Set `u=Y` and,
in the free group on `(e,u)`, define successively

```text
h   = u e u^(-1),             a   = e h e,
x   = a u^2,                  c   = u^2 a u^2,
f   = x^(-1) h x,             d   = e a^(-1) f,
s   = f a f,                  rho = x^(-1) s^(-1) c^(-1),
b   = rho u^(-1) rho.
```

Then the smallest Titz--Witzel group has the exact presentation

```text
<e,u | e^2, c^2,
       rho^2 e^(-1) u^(-1),
       b x u^(-1) d^(-1),
       a c d b>.
```

The inverse Tietze map is `Y=u`, `E=e`, `C=c`, `r=rho`; the separating
word is literally `u^8`.  Therefore the finite-permutation gate has only

```text
one exact matching e_n,
one arbitrary permutation u_n,
four approximate equations,
limsup d_H(u_n^8,1)>0.
```

The eliminated matching reconstructed from `(e_n,u_n)` is initially an
approximate involution; cyclewise involution rounding changes it by `o(1)`
and preserves the quantitative equivalence.  Thus the two-generator gate is
both an exact presentation theorem and an equivalent asymptotic CSP.

## 2. Two rigorous exclusions inside the reduced gate

### 2.1 The natural cyclic-affine family has maximal coupling error

For odd `n>=5`, on `Z/nZ`, put `h=(n+1)/2` and

```text
y(i)=i+1,               x(i)=-i+a,               z(i)=i+h.
```

All seven old square relators hold exactly and `y^8` moves every point.  But
the five coupling relators move exactly

```text
n-1, n-1, n, n-1, n
```

points.  Their normalized defects tend to `1,1,1,1,1`, not zero.  This
removes the most symmetric translation/reflection square-root ansatz.

The exact computation was checked at `n=5,7,9,11,17,31`.  Separate searches
on the exact-square manifold and unconstrained swap annealing also plateaued
at linear total defect.  Those latter searches are exploratory evidence only;
the affine-family formula is the theorem.

Direct annealing in the reduced `(c,e,r)` coordinates kept both matchings
exact and ran one million moves per size.  Representative best five-defect
vectors were

```text
n=12: (3,0,3,0,6),     supp(Y^8)=6,
n=20: (6,0,10,6,4),    supp(Y^8)=10,
n=28: (12,6,12,13,15), supp(Y^8)=16,
n=40: (19,4,18,18,19), supp(Y^8)=20.
```

The total defects remain linear.  This table is reproducible heuristic
search data, not a lower bound and not evidence that arbitrary solutions do
not exist.

### 2.2 Both matchings must have macroscopic support

In the `(c,e,r)` gate, set `e=1`.  Then

```text
Y=r^2,                  B'=F'=H'=1,
A'=r^(-4)c r^(-4),      D'=r^(-4)c r^(-2).
```

If


```text
delta_3=d_H(A'eD'F',1),       delta_4=d_H(D'F'eH',1),
```

bi-invariance gives

```text
d_H(Y^8,1) <= 8 delta_3 + 16 delta_4.
```

The same conclusion holds asymptotically when `d_H(e,1)->0`, by replacing
`e` with the identity and using the fixed-word Lipschitz estimate.
Explicit occurrence counting gives the dimension-independent bound

```text
d_H(Y^8,1) <= 8 delta_3 + 16 delta_4 + 296 d_H(e,1).
```

The other matching is forced as well.  If `c=1`, then `X=Y^(-2)` and the
second coupling word reduces freely to

```text
X r c S = Y r^(-2) = H^(-1).
```

Because `H=Y e Y^(-1)`, its defect is exactly `d_H(e,1)`.  Thus
`d_H(c,1)->0` first forces `d_H(e,1)->0`, and the preceding inequality then
collapses the mark.  Along every subsequence with positive marked
separation, **both** exact involutions have support bounded below by a
positive proportion.  More explicitly,

```text
d_H(Y^8,1)
 <= 296 delta_2 + 8 delta_3 + 16 delta_4 + 968 d_H(c,1).
```

If the mark stays at least `epsilon` and all coupling defects vanish, the
asymptotic support densities are therefore at least `epsilon/296` for `e`
and `epsilon/968` for `c`.

## 3. The same exotic building supplies no sofic donor

For the smallest Titz--Witzel building `X`, the primary source computes

```text
Aut(X)=barGamma,         Aut(X)^type=K,             [barGamma:K]=2,
```

and proves that `K` has no proper finite-index subgroup.  Since `Aut(X)` is
discrete, every lattice in it has finite index.  Intersecting such a lattice
with `K` shows that every lattice is exactly `K` or `barGamma`.

Consequently there is no independent residually finite, LEF, amenable, or
already-sofic lattice on the same building from which soficity could be
transferred by commensurability.  The common-building and common-ambient
measure-equivalence shortcuts collapse back to the original soficity gate.

## 4. Exact interface for an infinitely presented kernel

Let `K` be finitely generated, let `phi` be an automorphism, and put
`G=K semidirectProduct_phi Z`.  Then `G` is finitely presented **if and only
if** `K` has a finite two-sided invariant `L`-presentation: finitely many
base relators whose complete relation set is generated by word lifts of both
`phi` and `phi^(-1)`.

The forward direction is Reidemeister--Schreier rewriting of a finite
presentation of `G` along the exponent map.  The reverse direction adjoins
one stable letter and finitely many conjugation relators.  Hence the phrase
"finite automorphic presentation" is now an exact necessary-and-sufficient
gate, not merely a desirable feature.

This matters because a successful kernel need not itself be finitely
presented.  Requiring it to be finitely presented would solve Alekseev--Thom
Open Problem 6.1.  The exact weaker search target is instead:

```text
K finitely generated, torsion-free, sofic, property (T),
K has no nontrivial finite quotient,
K has a finite two-sided automorphic presentation,
and the ambient cyclic defect saturates K.
```

## 5. Standard self-similar ways to obtain that presentation fail

Two standard shift mechanisms are unavailable for a simple alternating
marked-limit kernel.

1. An infinite simple group cannot act faithfully on a locally finite rooted
   tree.  A nontrivial finite-level action has normal kernel; simplicity
   makes the kernel trivial and embeds the group into a finite symmetric
   group.  Therefore standard faithful automaton/contracting recursion cannot
   supply the desired simple infinite kernel.
2. If quotients `q_i:Gamma->Alt(n_i)` have unbounded `n_i>=7`, an exact mother
   automorphism shift
   `alpha^(-1)(ker q_i)=ker q_(i+1)` would force consecutive alternating
   quotients to be isomorphic, hence to have equal degree.  A coordinate
   shift in their product has the same obstruction.

Any alternating-limit solution therefore needs a new symmetry of the stable
relation kernel, not the obvious rooted-tree or finite-factor shift.

The current Rover--Nekrashevych `FP_infinity` simple groups do not repair this
gap.  Their commutators contain the Higman--Thompson group `V_d'`; consequently
they contain torsion and are not LEF.  They fail two mandatory kernel clauses
before property `(T)` or automorphic finite presentation is considered.

## 6. Cairn/source audit and remaining frontier

The repository's affine congruence construction already gives a concrete
torsion-free finitely presented Kazhdan compression source.  Its ascending
HNN vertical group is residually finite, however, so it is MF and cannot be
the required radical kernel.  Routing its defect into the existing
torsion-free Kazhdan full-radical quotient preserves every algebraic clause
but has no known soficity theorem.

The current primary-source sweep found no theorem proving the Titz--Witzel
lattice sofic and no torsion-free sofic Kazhdan group with full finite
residual and the required finite automorphic presentation.  The cleanest
remaining terminal problem is now the two-generator gate above:

```text
one exact involution e_n + one permutation u_n,
four displayed relator defects -> 0,
limsup d_H(u_n^8,1) > 0.
```

In the equivalent three-variable coordinates, both matchings must have
macroscopic support.  Solving the two-generator gate proves the soficity of
the Titz--Witzel kernel and completes the target by taking
`G=K x Z`; proving it impossible would eliminate that headline candidate but
would not by itself refute the general target.

## Validation

- The free-word checker prints `all free-word checks passed`.
- Each new Cairn claim and proof route previews as `ESTABLISHED`/`COMPLETE`.
- A full Cairn check still reports unrelated dangling references in the
  pre-existing `sl3-*` research nodes (and may report concurrent work in
  other areas); none involves the results recorded here.
- No Lean theorem was added in this pass.  These are paper-level Cairn proofs
  and explicit finite-word/permutation calculations.

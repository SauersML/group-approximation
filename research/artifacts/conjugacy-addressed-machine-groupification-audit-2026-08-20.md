# Conjugacy-addressed machine groupification audit

Date: 2026-08-20

## Outcome

This audit does **not** produce a nonhyperlinear group. Its useful output is
a sharper boundary for the machine/compiler route:

```text
literal conjugate local checks:       exact zero address-length loss;
coherent naming of orbit tape cells:  potentially unbounded stabilizer loss.
```

The first line is already represented by
`conjugacy-compressed-dimension-trigger`, now in its finite-prototype form.
The second is proved by the new established claim
`stabilizer-generator-control-has-unbounded-address-loss`. The remaining
machine target is correspondingly narrower: a finite group-theoretic
PCP/expander decoder that forces global cell consistency with a constant
normalized-Hilbert--Schmidt soundness bound.

## 1. Exact zero-loss transport of prototype checks

Fix finitely many relator words `r_1,...,r_s`. At a computation location `x`
put

```text
r_x=h_x^(-1) r_(j(x)) h_x.
```

For an arbitrary assignment of the generators to unitary matrices, formal
word evaluation is multiplicative and sends inverses to adjoints. Therefore

```text
r_x(U)-I=h_x(U)^* (r_(j(x))(U)-I) h_x(U)
```

and hence

```text
||r_x(U)-I||_2=||r_(j(x))(U)-I||_2.                    (1.1)
```

No approximate-representation hypothesis is needed for (1.1). The address
word may be arbitrarily long. The maximum defect of all addressed checks is
the maximum defect of the prototypes that occur, and any average squared
defect is only a convex combination of the prototype squared defects. Thus
neither address length nor runtime enters the local-check estimate.

This improves the diagnosis in `hs-pcp-boone-compiler`: an infinite
computation need not pay `T delta` merely because its local checks are far
from the origin. It pays `T delta` in a conventional derivation only when
the semantics are transported through `T` unrelated rewrites instead of
being installed as literal conjugate copies.

## 2. Where the loss moves: stabilizer coherence

Let tape cells be left cosets `G/H`, let `A` be a root observable, and put

```text
A_(gH)=U_g A U_g^*.
```

The names `g` and `gh` denote the same cell. Their discrepancy is exactly

```text
||Ad(U_g)(A)-Ad(U_(gh))(A)||_2
  =||A-Ad(U_h)(A)||_2.                                  (2.1)
```

If `H=<T>` and `h=t_1...t_L`, the generic deduction from generator control is
only

```text
||A-Ad(U_h)(A)||_2
 <= |h|_T max_(t in T union T^-1)||A-Ad(U_t)(A)||_2.     (2.2)
```

This factor is real, not an artifact of a loose estimate. On `C^2`, take
`A=sigma_z` and `U_t=exp(i theta sigma_x/2)`. Then

```text
||A-Ad(U_(t^n))(A)||_2=2|sin(n theta/2)|.
```

With `theta=L^-2`, the defect at `t^L` divided by the defect at `t` tends to
`L`. Finite stabilizer-generator relations therefore do not yield a
uniformly well-defined observable on `G/H`.

This explains the exact status of the Clifford orbit tape. Conjugacy can
copy the checks without loss, but a separate theorem must make the root
observable uniformly invariant under the whole stabilizer. Cairn already
contains one conditional sufficient mechanism:
`hs-stable-kazhdan-finite-bi-index-pair-gives-site-coherence` first exactifies
the ambient action and then uses an adjoint Kazhdan projection. The missing
structural existence target is recorded by
`uniform-hs-site-coherence-for-finite-bi-index-pair`.

## 3. Correct machine architecture after the audit

The live hypothetical compiler is

```text
Kleene fixed point
+ finite prototype checks placed by conjugacy
+ PCP/expander global consistency and marked-word decoding.
```

Kleene self-reference is already represented by
`kleene-mipco-self-destroying-game` and the complete desired compiler by
`hs-pcp-boone-compiler`. The new calculation removes local address transport
from the list of unknowns. It does **not** prove the semantic estimate

```text
||w(U)-c_(N(d))(U)||_2 <= C Def(U)
```

for a fixed marked word `w`, nor does it make multiple names of a tape cell
coherent. Those are the constant-soundness decoder theorem still missing
from `constant-hs-sound-self-detecting-tape-groupification`.

The old self-aware threshold shortcut remains invalid. If a simulation
still produces `T delta`, a hyperlinear microstate sequence supplies no
computable relation between the stage's dimension, defect, and the fixed
point machine's eventual runtime. The machine cannot safely choose a defect
threshold that dominates its own computation.

## 4. Deduplicated route map for the rest of the assessment

The remaining observations supplied to this audit were already present in
Cairn. They are linked here instead of being copied into new claim nodes.

| Observation | Existing Cairn node(s) | Exact status |
|---|---|---|
| A fixed non-CE BCS gives a dimension-independent matrix energy floor | `non-ce-bcs-has-robust-approximate-energy-gap` | established finite-dimensional obstruction; additive polynomial constraints are not yet groupified |
| Exponentially many Clifford/Pauli dimensions do not imply nonhyperlinearity | `commuting-schur-replicas-force-exponential-dimension`, `infinite-index-does-not-force-supercritical-site-rank` | established finite-window rank pressure, explicitly compatible with growing microstate dimensions |
| A common reducing carrier for all finite Clifford ranks would contradict one fixed matrix dimension | `summable-reducing-carriers-force-infinite-clifford-capacity` | established conditional endpoint; the common reducing carrier is missing |
| A signed finite-group block avoids the augmentation character | `character-rigid-signed-bcs-quotient`, `unique-trace-signed-corner-quotient-forces-nonhyperlinear` | open construction plus established trace-promotion theorem; a corner map alone still needs canonical-trace control |
| Steinberg relations compile ring addition and multiplication, but a trace-preserving decoder is missing | `relative-rank-one-fanizza-groupification`, `hs-schur-toeplitz-root-defect-collapse` | open normalized-HS groupification interface |
| The Iwahori edge problem reduces to one Nielsen involution of `Z*C_2` | `iwahori-commensurator-nielsen-involution`, `iwahori-nielsen-extension-transversality` | exact algebraic reduction; dimension-independent transversality remains open |
| The A8/A4 lane reduces to four rectangle holonomies and a scalar ellipse | `atlas-a4-packet-four-rectangle-normal-form`, `atlas-a4-root-energy-ellipse-ceiling` | finite exact compression; global inequality remains open |
| First-order A8 control is insufficient on attractive smaller packets | `atlas-certified-24-first-order-escape` | exact tangent no-go; collision/interior information must enter |
| A non-co-hyperlinear IRS is not a nonhyperlinear group | `non-cohyperlinear-irs-exists`, `diracization-gap-equals-nonhyperlinear-group` | published action/trace endpoint; the normal-Dirac promotion is missing |
| Local nonlinear central phases do not force a global canonical-trace obstruction | `boolean-predicate-central-phase-word`, `regular-trace-blocks-exact-local-predicate-return` | local finite packet exists; global return would also fire in the regular trace |
| Selector/reset amalgams and finite packet HNN transport do not carry contextual semantics | `selector-free-spin-reset-leaves-contexts-independent`, `clifford-block-amalgam-residually-finite` | exact representation-incidence no-go |

## 5. Canonical-trace rule

The audit reinforces the governing rule:

```text
a nonhyperlinearity proof must obstruct the canonical group trace,
not merely a selected representation or an arbitrary tracial state.
```

Every discrete group has its left-regular tracial representation. A finite
list of group identities cannot yield a contradiction by asserting that no
tracial representation with those identities exists. The obstruction must
be finite-dimensional/Connes-embeddability sensitive and must be promoted to
the canonical trace. This is why the live signed-corner target includes
character rigidity/unique trace, why normalized-HS rank mechanisms must act
on a positive canonical carrier, and why perfect completeness in the LCS
route is decisive.

## 6. External-status check

The repository's status labels agree with the April 2026 primary sources.
Taller and Vidick's revised abstract proves LCS hardness with completeness
`1-epsilon` and states that obtaining `epsilon=0` would imply a
nonhyperlinear group: [Taller--Vidick, arXiv:2507.22444v2](https://arxiv.org/abs/2507.22444).
This is represented by `taller-vidick-lcs-re-hardness` and
`perfect-lcs-gap-implies-nonhyperlinear`.

Manzoor proves a non-co-hyperlinear IRS and a non-Connes-embeddable
equivalence-relation von Neumann algebra, while explicitly noting that these
computability methods do not yet solve the group problem:
[Manzoor, arXiv:2502.06697v2](https://arxiv.org/html/2502.06697v2).
This is represented by `non-cohyperlinear-irs-exists` and
`non-ce-property-t-equivalence-relation-exists`.

## 7. Next falsifiable target

Do not revisit local conjugacy transport. The next theorem must instead
provide one of the following:

1. a finitely presented orbit tape whose stabilizer invariance follows with a
   dimension-independent normalized-HS modulus;
2. a finite PCP/expander code on cell names that turns any macroscopic naming
   inconsistency into constant prototype-relator energy; or
3. a different global decoder that never chooses coset representatives and
   sends the triggered local failure directly to the fixed marked word.

Any proposed proof must be rejected if its constant grows with stabilizer
word length, computation time, van Kampen area, detected multiplicity, or
matrix dimension. Conversely, a proof of one of the three items above would
combine with the already exact zero-loss identity to close a genuinely new
portion of `hs-pcp-boone-compiler`.

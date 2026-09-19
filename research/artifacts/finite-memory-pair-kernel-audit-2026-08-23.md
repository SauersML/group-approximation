# Finite-memory pair-kernel reduction: ingestion and audit

**Source:** external review session, 2026-08-23, unrefereed
("Finite-memory self-copy: a discrete kernel-jump reduction" and
"Finite-memory self-copy: full attack on the operator-norm gap", together with
a five-node Cairn patch).
**Auditor:** this session; every item below was re-derived before commitment.
**Verdict:** two positive items confirmed, one standard fact confirmed, the
proposed headline OPEN target **refuted**, and a repaired target substituted.

## 1. What the source proposed

For the Thompson even-lamp carrier

```text
I_X = ker(sum : F_2^(X) -> F_2),
Gamma_state = I_X rtimes V,
```

the source argued that neither `self-copy-kadison-kastler-checksum` nor
`operator-norm-finite-state-rounding` is necessary.  After exactifying the
lamp involutions (via `corona-commuting-torsion-lifts`) it proposed the
"moving-pair return checksum": for each actor generator `s`, with

```text
J_n(s) = sup { ||rho_n(b_(s x,s y))-I||_op : rho_n(b_(x,y))=I },
```

prove `J_n(s)<2` eventually.  Since `rho_n(b_(s x,s y))` is an exact
involution, `J_n(s) in {0,2}`, so any strict bound below `2` gives exact
kernel invariance.  Patch ids proposed:
`thompson-moving-pair-return-checksum` (OPEN),
`pointwise-pair-covariance-does-not-control-moving-kernel-jumps`,
`moving-tail-partition-kernel-jump-proof`,
`norm-matrix-corona-has-no-proper-isometries`,
`norm-corona-isometry-proof`.

## 2. Confirmed: the invariance lemma

Re-derived in full and landed as
`thompson-pair-kernel-invariance-kills-even-lamps`.  For an exact
`rho:I_X->U(d)`:

* `||rho(m)-I||_op in {0,2}` (exact involution, spectrum in `{+1,-1}`);
* `x ~ y iff rho(b_(x,y))=I` is an equivalence relation, because
  `b_(x,z)=b_(x,y)+b_(y,z)`;
* the image consists of commuting involutions, so it is simultaneously
  diagonalizable of order at most `2^d`, whence `|X/~| <= 2^d`;
* generator-wise invariance makes `X/~` a finite `V`-set, trivial because `V`
  has no nontrivial finite quotient, and universal by transitivity.

The lemma is correct, and it is a genuine strengthening of
`thompson-even-lamp-fp-finite-state-detector`: it needs **no** actor
representation, only invariance of the two-point kernel.

## 3. Refuted: the checksum as a target

The source's own §10 warns that `ker rho_n` need not be actor-invariant, but
then parks `J_n(s)<2` as a new hole.  That hole cannot be filled, and the
reason is sharper than the source's moving-tail construction.

**Counterexample (dimension two).**  Let `(A_n)` be any exhaustion of `X` by
finite sets and set

```text
sigma_n(m) = (-1)^(|supp(m) cap A_n|),
tau_n(m)   = diag(1, sigma_n(m)) in U(2).
```

`sigma_n` is a character of `I_X`, so `tau_n` is an exact homomorphism into
commuting involutions.  Every **fixed** `m in I_X` has finite even support, so
`sigma_n(m)=1` for large `n`: the lamp corona classes are all trivial, and
assigning `I_2` to every actor generator evaluates every relator of the finite
presentation to the identity (substituting `I_2` for actor letters turns a
relator into `tau_n(m_r)` for a fixed `m_r in I_X`).  The presentation defect
is exactly `0`.

But if `A_n` meets an infinite `s`-orbit then `s^(-1)(A_n) != A_n`, so picking
`x_n in s^(-1)(A_n) \ A_n` and `y_n outside A_n cup s^(-1)(A_n)` gives

```text
tau_n(b_(x_n,y_n)) = I,     tau_n(b_(s x_n,s y_n)) = diag(1,-1).
```

Hence `J_n(s)=2` for every `n`, in dimension `2`, for a zero-defect model of
the finite presentation whose lamp corona classes are all trivial — i.e. in a
case where the *conclusion the route wants is true*.  No dimension-independent
modulus can help.

**The two readings both fail.**  Universally quantified over exact
corrections, the checksum is false (above).  Existentially quantified, `rho=1`
is admissible exactly when the corona representation already kills the lamps,
so by §2 the hypothesis and the conclusion are the same statement — the
restatement-dressed-as-reduction trap.

**Diagnosis.**  A corona representation pins an exact lift only at fixed
module elements.  `sigma_n` is a character that is trivial on every fixed
element and nonconstant at the moving frontier, so the lift is free exactly
where the checksum needs control.  The source's tail-partition construction
shows the weaker fact that the fixed-pair implication can be eventually
*vacuous*; the character twist is strictly stronger, since there the actor is
exactly represented and fixed-pair covariance holds non-vacuously.

Landed as `exact-lamp-lifts-admit-moving-pair-kernel-jumps` with route
`moving-pair-kernel-jump-twist-proof`.  The source's two proposed ids for the
weaker fact were not used.

## 4. The repaired target

The defect of the checksum is that it constrains the *correction* rather than
tying it to the model.  Anchoring repairs it.  With `w_(x,y)` a transporter
naming of each pair lamp, ask for an exact commuting-involution `rho` with

```text
sup_(x != y) ||rho(b_(x,y))-w_(x,y)(U)||_op <= 1/2,            (PLC1)
sup_(x != y) ||U_s w_(x,y)(U) U_s^* - w_(s x,s y)(U)||_op <= eta < 1.  (PLC2)
```

The counterexample is excluded because there `w_(x,y)(U)=I` for every pair, so
an anchored `rho` is forced trivial.  The constants combine below the
involution threshold (`1+eta<2`), so §2 applies, and a final use of the
dichotomy in the corona (`Theta(b)` is an exact involution, so
`||Theta(b)-1|| in {0,2}`) turns the coordinatewise bound `1/2` into
`Theta(b)=1`.  No modulus tending to zero appears anywhere.

Landed as `thompson-pair-lamp-consistent-exactification` (OPEN) with route
`thompson-pair-lamp-exactification-non-mf-proof`.  It is weaker than
`operator-norm-finite-state-rounding` (two-point lamps, constant thresholds,
no corrected actor) and weaker than
`finite-presentation-must-expose-whole-module-with-uniform-defect` (no
all-pairs modulus).  It is strictly stronger than the target's conclusion and
can fail, so it is a reduction rather than a restatement.  Its natural
falsifier is a stabilizer-holonomy ladder along transporters of growing
length.

## 5. Confirmed: no proper isometries in a norm matrix corona

Standard, and correctly proved by the source: a bounded lift `x_n` of an
isometry has `||x_n^* x_n-I||->0`, hence is invertible for large `n` because
it is **square**, and its polar unitary is norm-close, so the class is
unitary.  Landed as `norm-matrix-corona-has-no-proper-isometries` with route
`norm-corona-isometry-proof`, with the scope note that the projections a group
presentation produces exactly in a corona are finite-subgroup character
projections — the existing finite-order/rank-monodromy lane.

## 6. Already in the graph, not re-recorded

* Uniform (Ulam) stability of Thompson groups does not apply to corona
  representations: `corona-defect-is-not-uniform` already records that corona
  representations supply pointwise, not uniform, defect.  The source's §15.G
  reaches the same conclusion independently.
* Finite-dimensional invisibility does not imply MF-radical membership:
  `corona-commutant-growth-witness`.
* Lossless conjugacy addressing: `conjugacy-addressed-opnorm-challenges-are-lossless`.
* Quantifier order of the depthwise lemma:
  `depthwise-opnorm-collapse-implies-mf-radical`.
* High transitivity plus two-torsion is not enough:
  `finitary-alternating-augmentation-lamp-global-rounding-no-go`.

## 7. Net effect on the frontier

No route closed.  The finite-memory lane keeps its three open gates; it gains
one strictly weaker gate (§4), one positive lemma (§2), one exact-corona fact
(§5), and one recorded no-go (§3) that removes a proposal which would
otherwise have been re-attempted.

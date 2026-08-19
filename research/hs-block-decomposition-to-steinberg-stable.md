---
rg: 2
id: hs-block-decomposition-to-steinberg-stable
kind: route
title: Transcribe the one-sided-compression nonsoficity argument to normalized HS
target: leavitt-steinberg-hs-stable
requires: [hs-expander-block-decomposition, tracial-median-concentration, leavitt-steinberg-hs-stability-fork]
artifacts:
  - c1168433:official/counterexample.tex
  - notes/NOTEPAD.md
---

The one-sided-compression criterion (`official/counterexample.tex`,
Proposition 2.3) proves that soficity of `G` forces the commuting non-LEF
subgroup `J` to be LEF, and with `J=V` Thompson's group this is what makes
`Q=EL_4(L_(F_2)(1,2))` nonsofic.  Its proof has three steps.  This route
records that **two of the three transcribe verbatim to a finite tracial
algebra**, so the whole gap between the permutation theorem and the
normalized-HS theorem is the single missing input
`hs-expander-block-decomposition`.  That corrects the ledger entry which
lists two permutation-specific inputs; integer cardinality is not one of
them.

## Step 2, conservation, transcribes

The permutation step is `sum_(z in Y) (f(p z)-f(z))=0`, formalized as
`Matching/PermutationConservation.permutation_conservation_full`, and it is
what upgrades a one-sided drift bound to an `L^1` bound.

**Lemma.**  Let `(M,tau)` be a finite von Neumann algebra, `u in M` unitary
and `f=f^* in M`.  Put `x = u f u^* - f`.  Then `tau(x)=0`, and if
`x >= -(eta*1 + c)` for some `c>=0` supported on a projection of trace
`<= gamma`, then

```text
‖x‖_1 = 2 tau(x_-) <= 2(eta + ‖c‖ gamma).
```

*Proof.*  `tau(u f u^*)=tau(f)` because `Ad u` is trace preserving, so
`tau(x_+)=tau(x_-)` and `‖x‖_1=2 tau(x_-)`.  Let `e` be the spectral
projection of `x` for `(-infinity,0)`.  Then
`tau(x_-) = -tau(e x e) <= tau(e(eta*1+c)e) <= eta + tau(c) <= eta + ‖c‖gamma`.

Specialising `M=l^infinity(Y)` with normalized counting trace and
`u f u^* = f o p^(-1)` returns the permutation identity exactly.  Trace
preservation under unitary conjugation is not weaker than bijectivity of a
permutation for this purpose; it is the same statement.

## Step 3, majority matching, transcribes

The permutation step is: distinct transported components cannot both occupy
a strict majority of the same target component, so the matching is
injective.  In Lean this closes with `omega` on `Finset.card`
(`Matching/BlockTransport.eq_of_two_mul_overlap_gt_card`), which is why it
was recorded as integrality-dependent.  It is not.

**Lemma.**  Let `e_1,...,e_k` be pairwise orthogonal projections and `f` a
projection in `(M,tau)`.  Then `sum_i tau(f e_i f) <= tau(f)`, so at most one
index satisfies `tau(f e_i f) > tau(f)/2`.

*Proof.*  `sum_i tau(f e_i f) = tau(f q f)` with `q = sum_i e_i <= 1`, and
`tau(f q f) = tau(f^(1/2) q f^(1/2)) <= tau(f)`.

No commutation and no integrality is used, and the permutation statement is
the case of indicator functions, where `tau(f e_i f) = |Q(P_i) cap D|/|Y|`.

**This does not collide with the index no-go.**
`notes/FALSE_KAZHDAN_COMPRESSION_INDEX_TO_PHASE.md:101-117` shows that an
*integer parity or Fredholm index* cannot be read from tracial microstates,
because "adding or removing one boundary dimension changes its parity while
changing a bounded operator by only `O(d^(-1/2))` in normalized
Hilbert--Schmidt norm".  That refutes the specific proposal
`KInd(U,Gamma)=ind(PUP)` and nothing more -- its own §5 says "This closes
only the direct proposal `(KIP10)`".  The majority-matching step reads no
integer off the model; it is the inequality above, and its stability under
`O(d^(-1/2))` perturbations is immediate because both sides are traces.
The two statements are about different objects and should not be conflated.

An alternative to assembling the matching by hand: in the **equal-trace**
case, `notes/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md` Proposition 11 converts an
almost-normalized `k`-atom block algebra directly into a Hamming-almost
multiplicative map on `k` points, which is a permutation model.  For a
nonsofic group that is already the contradiction, with no median device
needed.  The median device is what handles unequal block traces, so the
substance of the assembly is exactly the unequal-trace case.

## Step 1 is the whole gap

What does not transcribe is Kun's decomposition of a sofic approximation of
a Kazhdan group into expander components.  A permutation model acts on a
set, so the invariant algebra `l^infinity(Y)^Gamma` is atomic before any
theorem is applied and the atoms are the components; Kun's theorem only
upgrades them to expanders.  An almost-representation supplies no set, no
distinguished maximal abelian subalgebra, and -- since it is not a
representation -- no isotypic decomposition.  That is the content of
`hs-expander-block-decomposition`.

## Assembly

Having read the argument being transcribed
(`official/counterexample.tex:270-430`), its five steps and their tracial
status are:

1. **Two nested Kun decompositions**, for `Gamma` and for the ambient
   `G`.  This is `hs-expander-block-decomposition`, and it is the missing
   input.
2. **Median normalization and concentration of the size observable**, the
   manuscript's `f=M/(M+m_A)` and its conclusion `(8)`, "the sizes of
   original components meeting the same set `A \ E_n` differ by a factor
   tending uniformly to one" (`:371`).  This is
   `tracial-median-concentration`.  Half of it -- coarea -- already has a
   proved normalized-HS analogue; the other half is uniform expansion,
   i.e. step 1 again.
3. **Conservation**, which transcribes as `tau(ufu^*-f)=0` (above).
4. **Majority matching**, which transcribes as
   `sum_i tau(f e_i f) <= tau(f)` (above), and consumes step 2's output:
   `(8)` gives `|P triangle Q(P)| = o(|P|)`, hence
   `|P cap Q(P)| > |Q(P)|/2`, hence injectivity of `P |-> Q(P)`.
5. **Transport to `J`**: injectivity of the matching makes each fixed
   `Gamma`-word preserve blocks off a negligible set (`(10)` at `:418`),
   and the conjugated words `q_j = tau^(-1) p_(w_j) tau` give an exact
   finite action of `J`.  With `J=V` simple, infinite and finitely
   presented, that action is trivial, contradicting the separation the
   model was assumed to carry.  Hence `Q` has no nontrivial homomorphism
   into a tracial matrix ultraproduct, so `Q` is nonhyperlinear, and
   `leavitt-steinberg-hs-stability-fork` puts `U` on the stable branch.

**Where the unequal-trace difficulty actually lives.**  It is step 2 and
nowhere else.  The median device is not a way of coping with unequal block
traces; it is the proof that they are asymptotically equal, after which
step 4 and `notes/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md` Proposition 11 both
apply.  Anyone attacking the "unequal-trace case" should read that as
"prove `tracial-median-concentration`".

**On the former residual sketch.**  Turning "almost supported in a single
block" into an operator inequality `phi(t) f phi(t)^* >= f - eta` modulo a
small-trace corner was previously flagged here as a hole in prose.  A route
asserts its implication, so carrying a known gap in prose while presenting a
derivation is not allowed; the drift clause is now part of the statement of
`hs-expander-block-decomposition`, where it belongs -- in the permutation
case it is pointwise and free, and in a tracial model it is the same
construction as almost-invariance rather than a separate step.  The
prerequisites of this route now carry everything the argument uses.

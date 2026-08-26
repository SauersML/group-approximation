# A zero-literature Cairn proof of the finite-presentation MF \(\Pi^0_2\) upper bound

**Date:** 2026-08-26  
**Status:** complete mathematical proof and exact Lean implementation design; Lean declarations not yet added.  
**Scope:** the upper bound only. No hardness compiler is asserted here.

## 1. The theorem

For the repository's concrete recursive coding
`PresentationCodes.PresentationCode`, define

```text
OperatorMFCode(P) := IsOperatorMF (PresentationCodes.Carrier P).
```

Then

```text
OperatorMFCode is Pi^0_2,
NonOperatorMFCode is Sigma^0_2.                              (1)
```

More explicitly, there is a total computable Boolean function

```text
MFChecker : PresentationCode -> Nat -> MFAnswerCertificate -> Bool
```

such that

```text
IsOperatorMF (Carrier P)
  iff forall n, exists cert, MFChecker P n cert = true.       (2)
```

The proof uses no real-closed-field decision procedure, quantifier
elimination, eigenvalue algorithm, or literature theorem. Its finite matrix
tests are rational arithmetic plus the power/Frobenius certificates already
proved in `Analysis/OperatorNormCertificate.lean`.

## 2. Why the margins must be open

The existing normal form uses

```text
relator displacement <= 1/(k+1),
tested-word displacement >= 1/2.
```

Those closed inequalities are not directly complete under rational
perturbation: a microstate may lie on the boundary. Replace them by the open
conditions

```text
OpenPasses(P,W,k,M) :=
  (forall r in relators(P), M.len(r) < 1/(k+1)) and
  (forall w in W,          1/3 < M.len(w)).                   (3)
```

and

```text
OpenAnswers(P,W,k) :=
  (exists w in W, WordProblem(P,w)) or
  (exists M, OpenPasses(P,W,k,M)).                            (4)
```

The constants \(1/2\) and \(1/3\) leave a fixed separation margin, while
querying the old theorem at scale \(2k+1\) leaves a relator margin:

```text
1/(2k+2) < 1/(k+1),          1/3 < 1/2.                      (5)
```

### Lemma 2.1 — open microstate normal form

For every finite presentation code \(P\),

```text
IsOperatorMF (Carrier P) iff forall W k, OpenAnswers(P,W,k).  (6)
```

### Proof

Suppose first that the group is operator-MF. Apply
`MFMicrostate.isOperatorMF_iff_forall_answers` to `(W, 2*k+1)`. If its void
branch holds, the same word-problem witness proves the void branch of (4).
Otherwise its microstate satisfies

```text
M.len(r) <= 1/(2*k+2) < 1/(k+1),
1/3 < 1/2 <= M.len(w),
```

and hence satisfies (3).

Conversely, repeat the backward half of
`isOperatorMF_iff_forall_answers`, changing only its fixed weak-MF separation
constant from \(1/2\) to \(1/3\). Given a finite group window \(F\) and
\(\varepsilon>0\), choose raw names `wd(g)` for its elements. Let `W` contain
the words

```text
invWord(wd(h)) ++ wd(g),        g,h in F, g != h,
```

and let `mulWords` contain

```text
invWord(wd(g) ++ wd(h)) ++ wd(g*h),       g,h in F.
```

Every word in `mulWords` is trivial. By
`MFMicrostate.exists_area_bound_list`, one natural number \(N\) bounds all
their displacements by \(N\delta\) whenever every listed relator has
displacement at most \(\delta\). Choose \(k\) with

```text
N/(k+1) <= epsilon.                                            (7)
```

Apply `OpenAnswers(P,W,k)`. Its void branch contradicts the construction of
`W`: a word in `W` is trivial exactly when its two named elements are equal.
Thus a microstate satisfying (3) exists. Reading the microstate on the chosen
names gives a local model on \(F\). Equation (7) and the area bound give its
multiplicative error, while the second clause of (3) gives separation strictly
larger than \(1/3\). Hence the group is weak-MF with fixed positive separation
\(1/3\), and therefore operator-MF. This proves (6). \(\square\)

No new analytic theorem is used here; this is the existing backward proof
with one rational constant changed.

## 3. Executable rational matrices

The checker uses the existing types

```text
RatCode, ComplexCode, MatrixCode.
```

A natural `d` represents matrices on `Fin (d+1)`. Missing entries are zero.
The existing functions `matrixMul`, `conjTranspose`, `matrixSub`, `identity`,
and `wordMatrix` use only primitive-recursive list and rational operations.

Add the following total code operations:

```text
ratPow       : RatCode -> Nat -> RatCode
matrixPow    : Nat -> MatrixCode -> Nat -> MatrixCode
froSqCode    : Nat -> MatrixCode -> RatCode
gramPowCode  : Nat -> MatrixCode -> Nat -> MatrixCode

gramPowCode d A m =
  matrixPow d (matrixMul d (conjTranspose d A) A) (2^m).
```

Their semantic equations are

```text
toRat (ratPow q n) = (toRat q)^n,
toMatrix d (matrixPow d A n) = (toMatrix d A)^n,
toRat (froSqCode d A) = OperatorNormCertificate.froSq (toMatrix d A),
toMatrix d (gramPowCode d A m)
  = ((toMatrix d A)^H * toMatrix d A)^(2^m).                  (8)
```

Define the code for \(1/(k+1)\) by

```text
ratInvSucc(k) := ((1,0),k).
```

Thus `toRat (ratInvSucc k) = 1/(k+1)`.

### Strict upper certificate

```text
upperNormCert(d,k,A,m) :=
  RatLt
    (ratMul (ratOfNat ((dim d)^4))
      (froSqCode d (gramPowCode d A m)))
    (ratPow (ratInvSucc k) (2^(m+2))).                        (9)
```

By (8), `ratLt_iff`, and
`OperatorNormCertificate.opNorm_lt_of_certificate`,

```text
upperNormCert(d,k,A,m) -> ||toMatrix d A|| < 1/(k+1).        (10)
```

Conversely,
`OperatorNormCertificate.exists_certificate_of_opNorm_lt` gives an `m`
satisfying (9) whenever the strict bound in (10) holds.

### Strict lower certificate

Use `ratInvSucc 2`, whose value is \(1/3\):

```text
lowerThirdCert(d,A,m) :=
  RatLt
    (ratMul (ratOfNat ((dim d)^2))
      (ratPow (ratInvSucc 2) (2^(m+2))))
    (froSqCode d (gramPowCode d A m)).                        (11)
```

By (8) and
`OperatorNormCertificate.opNorm_gt_of_certificate`,

```text
lowerThirdCert(d,A,m) -> 1/3 < ||toMatrix d A||.             (12)
```

Conversely,
`OperatorNormCertificate.exists_certificate_of_lt_opNorm` supplies an `m`
whenever the strict bound in (12) holds.

These two natural-number witnesses replace real-closed-field feasibility
completely.

## 4. Coded microstates and word semantics

For a code `P`, dimension `d`, and a list `gens : List MatrixCode`, let

```text
codedGenerator(d,gens,i) := gens.getD i (identity d).
```

Require every supplied matrix code to pass the exact `isUnitary` test. A
missing generator is interpreted as the identity, so every generator selected
by `codedGenerator` is unitary even if the list is short. This defines

```text
codedMicrostate(P,d,gens,hunit) : MFMicrostate.Microstate P.  (13)
```

For a raw word `w`, put

```text
wordDefect(P,d,gens,w) :=
  matrixSub d (wordMatrix d P.1 gens w) (identity d).         (14)
```

The required semantic lemma is

```text
(codedMicrostate P d gens hunit).len w
  = ||toMatrix d (wordDefect P d gens w)||.                  (15)
```

Proof: induction on `w`. `letterMatrix` uses the same reduction modulo
`P.1+1` as `PresentationCodes.letterOf`; a positive letter is the chosen
unitary, a negative letter is its conjugate transpose, and `wordMatrix` folds
by multiplication. Therefore it is exactly the coercion of
`Microstate.hom (wordOf P w)`. Subtracting `identity` is precisely `opLength`.

## 5. Rationalization preserves the open packet

### Lemma 5.1 — word telescoping

Let `U_i` and `V_i` be two tuples of unitary matrices on the same finite
space, and suppose

```text
||U_i - V_i|| < eta
```

for every generator. Then for every raw word `w`,

```text
||eval_U(w) - eval_V(w)|| <= length(w) * eta,                 (16)
```

and consequently

```text
| ||eval_U(w)-1|| - ||eval_V(w)-1|| |
  <= length(w) * eta.                                        (17)
```

For inverse letters, the same generator bound holds because

```text
||U_i^* - V_i^*|| = ||U_i - V_i||.
```

The induction step is

```text
||U A - V B||
 <= ||U(A-B)|| + ||(U-V)B||
 <= ||A-B|| + ||U-V||,
```

since all factors are unitary. Equation (17) is the reverse triangle
inequality.

### Lemma 5.2 — finite open-packet rationalization

If `OpenPasses(P,W,k,M)`, then there are `d`, `gens`, and exact unitarity data
such that

```text
OpenPasses(P,W,k,codedMicrostate(P,d,gens,hunit)).             (18)
```

Proof: use `Microstate.naturalize` and its exact `naturalize_len`. Its positive
cardinality is `d+1` for some `d`. For the finite packet

```text
R = P.relators ++ W,
```

all inequalities in (3) have positive slack. Choose \(\eta>0\) so small that

```text
length(r)*eta < 1/(k+1) - M.len(r)       for every relator r,
length(w)*eta < M.len(w) - 1/3           for every w in W.    (19)
```

Such an \(\eta\) exists because this is a finite family of positive bounds;
one may take half the minimum of each slack divided by `length+1`, with
default value one for an empty family.

For each of the finitely many generator matrices, apply
`RationalMatrixEncoding.exists_unitary_matrixCode_close` with tolerance
\(\eta\). Collect the codes using `List.ofFn`. They are exactly unitary.
Equations (16)--(19) preserve every strict inequality, proving (18).
\(\square\)

This is the only new approximation lemma needed. It uses the repository's
proved rational-unitary density and elementary finite telescoping.

## 6. The finite matrix answer

Let

```text
MatrixAnswer :=
  Nat                       -- d
  x List MatrixCode         -- generator matrices
  x List Nat                -- one upper certificate per relator
  x List Nat.               -- one lower certificate per tested word
```

Define `matrixAnswerCheck(P,W,k,a)` to require:

1. every supplied generator code is exactly unitary;
2. the upper-certificate list has the same length as `P.2`, and corresponding
   entries satisfy

   ```text
   upperNormCert(d,k,wordDefect(P,d,gens,r),m);
   ```

3. the lower-certificate list has the same length as `W`, and corresponding
   entries satisfy

   ```text
   lowerThirdCert(d,wordDefect(P,d,gens,w),m).
   ```

Use equal-length zipped lists, or an equivalent `List.Forall₂`, so missing
certificates are rejected.

By (10), (12), and (15),

```text
matrixAnswerCheck(P,W,k,a)=true
  -> exists M, OpenPasses(P,W,k,M).                           (20)
```

Conversely, Lemma 5.2 supplies rational generator codes, and completeness of
the two norm certificates supplies the two finite lists of natural witnesses:

```text
(exists M, OpenPasses(P,W,k,M))
  -> exists a, matrixAnswerCheck(P,W,k,a)=true.               (21)
```

## 7. The void answer

Let

```text
VoidAnswer := RawWord x WordProblemRE.SearchData.
```

Define

```text
voidAnswerCheck(P,W,(w,p)) :=
  decide(w in W) && WordProblemRE.searchCheck((P,w),p).       (22)
```

The already proved theorem
`WordProblemRE.wordProblemPred_iff_exists` gives exactly

```text
(exists a, voidAnswerCheck(P,W,a)=true)
  iff exists w in W, WordProblem(P,w).                        (23)
```

Both membership in a finite list and `searchCheck` are primitive recursive.

Set

```text
MFAnswerCertificate := Sum VoidAnswer MatrixAnswer.           (24)
```

The Boolean checker dispatches on the sum. From (20)--(23),

```text
exists cert, packetChecker(P,W,k,cert)=true
  iff OpenAnswers(P,W,k).                                    (25)
```

## 8. One natural universal parameter

Let

```text
Challenge := List RawWord x Nat.
```

This type is `Primcodable`. Define the total decoder

```text
challengeAt(n) := (Encodable.decode n).getD ([],0).           (26)
```

and finally

```text
MFChecker(P,n,cert) :=
  packetChecker(P, challengeAt(n).1, challengeAt(n).2, cert). (27)
```

Every challenge occurs: `challengeAt(Encodable.encode(W,k))=(W,k)` by
`Encodable.encodek`. Therefore (6) and (25) give

```text
IsOperatorMF (Carrier P)
 iff forall W k, exists cert, packetChecker(P,W,k,cert)=true
 iff forall n,   exists cert, MFChecker(P,n,cert)=true.       (28)
```

## 9. Computability audit

All certificate types in (24) are built from naturals, booleans, products,
sums, and lists, hence are `Primcodable`.

The following primitive-recursive lemmas complete the executable layer:

```text
primrec_ratPow
primrec_matrixMul
primrec_identity
primrec_conjTranspose
primrec_matrixSub
primrec_generator
primrec_letterMatrix
primrec_wordMatrix
primrec_matrixPow
primrec_froSqCode
primrec_gramPowCode
primrecPred_isUnitary
primrecPred_upperNormCert
primrecPred_lowerThirdCert
primrec_matrixAnswerCheck
primrec_voidAnswerCheck
primrec_challengeAt
computable_MFChecker.                                        (29)
```

`RationalComplexCode` already proves primitive recursiveness of rational and
Gaussian-rational arithmetic. `EffectiveMatrixCodePrimrec.lean` currently
contains only the beginning of (29): `primrec_dim`, scalar operations,
`primrec_entry`, and `primrec_matrixEntryMul`. The rest is routine structural
recursion over bounded ranges and lists, but it must actually be added; the
file's current header overstates what is implemented.

For paired list checks, use equality of lengths together with
`PrimrecRel.forall_mem_list` on `List.zip`. For exact unitarity, check all
indices in `List.range (dim d)` using `ComplexEq`; no semantic matrix equality
appears in the Boolean program.

By `WordProblemRE.rePred_exists_eq_true computable_MFChecker`, the relation

```text
Q(P,n) := exists cert, MFChecker(P,n,cert)=true               (30)
```

is recursively enumerable. Equation (28) and
`ArithmeticalHierarchy.pi02_of_re_family` prove

```text
theorem operatorMFCode_pi02 :
  Pi02 (fun P => IsOperatorMF (Carrier P)).                   (31)
```

Complement duality gives

```text
theorem nonOperatorMFCode_sigma02 :
  Sigma02 (fun P => not IsOperatorMF (Carrier P)).            (32)
```

## 10. Exact Lean file plan

The clean implementation split is:

1. `Computability/EffectiveOperatorNormCode.lean`
   - `ratPow`, `matrixPow`, `froSqCode`, `gramPowCode`;
   - semantic equations (8);
   - `upperNormCert`, `lowerThirdCert` and their soundness/completeness;
   - primitive-recursive declarations for all code operations.
2. `Computability/CodedMicrostateEncoding.lean`
   - `codedMicrostate`, (15), word telescoping, and Lemma 5.2.
3. `Computability/MFRecognitionPi02.lean`
   - `OpenPasses`, `OpenAnswers`, Lemma 2.1;
   - certificate types and Boolean checkers;
   - (25), (28), `operatorMFCode_pi02`, and the Sigma-two complement.
4. Add the two new closed endpoints to `Endpoint/MFRecognitionAudit.lean`
   only after they compile without leading hypotheses.

No declaration in this plan accepts a real-closed-field solver, a density
theorem, or a norm decision oracle as a parameter. Rational-unitary density
and both directions of the norm certificate are already closed repository
theorems.

## 11. Dependency audit

The proof consumes only:

- `MFMicrostate.isOperatorMF_iff_forall_answers`;
- `MFMicrostate.exists_area_bound_list`;
- `Microstate.naturalize_len`;
- `RationalMatrixEncoding.exists_unitary_matrixCode_close`;
- `OperatorNormCertificate.opNorm_lt_of_certificate` and its converse;
- `OperatorNormCertificate.opNorm_gt_of_certificate` and its converse;
- `WordProblemRE.wordProblemPred_iff_exists` and
  `rePred_exists_eq_true`;
- elementary finite-list recursion and operator-norm inequalities.

There is no literature input and no hidden decision theorem.

## Conclusion

The upper bound does not require deciding arbitrary semialgebraic matrix
feasibility. Open margins reduce the problem to searching over dense exact
rational unitaries, while natural power/Frobenius witnesses make both strict
operator-norm comparisons decidable. The resulting checker has the exact
truth condition (2), establishing the finite-presentation MF \(\Pi^0_2\)
upper bound once the explicit Lean plumbing in (29) is implemented.

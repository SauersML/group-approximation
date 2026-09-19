# A zero-literature Cairn proof of Higman Section Five `CodeRE`

**Date:** 2026-08-26  
**Status:** complete mathematical proof and exact Lean implementation design; no Lean declaration has been added.  
**Scope:** only the `Transport.CodeRE` leaf in `Higman/TransportFive.lean`.

## 1. Exact target

The open structure is

```lean
structure GroupApproximation.Higman.Transport.CodeRE where
  code_re : ∀ (n : ℕ)
      (N : Subgroup (FreeGroup (Fin (n + 1)))),
    REPred (fun v : RawWord => rawToFree n v ∈ N) →
      REset (codeSet n N)
```

where

```text
RawWord       = List (Nat × Bool)
Seq.E         = ℤ →₀ ℤ
seqOfList l   = Σ (j,z) in l, Finsupp.single j z
REset B       = REPred (fun l : List (ℤ × ℤ) => seqOfList l ∈ B)

codeSet n N =
  {f | ∃ v : RawWord,
       rawToFree n v ∈ N ∧ f = codeSeq n v 0}.
```

Thus, after fixing `n`, `N`, and

```text
P(v) := rawToFree n v ∈ N,
```

the exact goal is

```text
REPred (fun l : List (ℤ × ℤ) =>
  ∃ v, P(v) ∧ seqOfList l = codeSeq n v 0).             (1)
```

There is no normality hypothesis and none is needed.

## 2. Why the obvious image proof needs one extra checker

The map `seqOfList` is surjective but not injective. For example,

```text
[(0,1),(0,-1)]
```

and the empty list code the same zero sequence. Consequently, it is not enough
to enumerate one canonical list for each `codeSeq n v 0`: `REset` tests every
list code of the same sequence.

The required repair is finite. Two list codes are equal as sequences exactly
when their coordinate sums agree at every index mentioned by either list.
That criterion is decidable and primitive recursive.

## 3. Canonical list code for `codeSeq`

For `x = (i,s) : Nat × Bool`, define

```text
sign(s) = if s then 1 else -1,

entry(n,k,x) =
  ( (k : ℤ) * ((n : ℤ) + 1) + ((i % (n+1) : Nat) : ℤ),
    sign(s) ).
```

Define a list-valued traversal carrying the current block number:

```text
codeListFrom n []             k = []
codeListFrom n ((i,s) :: v)  k =
  entry(n,k,(i,s)) :: codeListFrom n v (k+1).

codeList n v = codeListFrom n v 0.
```

### Lemma 3.1 — canonical-code correctness

For all `n`, `v`, and `k`,

```text
seqOfList (codeListFrom n v k) = codeSeq n v k.               (2)
```

### Proof

Induct on `v`. For the empty word, both sides are zero. For
`(i,s) :: v`, the definition of `seqOfList` gives

```text
seqOfList (entry(n,k,(i,s)) :: codeListFrom n v (k+1))
 = Finsupp.single (pos n k i) (sign s)
     + seqOfList (codeListFrom n v (k+1)).
```

The induction hypothesis changes the last term to `codeSeq n v (k+1)`, and
the result is the defining equation `codeSeq_cons`. This proves (2). In
particular,

```text
seqOfList (codeList n v) = codeSeq n v 0.                     (3)
```

### Lemma 3.2 — effectivity of the canonical code

For fixed `n`, the map

```text
v ↦ codeList n v
```

is primitive recursive.

### Proof

An implementation using only primitive-recursion combinators already exercised
in the repository is explicit. Put

```text
step_n (i,s) (k,L) = (k+1, entry(n,k,(i,s)) :: L),

stateFrom n k v =
  v.reverse.foldr step_n (k, []),

codeListFrom n v k = (stateFrom n k v).2.reverse.
```

Because `foldr` associates from the right, applying it to `v.reverse` processes
the letters of `v` from left to right. The accumulator therefore assigns block
numbers `k,k+1,...`; the second reverse restores the original letter order.
A direct induction on `v` gives the recursive equations displayed above.

At each step the computation uses only:

```text
k + 1,
i % (n+1),
k * (n+1) + i % (n+1),
Nat → Int,
a Boolean branch between the constants 1 and -1,
list cons.
```

All natural-number operations displayed are primitive recursive. List reverse
and `Primrec.list_foldr` are already available. The integer
coordinate can be computed as

```text
((k * (n+1) + i % (n+1) : Nat) : Int),
```

which equals `pos n k i`; `Higman.primrec_int_natCast` supplies the cast.
Primitive-recursive pairing and projections compute the state. Thus the
displayed reverse/fold/reverse program proves `Primrec (codeList n)`.

This proof deliberately avoids primitive-recursive integer multiplication and
modulus: all arithmetic is done in `Nat`, and the nonnegative answer is cast
once at the end.

## 4. Equality of arbitrary sequence codes

The repository already defines the computable coordinate evaluator

```text
Seq.evalCode l j = Σ p in l, if p.1 = j then p.2 else 0
```

and proves

```text
Seq.seqOfList_apply l j : seqOfList l j = Seq.evalCode l j.   (4)
```

For lists `l,m : List (ℤ × ℤ)`, define

```text
sameSeqCode(l,m) =
  (l ++ m).all (fun p =>
    decide (Seq.evalCode l p.1 = Seq.evalCode m p.1)).         (5)
```

Repeated indices and entries of value zero are intentionally retained.

### Lemma 4.1 — equality-checker correctness

```text
sameSeqCode(l,m) = true ↔ seqOfList l = seqOfList m.         (6)
```

### Proof

Assume first that the Boolean is true. Extensionality reduces equality of the
two finitely supported sequences to equality at an arbitrary `j : ℤ`.

If some pair `p` in `l ++ m` has `p.1 = j`, `List.all_eq_true` applied to that
pair gives

```text
Seq.evalCode l j = Seq.evalCode m j.
```

Equation (4) gives the required coordinate equality.

If no pair in `l ++ m` has first coordinate `j`, then no pair of either `l` or
`m` has first coordinate `j`. By `Seq.evalCode_eq_zero_of_not_mem`, both
evaluations at `j` are zero. Equation (4) again closes the coordinate equality.

Conversely, suppose `seqOfList l = seqOfList m`. For every pair `p` in
`l ++ m`, evaluate this function equality at `p.1` and rewrite with (4). The
corresponding equality test is true, so `List.all_eq_true` proves (5).

### Lemma 4.2 — effectivity of the equality checker

`sameSeqCode` is primitive recursive.

### Proof

Integer addition is primitive recursive by `Higman.primrec2_int_add`, hence
`Seq.primrec_evalCode Higman.primrec2_int_add` computes `evalCode`.
Primitive-recursive list append, list map/fold, pair projections, equality on
the `Primcodable` type `Int`, `decide`, and Boolean conjunction compute (5).

No equality decision on `Finsupp` is used.

## 5. The r.e. checker

Assume

```text
hP : REPred P.
```

By the repository's proved Kleene normal form
`Higman.exists_primrec_of_rePred`, choose

```text
F : RawWord → Nat → Bool
```

such that

```text
Primrec₂ F,
P(v) ↔ ∃ t, F v t = true.                                  (7)
```

For an input list code `l` and certificate `(v,t)`, define

```text
codeCheck n F l (v,t) =
  F v t && sameSeqCode(l, codeList n v).                         (8)
```

By Lemmas 3.2 and 4.2 and closure of primitive-recursive functions under
composition, pairing, and Boolean conjunction, `codeCheck n F` is computable
(indeed primitive recursive). Therefore
`WordProblemRE.rePred_exists_eq_true` gives

```text
REPred (fun l => ∃ q : RawWord × Nat,
  codeCheck n F l q = true).                                    (9)
```

### Lemma 5.1 — checker semantics

For every list `l`,

```text
(∃ q, codeCheck n F l q = true)
↔ seqOfList l ∈ codeSet n N.                               (10)
```

### Proof

Expand the certificate `q` as `(v,t)`, rewrite `Bool.and_eq_true`, then use
(6), (3), and (7):

```text
∃ v t, F v t = true
      ∧ sameSeqCode(l, codeList n v) = true

↔ ∃ v, P(v)
      ∧ seqOfList l = seqOfList (codeList n v)

↔ ∃ v, rawToFree n v ∈ N
      ∧ seqOfList l = codeSeq n v 0

↔ seqOfList l ∈ codeSet n N.
```

The last equivalence is exactly the definition of `codeSet` instantiated at
`f = seqOfList l`.

## 6. Assembly of `CodeRE`

Define

```text
codeREProof : Transport.CodeRE :=
{
  code_re := by
    intro n N hP
    obtain ⟨F, hF, hFspec⟩ := exists_primrec_of_rePred hP
    obtain hsearch :=
      WordProblemRE.rePred_exists_eq_true
        (primrec_codeCheck n hF).to_comp
    exact hsearch.of_eq (codeCheck_iff n N hFspec)
}
```

Here `primrec_codeCheck` packages Lemmas 3.2 and 4.2, and
`codeCheck_iff` is Lemma 5.1. Unfolding `REset` makes the final target exactly
the right side of (10).

This constructs an inhabitant of the exact repository structure with no added
axiom, no normality assumption, and no literature theorem.

## 7. Lean declaration plan

The smallest implementation can live in a new file, for example

```text
GroupApproximation/Higman/TransportCodeRE.lean
```

and import:

```text
GroupApproximation.Higman.TransportFive
GroupApproximation.Higman.HigmanCodingDictionary
GroupApproximation.Higman.IntPrimrec
```

It should add only these declarations:

```text
codeListFrom
codeList
seqOfList_codeListFrom
seqOfList_codeList
primrec_codeList

sameSeqCode
sameSeqCode_eq_true_iff
primrec_sameSeqCode

codeCheck
primrec_codeCheck
codeCheck_eq_true_iff

codeRE
```

The reverse/fold/reverse implementation in Lemma 3.2 avoids any need for a
special accumulator-recursion API.

## 8. Dependency and blocker audit

The proof uses only results already proved in the repository:

```text
exists_primrec_of_rePred
WordProblemRE.rePred_exists_eq_true
Seq.seqOfList_apply
Seq.evalCode_eq_zero_of_not_mem
Seq.primrec_evalCode
primrec2_int_add
primrec_int_natCast
```

plus elementary primitive-recursion closure rules and list extensionality.

**Genuine blocker:** none. The available `Primrec.list_reverse` and
`Primrec.list_foldr` operations implement the only stateful traversal needed.

Closing this leaf does **not** close `TransportSectionFive`: the independent
`CompletionLemma` and `UnConjugation` leaves remain.

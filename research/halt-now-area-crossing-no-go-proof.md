---
rg: 2
id: halt-now-area-crossing-no-go-proof
kind: route
title: Separate the halting contradiction from existence of an accepted matrix witness
target: halt-now-certificate-area-still-needs-a-crossing-envelope
requires:
  - dimension-kleene-threshold-needs-amplification-envelope
  - posthalt-clifford-cannot-power-reverse-kleene
---

Fix the recursion-theorem index and run the proposed search.  For every
candidate `U` that it examines, the complete hypothetical halt computation is
finite, so the proposed compiler may compute its finite derived certificate
and the number `A(U)`.  Strict inequality `(HNA1)` is therefore a legitimate
semidecision test.

If the test succeeds and the machine halts, dimension-matched soundness for
that same halt transcript contradicts the marked separation of `U`.  Hence
the usual recursion argument proves `(HNA2)`.  Notice that no part of this
argument proves that a hyperlinear microstate succeeds in the test.

For a tuple of dimension `d`, include every legal tensor amplification and
halt payload `q` and define the best window

```text
Theta(U)=sup_(k,q) b/A(U tensor I_k,q).                 (PRO1)
```

The search accepts some amplification of `U` exactly when its unchanged
normalized-HS defect is below `Theta(U)`.  This is the candidate-dependent
version of the amplification envelope.  If `Theta` has a positive lower
bound on all sufficiently separated candidates, the old Kleene proof works.
More generally it works if every possible canonical microstate profile
crosses `Theta` once.  Without that assumption, convergence of defects to
zero supplies no comparison with `Theta`.

Numerically, on any subsequence with `Theta(U_n)->0`, the profile

```text
Def(U_n)=sqrt(Theta(U_n))
```

tends to zero and misses every acceptance window.  This is a logical defect
profile, not a claim that an arbitrary prescribed profile is realized by a
particular presentation; it proves that hyperlinearity alone does not imply
the missing comparison.  If `Theta` does not approach zero, its positive
subsequence is precisely the pre-halt envelope, so the proposal has not
removed the modulus.

Now suppose the search directly checks the derived multiplication table
instead.  Let `W_m` enumerate the increasing finite derived word windows and
let `x_(n,m)` be their maximal evaluation error on the `n`th candidate.
Canonical microstate convergence asserts only

```text
for every fixed m, x_(n,m)->0.
```

The challenge chosen after reading candidate `n` uses an index `m(n)` large
enough to exceed its dimension.  No diagonal conclusion for
`x_(n,m(n))` follows; the displayed triangular array is an explicit
counterexample.  Freezing `m` first restores convergence, but the eventual
microstate dimension may then exceed the frozen Clifford capacity.  Enlarging
`m` restarts the same chase.

Finally, runtime makes the proposed window potentially worse.  If simulating
the halt transcript to time `t` gives area `A(t,d)` growing with `t`, a late
discovery is tested against a smaller reciprocal.  One cannot freeze the
earlier transcript and halt later: the actual halting computation is the
later transcript.  Printing a payload early does not help unless the compiler
activates before genuine halting, which changes the NONHALT semantics.

This proves the no-go and identifies the only positive exception: a verified
crossing/amplification envelope known independently of hyperlinearity.

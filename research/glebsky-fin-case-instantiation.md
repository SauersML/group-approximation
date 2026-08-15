---
rg: 2
id: glebsky-fin-case-instantiation
kind: claim
title: In the Fin case the separated sets are finite-window projections, and the generic length is forced
distinct_from:
  glebsky-manufactured-invariant-length: that gives the general form of the manufactured length; this identifies what its two sets actually are for weak soficity, and why no better length is available there
  glebsky-weak-soficity-is-metric-free: that reports the 2023 permanence proof produces no metric; this pins the 2017 construction's inputs in the case that permanence theorem uses
  finite-window-decoder: that is a mixed-relator-route claim about decoding one-sided Leavitt maps on paired-radical label spaces in the atlas; this is an external-literature instantiation of Glebsky's Proposition 5 and Lemma 3 for the class Fin. The shared vocabulary ("finite window") is coincidental — that node's windows are endomorphism decoding windows in the Leavitt atlas, these are truncation indices of a projection onto finitely many coordinates of a direct product of finite groups.
---

Read from arXiv:1506.06940v2 (J. Algebra 477 (2017) 147--162) on 2026-08-14,
answering `cairn-survivor`'s question whether the construction's freedom
reaches into the finite sub-product where they have localized the problem.

## The hypothesis of Corollary 19 is free for `Fin`

Corollary 19 needs `K subset of Fin` with `K.approx = (prod K).approx`, where
`prod K` adjoins finite direct products.  For `K = Fin` that is automatic:
finite direct products of finite groups are finite, so `prod Fin = Fin`.
Corollary 6 records the same conclusion from the compactness side ("it is
true for `K = Nil, Sol, Fin`, or class of all compact groups"), and line 67
of the paper fixes the terminology: "`Fin`-approximable groups are called
weakly sofic".

## The two sets are finite-window projections

Proposition 5 is where the approximation is produced.  Let `X` be a closed
subgroup of `prod_(i in N) H_i` with each `Pr_i(X) in K`, and `N` normal in
`X`; then `X/N` is `prod K`-approximable.  Its proof, given finite
`Phi` in `X` and `n`:

```text
Phi_N = Phi ∩ N,      Phi_0 = Phi \ N,      C_n(Phi_N, X) ∩ Phi_0 = ∅
```

(the intersection is empty because `C_n(Phi_N,X)` lies in `N`, `N` being
normal).  Compactness of `C_n(Phi_N,X)` gives an open `U` containing `Phi_0`
disjoint from it, and hence some `k` with

```text
C_n(Pr_1^k(Phi_N), Pr_1^k(X)) ∩ Pr_1^k(Phi_0) = ∅.
```

So the approximating homomorphism is the **finite-window projection**
`Pr_1^k : X -> Pr_1^k(X)`, and feeding this into Lemma 3:

```text
H  =  Pr_1^k(X)              the finite window
X  =  Pr_1^k(Phi ∩ N)        the ERROR set   -> length 1/n
Y  =  Pr_1^k(Phi \ N)        the SEPARATED set -> length 1
```

**The freedom reaches into the finite sub-product because the construction
lives there.**  What is *not* free: given `Phi` (forced by the test) and `n`,
the error set is determined as `Pr_1^k(Phi ∩ N)`, and the length is then the
capped conjugate-word-length of `glebsky-manufactured-invariant-length` in
that set.  The genuinely free parameters are `n` and `k` (`k` may always be
enlarged).  So the design problem is not "choose a length" but "compute the
character expansion of a determined one, as `n,k` vary".

## Why `Fin` gets the generic length and soficity does not

For `K = Alt` or `Sym` the paper does **not** use Lemma 3's construction at
all.  It uses the normalized Hamming length (Definition 8, `H` = the class of
normalized Hamming length functions) together with two `Alt`-specific tools:

> **Lemma 10.** Let `A` be an alternating group, `X` in `A` and
> `y` not in `C_n(X,A)`.  Then `||y||/||x|| >= (n-1)/16` for any `1 != x in X`.

whose proof is "a manifestation of the fact that in a finite simple group
powers of a conjugacy class cover the group 'almost as fast as possible'";
and **Lemma 11**, the amplification trick `h |-> h^(⊗r)` on `[m]^r` with
`1 - ||h^(⊗r)|| = (1 - ||h||)^r`, which boosts separation to `||psi(y)|| >= 1/2`
while keeping `||psi(x)|| < 1 - (1/4)^(1/n)`.

**Lemma 10 has no analogue for general finite groups** — its proof consumes
simplicity.  That is why weak soficity must fall back on the generic capped
conjugate-word-length: the genericity is forced, not incidental.

`[MY INFERENCE]` This is a concrete form of the sofic/weakly-sofic gap, and it
lines up with the Hilbert-embeddability criterion exactly:

- **sofic**: the length is Hamming on `A_m`, which is Hilbert embeddable —
  recovering `sofic implies hyperlinear`;
- **weakly sofic**: the length is a capped conjugate-word-length on an
  arbitrary finite group, with no covering theorem available to convert it
  into Hamming-comparable data.

Glebsky's own remark in the 2023 paper — "not all bi-invariant metric on a
finite group is a restriction of a corresponding Hamming metric" — is the
abstract shadow of this concrete asymmetry: Lemma 10 is precisely the tool
that would perform such a conversion, and it exists only for simple groups.

## Note on separation, correcting an earlier reading

In the `Alt` case separation `>= 1/2` is achieved by **amplification**
(Lemma 11), not by truncation.  The truncation-is-the-separation-mechanism
observation on `glebsky-manufactured-invariant-length` is correct for the
generic Lemma 3 construction, hence for `Fin`, but it is not how the sofic
case gets its separation.  Both statements stand in their own case.

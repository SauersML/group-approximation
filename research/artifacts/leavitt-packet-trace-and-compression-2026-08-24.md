# The Leavitt direct-finiteness lane after the packet-trace obstruction

Checked and integrated 2026-08-24.  This artifact records a user-supplied
mathematical audit of the Cairn Kaplansky lane and two exact verifier programs.
It does **not** claim a resolution of Kaplansky's conjecture.  The remaining
new implication is the finite-support equivalence `e ~ f` described below.

Throughout,

```text
R = L_(F_2)(1,2),        G = R^x,        S = F_2[G],
pi : S -> R
```

is evaluation.  The notation for `e`, `f`, the rank-three lifts `t~,s~`, the
corner factors `A,B`, the defect `Delta`, and the packet `P_x` agrees with
`one-nonnormal-packet-corner-correction-2026-08-21.md`.

## 1. Exact p-adic reformulation

For a prime `p` and a group `G`, let

```text
C_p(G) = c_0(G,Z_p)
```

with the supremum norm and convolution.  Finite-support functions are dense,
so convolution extends continuously and makes this a non-Archimedean Banach
algebra.  Then

```text
F_p[G] is directly finite  <=>  C_p(G) is directly finite.       (1)
```

The same assertion holds after applying `M_n` for every finite `n`.

Assume first that `C_p(G)` is directly finite and `ab=1` in `F_p[G]`.
Choose finite-support lifts `A,B in Z_p[G]`.  Write `AB=1+pC`.  Since
`||pC||_p<1`, the Neumann series makes `AB` invertible in `C_p(G)`.  Thus

```text
B' = B(AB)^(-1),        AB'=1.
```

Direct finiteness gives `B'A=1`.  Reduction modulo `p` sends `(AB)^(-1)` to
`1`, hence sends `B'` to `b`, and gives `ba=1`.

Conversely suppose `F_p[G]` is directly finite and `AB=1` in `C_p(G)`.
Reduction modulo `p` has finite support because a `c_0` function has only
finitely many coefficients of norm one.  Hence

```text
bar(A)bar(B)=1,        bar(B)bar(A)=1.
```

Put `D=1-BA`.  Then `D in pC_p(G)`, while `BA` and therefore `D` are
idempotent.  If `D` were nonzero, submultiplicativity would give

```text
0 < ||D||_p < 1,       ||D||_p = ||D^2||_p <= ||D||_p^2,
```

an impossibility.  Thus `BA=1`.  Entrywise reduction, the matrix supremum
norm, and the same idempotent argument prove the matrix version.

This is an exact equivalence, not a completion method for evading the
positive-characteristic problem.

## 2. Strict idempotent compression criterion

Let `T` be a unital ring, let `p != 0` be idempotent, and suppose a unit `w`
strictly compresses it:

```text
q = w p w^(-1),        pq=qp=q,        q != p.          (2)
```

Set

```text
x = p w^(-1) q,        y = q w p.
```

Then `xy=p` and `yx=q`.  Both elements lie in `pTp`, so padding gives

```text
X=x+(1-p),        Y=y+(1-p),
XY=1,             YX=q+(1-p) != 1.                     (3)
```

Therefore `T` is not directly finite.  More generally, (3) needs only a
strict Murray--von Neumann equivalence: idempotents `q<p` and elements
`x in pTq`, `y in qTp` with `xy=p`, `yx=q`.

For Cairn's explicit Leavitt corner,

```text
e = [g]+[g^2],              f = [1]+[u]+[v]+[g],
f < e,                      pi(e)=1,        pi(f)=s_0t_0.
```

Thus the concrete open target is

```text
e ~ f in S:  find x in eSf and y in fSe with xy=e and yx=f.       (4)
```

This target is now refuted by the canonical coefficient trace.  If
`tau:S->F_2` denotes coefficient of the identity, then `tau(ab)=tau(ba)` for
all `a,b in S`.  Since `g,g^2` are nonidentity while the support of `f`
contains the identity exactly once,

```text
tau(e)=0,                    tau(f)=1.                  (4a)
```

Therefore no `x,y` anywhere in `S` can satisfy `xy=e`, `yx=f`.  The narrower
corner supports in (4) cannot help.  See
`group-algebra-coefficient-trace-separates-leavitt-corners`.

## 3. Global trace obstruction for the two-packet equation

Let `tau:S->F_2` be coefficient of the identity.  The two linear packet terms
obey, for every `x in G`,

```text
tau(A P_x)=0,             tau(P_x B)=0.                 (5)
```

This is not a bounded-search assertion.  Here is the complete reduction.
If an identity monomial occurred in `AP_x`, a conjugate `x sigma x^(-1)` of
a nontrivial constant transposition `sigma in GL_2(F_2)` would lie in the
finite set `supp(e) supp(A)^(-1) supp(e)`.  The symmetric statement for
`P_xB` uses `supp(e) supp(B)^(-1) supp(e)`.

Exact Bergman normal form classifies the involutions in the first finite set
as the identity and the following six elements, for `i=0,1`:

```text
I + [[0,t_i],[0,0]],
I + [[0,0],[t_i,0]],
I + t_i [[1,1],[1,1]].                                  (6)
```

For the second set, replace `t_i` by `s_i`.  The finite classification is
asserted exactly by `check_linear_identity_invariant.py`, using the same
Bergman normal-form implementation as the existing corner verifier.

None of the six values in either list is conjugate in `GL_2(R)` to a constant
transposition.  Indeed, for a constant transposition, `N=sigma-I` is a
rank-one square-zero endomorphism of the right module `R^2` and

```text
im(N) = ker(N).                                           (7)
```

Conjugation preserves (7).  For `a=t_i`, one has `aR=R` because `t_i s_i=1`,
but `rAnn(a)` is nonzero because `t_i s_(1-i)=0`.  For `a=s_i`, one has
`rAnn(a)=0` because `t_i s_i=1`, but `aR != R`: a right inverse would have to
be `t_i`, contradicting `s_i t_i != 1`.  For each upper, lower, and symmetric
nilpotent in (6), these facts make `im(N)` a proper subset of `ker(N)`.  This
proves (5).

The explicit defect has `tau(Delta)=1`, also checked by the base corner
verifier.  Applying `tau` to

```text
A P_y + P_x B + P_x P_y = Delta                          (8)
```

and using (5) gives the global necessary condition

```text
tau(P_x P_y)=1.                                           (9)
```

Every packet is self-adjoint.  In characteristic two,

```text
tau(P_x P_y) = |supp(P_x) intersect supp(P_y)| mod 2.     (10)
```

Thus every solution of (8) has odd packet-support intersection.  The diagonal
`x=y` is impossible, since

```text
tau(P_x^2)=epsilon(P_x)=0.
```

## 4. Independent mixed-root exhaustion through length four

The eight elementary root involutions are

```text
U_(s_0), L_(s_0), U_(s_1), L_(s_1),
U_(t_0), L_(t_0), U_(t_1), L_(t_1).
```

Exact Bergman reduction gives 1,254 distinct genuinely mixed elements through
word length four.  Their Cartesian square contains 1,572,516 ordered pairs.
Condition (10) leaves 1,394 pairs; direct evaluation of (8) on precisely those
pairs gives no solution.  Through length three there are 204 candidates and
41,616 ordered pairs, of which 208 survive (10), again with no solution.

`filter_two_packet_len4.py` is a replayable full exhaustion of exactly this
finite family.  It asserts both candidate counts, both survivor counts, the
global linear-trace conclusion on the enumerated packets, and nonvanishing of
the complete residue for every survivor.  It deliberately says nothing about
longer words or conjugators outside this eight-root family.

## 5. Recursive and symmetric-compressor no-go results

The recursion `lambda:S->fSf`, `lambda(1)=f<1`, does not imply failure of
direct finiteness.  The existing Cairn nodes prove more concretely that
`q_n=lambda^n(z)` lies in a finite group algebra `F_2[H_n]`; every finite
combination of recursive packets therefore remains in a directly finite
subring.  A proper self-similar corner is not a proper isometry.

There is a second exact no-go in the nine-leaf compressor geometry.  For its
two compressors `u,v`, put `c=v^(-1)u`.  The prefix tables show that `c` fixes
every `alpha_i` cylinder and swaps the two auxiliary three-cylinder families.
Thus `c^2=1` and `c` centralizes the embedded elementary subgroup `Gamma`.
In characteristic two,

```text
n=1+[c],        n^2=0,        [u]+[v]=[v]n.
```

Also `[u^(-1)]+[v^(-1)]=n[v^(-1)]`.  Hence for every
`a in F_2[Gamma]`,

```text
([u]+[v]) a ([u^(-1)]+[v^(-1)])
  = [v] n a n [v^(-1)]
  = 0.                                                     (11)
```

Summing the two compressors creates a square-zero packet, not a proper
isometry.

## 6. Correction to the matrix-amplification statement

The scalar/constant construction proves an injective nonunital map

```text
M_2(S) -> eSe.
```

It does not prove that the image equals all of `eSe`.  The embedding alone is
enough for the stable/direct-finiteness equivalence: transport a matrix
witness into its supported corner and pad by the complementary idempotent.
The Cairn claim and proof have been narrowed accordingly.

## 7. External-status boundary

On 2026-08-24 the public abstract of Zongmin Liu's preprint, *Kaplansky's
Direct Finiteness Conjecture for the First Non-Sofic Group: Unit Sums, a
Stratification, and Complete Bounded Searches* (Zenodo record 21840947,
published 2026-08-05), was checked.  It independently states the surjectivity
of evaluation, structural constraints on counterexamples, exact bounded
searches, and no counterexample.  This ingestion did not compare every lemma
or the released code against (5)--(10), so it makes no priority claim for the
packet-trace theorem.

Bradford--Fournier-Facio, *Hopfian wreath products and the stable finiteness
conjecture*, Math. Z. 308 (2024), records both the universal equivalence of the
direct- and stable-finiteness conjectures and the reduction of arbitrary
characteristic-`p` fields to `F_p`.  Those universal reductions are context;
the p-adic equivalence above is proved directly here.

Sources:

- <https://zenodo.org/records/21840947>
- <https://link.springer.com/article/10.1007/s00209-024-03589-3>

## Honest frontier

No pair solving (8) is supplied.  Equivalence (4) is impossible by (4a), so
it is no longer a live finite-support target.  The surviving direct-finiteness
lane must use a pair of products with equal canonical coefficient trace; in
the packet equation this leaves (8) under the odd-intersection condition
(10).  The earlier theorem remains the global trace/odd-intersection
obstruction, and the finite result remains the independent mixed-root
exhaustion through length four.

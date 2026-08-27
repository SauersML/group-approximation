# 2026-08-18 — Exact-support sparsification at the LCS/nonhyperlinear boundary

**Status:** source-verified boundary plus an elementary new sparsification
criterion.  No nonhyperlinear group is claimed here.

## 1. The exact literature endpoint

Paddock--Slofstra, *Satisfiability problems and algebras of boolean constraint
system games* (arXiv:2310.07901), Lemma 5.7 and Proposition 5.8, give the
correct groupification target.  For a linear system `Ax=b` with solution group
`Gamma(A,b)` and central involution `J`:

```text
tracially satisfiable  <=>  J != 1 in Gamma(A,b),
R^U-satisfiable        <=>  J is nontrivial in approximate representations.
```

Consequently there exists a tracially satisfiable but non-`R^U` linear system
if and only if there exists a finitely presented nonhyperlinear group.

The distinction from ordinary matrix-unsatisfiability matters.  A group can
have no exact low-dimensional representation and still admit arbitrarily good
high-dimensional approximate representations.  The marked `J` has to be
killed by **all sufficiently accurate** finite-dimensional almost
representations.

## 2. Exact-support sparsification criterion

Fix a free group on finitely many generators, a distinguished word `j`, a
finite relator menu `S`, and a probability distribution `mu` on `S`.  Assume
there is a tracial von Neumann algebra `(M,tau)` and a unitary assignment `rho`
of the free generators such that

```text
d_2(rho(j),1) >= delta0 > 0.
```

Let

```text
E = { r in S : rho(r)=1 exactly },
g = mu(E).
```

For a finite-dimensional unitary assignment `U`, call it `delta`-marked when
`d_2(j(U),1)>=delta`.  Let `K_delta` be the compact finite trace-profile space
for the word menu

```text
W = S union {j}.
```

Fix `0<eps<eps_plus` and a profile-net radius `eta` with

```text
2 eta < eps_plus^2-eps^2.
```

For `z in K_delta` set

```text
p(z)=Pr_(r~mu)[2-2 z_r <= eps_plus^2],
q=sup_(z in K_delta) p(z).
```

If

```text
g > q,
```

then for sufficiently large `m`, because the profile net has finite size `N`,

```text
g^m > N q^m.
```

Sample `m` relators independently from `mu`.

- With probability `g^m`, every sampled relator lies in `E`; on this event
  `rho` is an exact tracial representation of the sampled presentation and
  keeps `j` nontrivial.
- By finite-moment sparsification, with probability at most `Nq^m` there is a
  finite-dimensional `delta`-marked tuple satisfying all sampled relators to
  defect `eps`.

So some sampled finite presentation has an exact tracial representation with
`j` nontrivial but has no sufficiently accurate finite-dimensional almost
representation keeping `j` separated.  Equivalently `j` is trivial in
approximate representations of that presentation.  This gives a finitely
presented nonhyperlinear group.  If the relator menu is LCS syntax and `j=J`,
this is exactly the Paddock--Slofstra endpoint.

This criterion is strictly weaker than a perfect-completeness compiler: the
whole menu need not be exactly satisfied by the tracial assignment.  It only
asks that the **measure of exactly satisfied checks** exceed the maximum
measure that a marked finite-dimensional approximate assignment can satisfy.
That inequality is the new target.

## 3. Why the Taller--Vidick long-code test is close

Taller--Vidick, *Approximating the quantum value of an LCS game is RE-hard*
(arXiv:2507.22444), Definition 4.1 samples an independent noise function
`mu(y)` with `Pr[mu(y)=1]=1-epsilon`.  Their completeness proof, Lemma 4.2,
starts from a perfect synchronous BCS strategy and constructs the output LCS
strategy.  On page 21, the proof isolates the loss exactly: for every active
long-code outcome `phi`, the output equation is accepted whenever the sampled
noise has `mu(phi)=1`; averaging this condition gives the factor `1-epsilon`.
Their soundness Proposition 4.1 gives a constant synchronous-value gap whenever
the repeated input game has sufficiently small quantum value.

So the present criterion suggests a route strictly between their current
`1-epsilon` completeness and the still-open perfect-completeness LCS compiler:

> prove that, for a suitable tracially satisfiable BCS source and a suitable
> reweighting/derandomization of the long-code checks, the mass of checks that
> are **operator-exact** in the tracial strategy is larger than the maximum
> mass satisfiable by a marked finite-dimensional approximate assignment.

Call this the **exact-support gap**.

The unmodified verifier does not visibly supply the needed inequality.  If an
equation has active support `T`, the sufficient event that the noise equals
`+1` on every active `phi in T` has probability `(1-epsilon)^|T|`, which may be
much smaller than the finite-dimensional soundness value.  Thus simply
sparsifying the existing verifier is not a proof.  The next work is to preserve
soundness after conditioning/reweighting toward the exact-support checks, or to
redesign the noise test so that exact-support mass stays large.

## 4. Why recent gadget theory is relevant

Paddock--Slofstra give algebra-preserving reductions among BCS languages, but
LIN is exactly the exceptional language where a general tracial/non-`R^U`
gap cannot simply be imported without solving the group problem itself.
Taller--Vidick provide a quantitative BCS-to-LCS test, but with imperfect
completeness.  Lin's 2025/26 commuting-operator compression paper explicitly
lists extending compression to linear-constraint-system games as an open
problem.

Culf--van Dobben de Bruyn--Zeman, arXiv:2604.01408, now characterize robust
commutativity gadgets in the finite-dimensional, quantum-approximate and
commuting-operator models through weighted quantum-polymorphism algebras, and
show robust gadget existence is equivalent to the corresponding non-robust
existence.  This gives a modern language for asking whether the
conditioning/reweighting needed by the exact-support gap can be made
quantum-sound without accidentally forcing the commuting-operator and
approximate models to coincide.

## 5. Concrete theorem target

A full finish via this lane would consist of an explicit finite BCS source and
an explicit finite LCS check distribution with a marked central involution `J`
such that:

1. there is a tracial assignment with `d_2(J,1)>0`;
2. its exact-check mass is `g`;
3. every finite-dimensional `J`-separated approximate assignment has enlarged
   threshold satisfaction mass at most `q<g`;
4. the constants and finite trace-profile net are effective enough to extract
   one explicit sampled LCS subpresentation.

Items 1--3 plus finite-moment sparsification already imply existence of a
finitely presented nonhyperlinear solution group.  Item 4 upgrades existence
to Cairn's explicit root target.

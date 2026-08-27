# Cairn audit of Higman's un-conjugation leaf

**Date:** 2026-08-26  
**Scope:** only `Transport.UnConjugation` and
`Star.ConjugatorGraph.graph_benign`  
**Inputs:** repository definitions and elementary free-group calculations only  
**Not used:** Lean execution, MSI, or literature

## Verdict

The reduction already present in `Higman/TransportStar.lean` is correct:

\[
  \operatorname{BenignTF}(\mathsf{graphSub})
  \quad\Longrightarrow\quad
  \mathsf{Transport.UnConjugation}.
\]

It is not, however, a proof of un-conjugation.  The remaining field

```lean
Star.ConjugatorGraph.graph_benign : BenignTF Star.graphSub
```

is a genuine benign-witness construction.  None of the currently proved
closure operations produces that witness.  In particular, the shortest
apparent proof would require transporting benignness along an injective map
whose source has infinite rank.  The repository's `BenignTF.mapEmb` correctly
requires the source to be finitely generated, and deleting that hypothesis is
false in general.

This audit gives the exact reduction, proves the two elementary obstructions
which prevent the standard kernel and one-letter-orbit witnesses, and isolates
the precise theorem that would finish the leaf.  It does **not** assert that
`graphSub` is non-benign; no counterexample to the desired conclusion was
found.

## 1. Exact declarations

In `GroupApproximation/Higman/TransportFive.lean` the requested result is:

```lean
structure Transport.UnConjugation where
  unconj : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) →
    BenignTF (Subgroup.closure (Seq.bElt '' B))
```

In `GroupApproximation/Higman/TransportStar.lean` the residual is:

```lean
structure Star.ConjugatorGraph where
  graph_benign : BenignTF Star.graphSub
```

and the proved bridge is:

```lean
theorem Star.unConjugation_of
    (hgraph : Star.ConjugatorGraph) : Transport.UnConjugation
```

The ambient group is

\[
F_3=F(a,b,c),\qquad K=\langle b,c\rangle\le F_3,
\]

and

\[
\begin{aligned}
  \mathsf{graphHom}&:F(K)\longrightarrow F_3\times F_3,\\
  [h]&\longmapsto (h^{-1}ah,h),\\
  \mathsf{graphSub}&=\operatorname{range}(\mathsf{graphHom})
   =\left\langle (h^{-1}ah,h):h\in K\right\rangle.
\end{aligned}
\]

Here `F(K)` means the free group on the underlying set of `K`, not the
rank-two group `K` itself.  The first coordinate is the map `Conj.cbHom`, and
`Conj.cbHom_injective` makes `graphHom` injective.

## 2. The reduction is complete

For a set `T ⊆ K`, let

\[
  C_T=\langle [h]:h\in T\rangle\le F(K).
\]

The repository proves the following three identities.

First, cutting the full graph by the first coordinate cuts its free basis:

\[
 C_T\mathsf{.map}(\mathsf{graphHom})
 =\mathsf{graphSub}\cap
   \bigl(C_T\mathsf{.map}(\mathsf{cbHom})\times F_3\bigr).
\tag{1}
\]

The reverse inclusion in (1) is exactly where injectivity of `cbHom` is used.
If a graph word and a `T`-word have the same first coordinate, they are the
same word in `F(K)`.

Second, joining with the first coordinate axis erases the first coordinate:

\[
 C_T\mathsf{.map}(\mathsf{graphHom})\vee(F_3\times 1)
 =F_3\times C_T\mathsf{.map}(\mathsf{evalHom}).
\tag{2}
\]

Indeed, if `(cbHom(w),evalHom(w))` is a graph element, multiplication by
`(cbHom(w)^{-1}x,1)` produces `(x,evalHom(w))`.

Third, pulling (2) back along the second-coordinate inclusion gives

\[
 (F_3\times H)\mathsf{.comap}(\mathsf{inr})=H.
\tag{3}
\]

Thus `BenignTF.inf`, `BenignTF.sup`, and `BenignTF.comap`, together with
benignness of the finitely generated first axis, turn

\[
  \operatorname{BenignTF}\bigl(C_T\mathsf{.map}(\mathsf{cbHom})\bigr)
\]

into

\[
  \operatorname{BenignTF}\bigl(C_T\mathsf{.map}(\mathsf{evalHom})\bigr)
\]

provided `graphSub` is benign.  At `T = Seq.bK '' B`, the two groups are
definitionally identified by proved theorems with `Seq.ASub B` and
`closure (Seq.bElt '' B)`.  Hence the implication to `UnConjugation` has no
remaining algebraic or normal-form gap.

## 3. The attractive direct-product route and its exact stopping point

Put

\[
 W=F(K)\times F_3
\]

and define two injective/auxiliary maps

\[
\begin{aligned}
 j &: W\longrightarrow F_3\times F_3,
      &(w,g)&\longmapsto(\mathsf{cbHom}(w),g),\\
 q &: W\longrightarrow F_3\times F_3,
      &(w,g)&\longmapsto(\mathsf{evalHom}(w),g).
\end{aligned}
\]

Let `Delta` be the diagonal subgroup of `F3 x F3`.  It is finitely generated,
so it is benign with a torsion-free witness.  Its preimage

\[
 \Gamma=q^{-1}(\Delta)
   =\{(w,\mathsf{evalHom}(w)):w\in F(K)\}
\]

is benign in `W` by the proved `BenignTF.comap`, because `j` embeds `W` in the
finitely presented torsion-free group `F3 x F3`.  Moreover

\[
 j(\Gamma)=\mathsf{graphSub}.
\tag{4}
\]

Both inclusions in (4) are literal:

* `j(w,evalHom(w)) = (cbHom(w),evalHom(w)) = graphHom(w)`;
* every element of `graphSub` is `graphHom(w)` for some `w`.

So the residual becomes exactly this image-transport problem:

> transport a benign subgroup of `W` along the injective map
> `j : W -> F3 x F3`.

The proved theorem has signature

```lean
BenignTF.mapEmb
  [Group.IsFinitelyPresented N] [Group.FG G]
  (h : BenignTF H) (theta : G →* N)
  (htheta : Function.Injective theta) : BenignTF (H.map theta)
```

and cannot be applied because `W` is not finitely generated.

### Why `W` is not finitely generated

The set underlying `K = F(b,c)` is infinite.  `F(K)` has one free generator
`[h]` for every `h in K`.  If finitely many words generated `F(K)`, only
finitely many basis letters would occur in those words.  Sending one unused
basis letter to `1 in Z` and every occurring basis letter to `0` gives a
homomorphism that kills the alleged finite generating set but not the unused
letter, a contradiction.  Hence `F(K)`, and therefore `W`, is not finitely
generated.

This is not cosmetic.  `mapEmb` constructs an amalgam over the whole source
group, and finite presentability of that amalgam is exactly what finite
generation pays for.

## 4. The smallest false shortcut: unrestricted image transport

The following tempting strengthening is false:

```text
For every injective theta : G -> N with N finitely presented,
Benign(H in G) implies Benign(theta(H) in N), with no FG hypothesis on G.
```

Here is a zero-literature diagonal proof.

1. Every subgroup `S` of `F2` is the image of the top subgroup of the abstract
   group `S` under its inclusion `S -> F2`.
2. The top subgroup of `S` is benign in `S`: use `F2` itself as a finitely
   presented overgroup and its finitely generated top subgroup as cutter.
3. Therefore unrestricted image transport would make every subgroup of `F2`
   benign.
4. There are only countably many benign subgroups of `F2`.  A witness is
   specified by a finite presentation, the two words giving the embedding of
   `F2`, and finitely many words generating the cutter; all such finite strings
   form a countable set.
5. There are uncountably many subgroups of `F2`.  The elements
   `b^{-n} a b^n`, `n in N`, freely generate a free group of countable rank
   (the same elementary conjugate-basis action used by `cbHom_injective`).
   Distinct subsets of this basis generate distinct subgroups, yielding one
   subgroup for every subset of `N`.

This is exactly the obstruction formalized conditionally in
`Higman/MapEmbSharp.lean`.  Consequently the missing hypothesis may not be
deleted merely to close (4).

## 5. Two other standard witness shapes are impossible here

### 5.1 `graphSub` is not a kernel

The seed

\[
  (a,1)=\mathsf{genPair}(1)
\]

lies in `graphSub`.  Conjugating it in the first factor by `b` gives

\[
  (b^{-1}ab,1).
\]

If this were `graphHom(w)`, its first coordinate would, by injectivity of
`cbHom`, force `w=[b]`.  Its second coordinate would then be `b`, not `1`.
Thus `graphSub` is not normal.  In particular it cannot be produced by the
direct-product kernel witness `BenignWitness.ker`.

This is the theorem `Star.not_normal_graphSub` in
`Higman/TransportStarWitness.lean`.

### 5.2 No homomorphism un-conjugates

Suppose homomorphisms `psi : F3 -> Q` and `u : K -> Q` satisfied

\[
  \psi(h^{-1}ah)=u(h)\qquad(h\in K).
\]

Taking `h=1` gives `psi(a)=1`.  Therefore every left side is a conjugate of
`1`, so `u(h)=1` for every `h`.  At the inclusion `u : K -> F3`, `h=b` gives
the contradiction `b=1`.

Hence no endomorphism of `F3`, and in fact no homomorphism from `F3` to any
group with a nontrivial target map on `K`, can turn all `a^h` into `h`.  The
finitely generated graph-of-an-endomorphism HNN witness is therefore
impossible.  This is `Star.eq_one_of_unconj` / `Star.not_endo_unconj`.

Likewise a RowSubgroup-style single conjugacy orbit cannot work in any
overgroup retaining a homomorphism to the second `F3`: conjugation preserves
the fact that the second coordinate is `1`, whereas `genPair(h)` has second
coordinate `h`.  This is `Star.eq_one_of_conj_genPair`.

## 6. Exact remaining theorem

There are two honest ways to state the remaining obligation.

### Concrete form

Construct directly

```lean
Nonempty (TorsionFreeBenignWitness Star.graphSub)
```

That means explicit data:

* a finitely presented torsion-free group `P`;
* an injective homomorphism `e : F3 x F3 -> P`;
* a finitely generated subgroup `L <= P`;
* a proof `L.comap e = graphSub`.

No such `P,e,L` are present in the repository.

### Narrow transitivity form

Prove benignness can be transported in this specific diagram

\[
 \Gamma\le W\xrightarrow{\;j\;}F_3\times F_3,
 \qquad j(\Gamma)=\mathsf{graphSub},
\]

using the explicit `comap` witness for `Gamma`, without assuming `W` finitely
generated.  A fully general source-free `mapEmb` is false, so any successful
lemma must use extra data particular to this diagram (or a genuine benign-in-
benign transitivity hypothesis plus its own finite witness construction).

The phrase “benign in benign is benign” is not itself a proof here.  Its
natural amalgam glues over the infinite-rank middle group and is not known to
be finitely presented.  Invoking the recursively-enumerable-subgroup
characterization to prove transitivity would be circular: that characterization
is the Higman theorem this Section 5 transport is being assembled to prove.

## 7. Dependency boundary

The exact dependency chain is

```text
Star.ConjugatorGraph.graph_benign
  -> Star.unConjugation_of_graphBenign
  -> Transport.UnConjugation
  -> Transport.transportSectionFive_of_parts
       (also needs CodeRE and CompletionLemma)
  -> TransportSectionFive
  -> REBenignTF / the effective Higman compiler downstream
```

All arrows after `graph_benign` are already implemented.  Thus this audit
neither widens nor hides the gap: the single unproved mathematical assertion
on this branch remains the existence of the torsion-free finite witness
`P,e,L` above.

## 8. Safe conclusion

The claimed *reduction* is valid.  The claimed *leaf* is not discharged.
There is no counterexample to `UnConjugation`, but there are explicit
counterexamples to each cheap proof shape:

* `graphSub` is not a kernel;
* no homomorphism performs un-conjugation;
* no single conjugacy orbit preserving the second projection generates the
  required pairs;
* unrestricted `mapEmb` without finite generation would make every subgroup
  of `F2` benign and is false.

Any unconditional completion must therefore supply a new finite witness (or
a non-circular, finite-presentation-preserving transitivity construction), not
just another application of the existing closure API.

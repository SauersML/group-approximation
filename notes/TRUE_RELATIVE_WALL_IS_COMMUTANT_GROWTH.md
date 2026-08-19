# The relative wall is exactly compressor growth of a relative commutant

Date: 2026-08-14

## 1. Outcome

Let `Gamma<G` be a compressor pair,

```text
P_Gamma={s in G : s Gamma s^(-1)<=Gamma},
t in P_Gamma,   gamma in Gamma,   h=t^(-1) gamma t notin Gamma.   (CG1)
```

Let `M` be a finite von Neumann algebra with faithful normal trace `tau`
and let `pi:G->U(M)` be a homomorphism.  Write

```text
N  =M intersect pi(Gamma)',
N_s=M intersect pi(s Gamma s^(-1))'      (s in P_Gamma).          (CG2)
```

This note proves four things.

1. **Normal form.**  A relative wall for `(Gamma<G,t)` in `M` exists if and
   only if the inclusion `N<=N_t` is *proper*.  The marked element `h`
   disappears from the criterion entirely.
2. **Clifford normal form.**  A *Clifford* wall exists if and only if there
   are `gamma in Gamma` and a self-adjoint involution `w in N_t` with
   `w` and `pi(gamma) w pi(gamma)^*` anticommuting.  The compressor `t`
   survives only through the subgroup `Gamma_1=t Gamma t^(-1)<=Gamma`.
3. **Index rigidity.**  The growth index
   `lambda(s)=[Ad pi(s)(N):N]` is a submultiplicative function on the
   compressor semigroup `P_Gamma`, multiplicative wherever finite, and
   equal to `1` on `N_G(Gamma)`.  A wall forces `lambda(t)>1`, hence
   `[M:N]=infinity` and a strictly increasing compressor tower.
4. **Commutator compressors are rigid.**  If `s=[a,b]` with
   `a,b,s in P_Gamma` and `lambda(a),lambda(b)<infinity`, then
   `lambda(s)=1`: *no wall at `s`*.  The explicit compressor of Kun--Thom
   Theorem E used in this repository, `t=t_(u_12)` with `u_12=I+e_12`, is a
   commutator `[u_13,u_32]` of two further compressors, so a wall there
   requires **infinite-index** commutant growth at `u_13` or `u_32`.
   Finite lamps cannot build the wall.

Item 4 is the sharpest structural constraint currently known on the Clifford
wall.  It rules out every candidate in which the compressor enlarges the
relative commutant by a finite-index amount, and it is consistent with -- in
fact it forces a prediction about -- the Clifford crossed-product model of
`TRUE_KUN_THOM_CLIFFORD_PHASE.md`.

Nothing here uses Connes embeddability, property `(T)`, finite dimensions,
or any approximation notion.  All statements are exact von Neumann algebra
facts about an arbitrary homomorphism into a finite tracial algebra.  The
approximation content of the problem is discussed in Section 6.

## 2. The compressor moves the relative commutant one way

Lemma 1 and Theorems 2 and 3 use no analysis whatever.  State them for an
arbitrary target **group** `U` and a homomorphism `pi:G->U`, writing

```text
N  =C_U(pi(Gamma)),
N_s=C_U(pi(s Gamma s^(-1)))       (s in P_Gamma)                  (CG2a)
```

for the centralizers.  The case of interest is `U=U(M)` with `M` finite
tracial, where `(CG2a)` returns `(CG2)` because a von Neumann algebra is the
closed span of its unitaries; Section 5 onwards is specific to that case.
Section 8 uses the extra generality in an essential way.

**Lemma 1.**  For every `s in P_Gamma`,

```text
Ad pi(s)(N)=N_s,        N<=N_s.                                   (CG3)
```

**Proof.**  Let `a in N` and `s' in s Gamma s^(-1)`, say `s'=s r s^(-1)`
with `r in Gamma`.  Then

```text
pi(s)a pi(s)^* pi(s')=pi(s)a pi(r) pi(s)^*
                     =pi(s) pi(r) a pi(s)^*
                     =pi(s') pi(s) a pi(s)^*,
```

so `Ad pi(s)(N)<=N_s`.  Conversely, if `b in N_s` and `r in Gamma`, the same
computation applied to `pi(s)^* b pi(s)` and `pi(r)=pi(s)^* pi(s r s^(-1))
pi(s)` gives `Ad pi(s)^(-1)(N_s)<=N`.  The two inclusions give equality.
Finally `s Gamma s^(-1)<=Gamma` gives `pi(s Gamma s^(-1))'>=pi(Gamma)'`,
respectively `C_U(pi(s Gamma s^(-1)))>=C_U(pi(Gamma))`, i.e. `N<=N_s`.
End proof.

Lemma 1 is the general form of the finite-dimensional statement
`commutant_no_growth`, and it exhibits the compressor as an **isomorphism of
`N` onto a possibly larger `N_s`**.  The consequence is the established,
Lean-checked principle `invariant-size-collapse`
(`Criterion/FiniteQuotientBlindness.no_strict_compression_of_invariantSize`):
such an inclusion is an equality as soon as the target carries a size that
conjugation preserves and that distinguishes proper inclusions.  Its known
instances -- cardinality, `finrank`, `Nat.card`, Haar -- cover finite groups,
genuine finite-dimensional representations and compact targets, which is why
`commutant-no-growth` and `infranormal-compact-closure-normal` both fall out.

That node also records where the principle stops: the II_1 trace satisfies
the invariance hypothesis but fails the *other* one, being refinement-blind,
and it calls that single failure the whole open branch.

It is worth naming that failure in the form the sofic side uses.  The
permutation obstruction runs on **atomicity** of the fixed algebra
`ell^infinity(Y)^Gamma`; atomicity is what makes the minimal projections a
countable invariant, and hence what supplies the strictly monotone size.  In
a tracial ultraproduct atomicity fails -- the commutant can be diffuse -- and
that is the same fact as refinement-blindness of the trace.  So "the
obstruction is permutation specific only at atomicity" and "the collapse
principle stops at the II_1 trace" are one statement in two vocabularies.

**Refinement, due to the stability lane.**  Atomicity is the *ultraproduct*
symptom and not the finite-level content.  At finite level every subalgebra
of `M_d` is atomic, so minimal projections always exist and always supply a
count; what fails is **uniformity** -- the atom count diverges and the atom
traces vanish.  The sharp example is `SL_3(Z)` with its finite-quotient
regular representations: the commutant is `C[SL_3(Z/n)]`, whose minimal
projections have trace `d_pi/|G_n|<=|G_n|^(-1/2)->0`, so every finite level
is atomic while the ultraproduct commutant is diffuse.  So the monotone size
does not fail to *exist* at finite level, it fails to be *stable*, and that
is why the sofic argument spends a median device restoring uniformity of atom
traces rather than restoring atomicity.

This matters for wall design.  The finite-level target is not "the `C_n`
carry non-atomic commutant structure", which is unsatisfiable, but "the `C_n`
carry commutant structure whose atom traces are not uniformly controlled".

Section 5 supplies the missing invariant on exactly that branch.  The Pimsner--Popa index of the
inclusion is conjugation invariant **and** distinguishes proper inclusions,
so it is a size in the required sense; what it is not is finite.  Everything
below is the exploitation of that one remaining invariant: it is
multiplicative on the compressor semigroup, so it can be cancelled across a
group relation, and a wall survives only where it is infinite.

## 3. Normal form for the wall

Say that `(pi,v)` is a **relative wall** if `v` is an element of `N` with

```text
[v,pi(h)]!=1.                                                     (CG4)
```

In a unitary target this is the same as `v pi(h)-pi(h)v!=0`.  By
`FALSE_RELATIVE_BICOMMUTANT_ENDPOINT.md`, Theorem 1, it is the exact
one-representation form of a Connes-embeddable separating representation of
the radical double, and by `TRUE_KUN_THOM_CLIFFORD_PHASE.md` its involutive
strengthening is the free-lamp endpoint.

**Theorem 2 (normal form).**  A relative wall exists in `U` if and only if

```text
N!=N_t.                                                           (CG5)
```

**Proof.**  Suppose `N=N_t` and let `v in N`.  By Lemma 1,
`Ad pi(t)(v) in N_t=N`, so `Ad pi(t)(v)` commutes with `pi(gamma)`.
Therefore

```text
Ad pi(h)(v)=Ad pi(t)^(-1) Ad pi(gamma) Ad pi(t)(v)
           =Ad pi(t)^(-1) Ad pi(t)(v)=v,                          (CG6)
```

using `h=t^(-1) gamma t`.  Thus `(CG4)` fails for every `v`, for every
`gamma in Gamma`.

Conversely suppose `N<N_t` properly and pick `w in N_t` with `w notin N`.
(For `U=U(M)` this may be taken unitary: a von Neumann algebra is the closed
linear span of its unitaries and `N` is weakly closed, so if every unitary of
`N_t` lay in `N` the two algebras would coincide.)  Then `w` fails to commute
with `pi(gamma)` for some `gamma in Gamma`.  Put

```text
v=Ad pi(t)^(-1)(w) in Ad pi(t)^(-1)(N_t)=N,                       (CG7)
```

an element of `N` by Lemma 1.  Applying the automorphism `Ad pi(t)` to the
commutator and using `t h t^(-1)=gamma`,

```text
Ad pi(t)([v,pi(h)])=[w,pi(gamma)]!=1.                             (CG8)
```

Hence `(CG4)` holds for this `v` and this `gamma`.  End proof.

Two consequences are worth isolating.

*The marked element is not data.*  Theorem 2 shows that the choice of
`gamma in Gamma`, and hence of the marked predecessor `h`, is irrelevant to
existence: some `gamma` works precisely when `N!=N_t`.  What has to be
constructed is the strict growth of one relative commutant under one
compressor.

*Only the compressed subgroup appears.*  The wall unitary is manufactured
inside `N_t=M intersect pi(Gamma_1)'` for `Gamma_1=t Gamma t^(-1)`, and is
then pulled back by the automorphism `Ad pi(t)^(-1)`.  The commutation
demand is against the *smaller* group `Gamma_1`, not against `Gamma`.

Infranormality turns Theorem 2 into a single invariance statement.

**Corollary 2a.**  Suppose `Gamma` is infranormal, i.e. `P_Gamma` generates
`G`.  Then a relative wall exists for **some** compressor if and only if

```text
N=C_U(pi(Gamma))   is not   Ad pi(G)-invariant.                   (CG8a)
```

**Proof.**  If `N` is `Ad pi(G)`-invariant then `N_s=Ad pi(s)(N)=N` for every
`s in P_Gamma`, and Theorem 2 excludes a wall at each.  Conversely, if no
wall exists at any `s in P_Gamma` then `Ad pi(s)(N)=N` for every such `s` by
Theorem 2 and Lemma 1; each such `Ad pi(s)` then restricts to an
automorphism of `N`, so `Ad pi(s)^(-1)(N)=N` as well.  Hence
`{g in G : Ad pi(g)(N)=N}` is a subgroup containing `P_Gamma`, and
infranormality makes it all of `G`.  End proof.

### 3.1 The sofic shadow of Theorem 2

Corollary 2a has an exact classical counterpart in the literature.  Kun and
Thom, arXiv:2608.06222, Theorem C, prove that if `Gamma` is infranormal in
`G`, both Kazhdan, and `G` acts on `(X,mu)` by a **sofic** probability
measure preserving action, then the fixed-point algebra `L^infinity(X)^Gamma`
is `G`-invariant; their Corollary D deduces that the generalized Bernoulli
action on `(K,kappa)^(G/Gamma)` is not sofic, exactly as Theorem 2 deduces a
wall from properness of an inclusion.

The dictionary is now exact rather than merely analogous.  `L^infinity(X)^Gamma`
is the abelian instance of `N`, and Kun--Thom Theorem C asserts precisely the
right-hand side of `(CG8a)` for sofic actions.  **The wall is the failure of
the noncommutative Kun--Thom Theorem C**, with "sofic action" weakened to
"Connes-embeddable model".

*Verification status.*  Theorems A and E of that paper are recorded verbatim
from a PDF read in `research/wreath-not-sofic.md`; the statement of Theorem C
quoted here is a paraphrase from the same read, not a verbatim quotation, and
is used below only as orientation.  No theorem of this note depends on it.

What Corollary 2a adds is that invariance of the fixed-point algebra is not
merely a sufficient obstruction but the *exact* content of the wall, and that
the hypothesis to break is soficity of the action, not amenability or finite
dimension.

### 3.2 Untwisting is self-defeating

Corollary 2a settles a design question raised on the sofic side.  Kun--Thom
arXiv:1901.03963 v3, Theorem 1.4, is an amenable-lamp obstruction that needs
only the whole approximation to be an expander sequence -- weaker than the
`Gamma`-labelled expansion of their Theorem 1.1 -- but is stated for
**direct** products `Gamma times Delta` with `Delta` amenable.  Our Clifford
lamp is locally finite, hence amenable, and our configuration
`Vtilde_S semidirect G` is semidirect, so Theorem 1.4 does not apply as
stated; the boundary between "applies" and "does not" is exactly the
semidirect twisting.

The relevant risk is therefore that a wall construction accidentally
untwists the extension -- producing, say, a `G`-invariant complement or an
invariant copy of the lamp algebra inside the model.  Corollary 2a shows
that this is self-defeating quite apart from Theorem 1.4: an invariant lamp
algebra sits inside `N` and makes `N` itself `Ad pi(G)`-invariant, which is
exactly the right-hand side of `(CG8a)` and kills the wall.  So untwisting
costs the construction its own conclusion, and would simultaneously hand
Theorem 1.4 a live obstruction on the sofic side.  Both readings forbid the
same move, and the twisting is not a technical nuisance to be removed but
the entire source of the phenomenon.

For the record, KT v3 Lemma 5.1 -- a finitely generated group with a
finite-index LEF subgroup is LEF -- is not used anywhere in this note.  It
transports LEF across finite index, and every index appearing here is
infinite by Corollary 5.

## 4. Clifford normal form

Recall the free-lamp amalgam and its marked word,

```text
H=G *_Gamma (Gamma times <k>)=<G,k | k^2=1,[k,Gamma]=1>,
r=[k,h],   x=[k,r].                                               (CG9)
```

A **Clifford wall** is a self-adjoint involution `C in N` such that, with
`C_h=Ad pi(h)(C)`,

```text
C C_h+C_h C=0.                                                   (CG10)
```

Given `(CG10)`, the assignment `g|->pi(g)`, `k|->C` is a homomorphism
`Psi:H->U(M)` and, since `C_h C=-C C_h` and both factors are involutions,

```text
Psi(x)=(C_h C)^2=-C_h C_h C C=-1.                                (CG11)
```

**Theorem 3 (Clifford normal form).**  A Clifford wall exists in `M` if and
only if there are `gamma in Gamma` and a self-adjoint involution

```text
w in N_t=M intersect pi(t Gamma t^(-1))'                         (CG12)
```

such that

```text
w (pi(gamma) w pi(gamma)^*)+(pi(gamma) w pi(gamma)^*) w=0.       (CG13)
```

**Proof.**  Apply the trace-preserving automorphism `theta=Ad pi(t)` of `M`
to `(CG10)`.  Put `w=theta(C)`.  By Lemma 1, `C in N` gives `w in N_t`, and
`w` is again a self-adjoint involution.  Moreover

```text
theta(C_h)=Ad(pi(t)pi(h)pi(t)^(-1))(theta(C))
          =Ad pi(t h t^(-1))(w)=Ad pi(gamma)(w),                 (CG14)
```

because `t h t^(-1)=gamma`.  Since `theta` is a `*`-automorphism it carries
`(CG10)` to `(CG13)`.  Every step is reversible: given `w` and `gamma` as in
`(CG12)--(CG13)`, set `C=theta^(-1)(w) in N`.  End proof.

So the Clifford wall is precisely a **Majorana over the coset space
`Gamma/Gamma_1`**: an involution centralizing the compressed copy `Gamma_1`
whose `Gamma`-conjugate anticommutes with it.  The `Gamma`-orbit of the
distinguished site is `Gamma/Gamma_1`, since the stabiliser in `Gamma` of the
point `t Gamma in G/Gamma` is `Gamma intersect t Gamma t^(-1)=Gamma_1`.

This is a genuine simplification of the search target -- the anticommutation
is now a one-step `Gamma`-conjugation, with no compressor inside it -- but it
is not a reduction of the problem to `Gamma`: the homomorphism `pi` must
still be defined on all of `G`.  Indeed, transporting the site condition
`Gamma_1<=K`, `gamma notin K` by `t` returns exactly the condition
`Gamma<=K'`, `h notin K'` of `FALSE_RELATIVE_BICOMMUTANT_ENDPOINT.md`,
`(RBE19)`, so the generalized-Bernoulli search space is unchanged.  What is
gained is the structural criterion `(CG5)`, which the next section exploits.

## 5. Index rigidity on the compressor semigroup

For `s in P_Gamma` define the **growth index**

```text
lambda(s)=[Ad pi(s)(N):N] in [1,infinity],                       (CG15)
```

the Pimsner--Popa index of the inclusion `N<=N_s` of `(CG3)` with respect to
the trace-preserving conditional expectation.  Recall two standard facts.

* (Automorphism invariance)  If `theta` is a trace-preserving automorphism
  of `M` then `[theta(B):theta(A)]=[B:A]`.
* (Tower behaviour)  For `A<=B<=C`, `[C:A]<=[C:B][B:A]`, with equality
  whenever `[C:A]<infinity`.

Submultiplicativity is immediate from the Pimsner--Popa inequality applied
twice; equality in the finite case is the standard multiplicativity of the
index.

**Scope: the index is not a metric invariant.**  Everything below uses it
only on *exact* inclusions inside one fixed algebra, and that restriction is
essential.  The index is discontinuous in `||.||_2`: for finite-dimensional
abelian `N<=M` with `N`-atoms `e_i` and `M`-atoms `f_j` one has
`Index=max_j tau(e_(i(j)))/tau(f_j)`, so refining a single atom of trace `t`
into pieces of trace `t-epsilon` and `epsilon` moves the subalgebra by
`O(sqrt epsilon)` while sending the index to at least `t/epsilon`.  The index
therefore blows up on metrically invisible refinements, and it is useless in
any statement about almost-invariant or approximately defined subalgebras --
where, moreover, there is no exact inclusion to take an index of.  This is
recorded because the neighbouring stability lane needs an invariant that is
`||.||_2`-stable, and the index is not it.

**But the index is a legitimate *target functional* on an exact nesting, and
on abelian pairs it is exactly the unequal-trace statement.**  The
distinction is between using the index to compare nearby subalgebras, which
fails, and evaluating it on one exact pair, which does not.

**Proposition 4a.**  Let `B_0<=B_1` be finite-dimensional abelian unital
subalgebras of a tracial `M`, with `B_1`-atoms `p_i` and `B_0`-atoms
`q_A=sum_(i in A) p_i`.  Then

```text
[B_1:B_0]=max_A ( sum_(i in A) tau(p_i) ) / ( min_(i in A) tau(p_i) )
        >= max_A #A,                                              (CG25c)
```

with equality in a block `A` if and only if all the `p_i`, `i in A`, have
equal trace.

**Proof.**  For abelian inclusions the trace-preserving expectation is
`E(p_i)=(tau(p_i)/tau(q_(A(i))))q_(A(i))`, so the Pimsner--Popa constant is
`min_i tau(p_i)/tau(q_(A(i)))` and its reciprocal is the displayed maximum.
Within a block, `sum_(i in A) tau(p_i) >= #A min_(i in A) tau(p_i)`, with
equality exactly when the traces agree.  End proof.

So on a nested pair of coarse and fine block algebras, the index is bounded
below by the fine-block count and is *minimal precisely when the fine blocks
inside each coarse block have equal trace*.  A median device whose conclusion
is "size ratios tend to one uniformly" is therefore asserting exactly

```text
[B_1:B_0] / max_A #A -> 1,                                        (CG25d)
```

index asymptotically minimal.  This is a reformulation rather than a new
theorem, but it is the reformulation in which the target is a single number,
and it is available because the nesting is demanded exact -- which is
precisely the hypothesis under which the continuity objection above does not
apply.

**RETRACTED (2026-08-15).**  (CG25d) is NOT equivalent to the median
device's conclusion (fork's (8)), and the failure is in the direction that
matters.  `cairn-fork`'s counterexample, verified and accepted by
`cairn-wall` in their transcript minutes before the session limit hit
(the retraction annotation is applied by the coordinator because the agent
died before writing it): take one coarse block with `k` fine atoms all of
trace `t`, and a second with two fine atoms of traces `10s` and `s`.  The
first contributes index `k`, the second `11`, so for `k >= 11` the index
equals `max_A #A` exactly and the normalized quantity (CG25d) is exactly
`1` — while the second block has trace ratio `10` and (8) fails badly.
Taking maxima over coarse blocks discards precisely the per-block
information the median device is about, and the blockwise repair
(`index_A/#A`, a mean-over-min) fails too.  Structurally: the index is a
sup-based functional with no exceptional-set tolerance, while (8) permits
discarding a vanishing-trace exceptional set — one tiny unbalanced block
ruins the index invisibly to (8), and one large balanced block masks a
small unbalanced one in the index's max.  Proposition 4a's FORMULA above
stands; only the reformulation claim (CG25d) is withdrawn.  Do not
re-attempt.

**Theorem 4.**  `lambda` satisfies

```text
lambda(s_1 s_2)<=lambda(s_1) lambda(s_2),
lambda(s_1 s_2)=lambda(s_1) lambda(s_2)  if the left side is finite,
lambda(s)=1                              for s in N_G(Gamma),
lambda(s)=1 <=> Ad pi(s)(N)=N.                                   (CG16)
```

**Proof.**  `Ad pi(s_1 s_2)=Ad pi(s_1) Ad pi(s_2)`, so by Lemma 1

```text
N <= Ad pi(s_1)(N) <= Ad pi(s_1) Ad pi(s_2)(N)=Ad pi(s_1s_2)(N).
```

The top index of this tower is
`[Ad pi(s_1)Ad pi(s_2)(N):Ad pi(s_1)(N)]=[Ad pi(s_2)(N):N]=lambda(s_2)`
by automorphism invariance, and the bottom one is `lambda(s_1)`.  The tower
facts give both displayed relations.  If `s` normalizes `Gamma` then
`s Gamma s^(-1)=Gamma` and `N_s=N`.  Finally the Pimsner--Popa index of an
inclusion equals `1` exactly when the inclusion is an equality.  End proof.

**Corollary 5.**  If a relative wall exists in `M` then `lambda(t)>1`, the
tower

```text
N<Ad pi(t)(N)<Ad pi(t)^2(N)<...                                  (CG17)
```

is strictly increasing with `[Ad pi(t)^j(N):N]=lambda(t)^j`, and

```text
[M:N]=infinity.                                                  (CG18)
```

**Proof.**  Theorem 2 gives `N!=N_t`, so `lambda(t)>1` by `(CG16)`.  If
`lambda(t)<infinity` then `[Ad pi(t)^j(N):N]=lambda(t)^j->infinity` and
`[M:N]>=lambda(t)^j` for every `j`; if `lambda(t)=infinity` then
`[M:N]=infinity` directly.  End proof.

So a wall is impossible whenever the relative commutant of `pi(Gamma)` is
finite-dimensional, or more generally of finite index in `M`.  This is the
exact II_1 replacement for the finite-dimensional collapse, and it explains
why every honest finite-dimensional model fails: there `[M:N]<infinity`
automatically.

**How informative is Corollary 5?  Not established, and an earlier answer
here was withdrawn.**  A previous version of this paragraph asserted that the
infinite-index regime is where tracial models generically live, on the ground
that a diffuse limiting commutant forces `[M:N]=infinity`.  That ground was
retracted by its author and the assertion is withdrawn with it.  It fails
twice: a diffuse algebra has no minimal projections, so the
finite-dimensional index formula that suggested it does not apply after the
limit; and diffuseness does not force infinite index in any case, since a
finite-index subfactor of a II_1 factor is diffuse.

The nearest correct statement is narrow.  If `N` is **diffuse abelian** in a
II_1 factor `M` then `[M:N]=infinity`, because finite index makes `N' cap M`
finite dimensional while `N<=N' cap M` is not.  That does not reach the
present setting: in the Clifford model `N` contains the anticommuting
Majoranas at the `Gamma`-fixed sites and so is not abelian, and the
`SL_3(Z)` model whose commutant is `prod^omega C[SL_3(Z/n)]` is diffuse but
also not abelian.

So `(CG18)` is recorded as what it is -- a proved necessary condition which
in particular excludes every finite-dimensional model -- and whether infinite
index is typical or atypical among Connes-embeddable tracial models of this
group is left open rather than asserted in either direction.

None of this touches Theorem 6 or Corollary 7, and the distinction is worth
stating.  They concern `lambda(s)=[Ad pi(s)(N):N]`, the index of `N` inside
its own compressor image, not `[M:N]`.  Diffuseness of `N` says nothing about
`lambda(s)`: if `N=Ad pi(s)(N)` then `lambda(s)=1` however diffuse `N` is.
So `lambda(s)=infinity` is a genuine demand that no genericity consideration
supplies, and it is where the content of Section 5 sits.

**Theorem 6 (commutator compressors carry no wall).**  Let `a,b in P_Gamma`
and suppose the group commutator `s=[a,b]=a b a^(-1) b^(-1)` also lies in
`P_Gamma`.  If `lambda(a)<infinity` and `lambda(b)<infinity`, then

```text
lambda(s)=1,                                                     (CG19)
```

so there is no relative wall for the compressor `s`.

**Proof.**  In `G` the commutator identity reads `a b=s b a`, an equality of
products of elements of `P_Gamma`.  By Theorem 4,

```text
lambda(ab)<=lambda(a) lambda(b)<infinity,
```

so `lambda(ab)` is finite and therefore `lambda(ab)=lambda(a)lambda(b)`.
The same element factors as `s b a`, and

```text
lambda(sba)=lambda(ab)<infinity,
```

so the three-term factorization is also multiplicative:

```text
lambda(s) lambda(b) lambda(a)=lambda(a) lambda(b).
```

The right-hand side is finite and nonzero, so `lambda(s)=1`.  Theorem 2 and
`(CG16)` then exclude a wall at `s`.  End proof.

Theorem 6 replaces the Ore-type argument that
`FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md` refutes.  The compressor
semigroup has no useful fractions, but it does have commutators, and a
multiplicative invariant with values in an abelian monoid cannot see a
commutator unless it is infinite on a factor.

### 5.1 The explicit Kun--Thom pair

Kun--Thom, arXiv:2608.06222, Theorem E, supplies the explicit residually
finite Kazhdan infranormal pair: for a prime power `q` and `r,d>=3`,

```text
R_+=F_q[x_1,...,x_d]<R=F_q[x_1^(+-1),...,x_d^(+-1)],
Gamma=EL_r(R_+),   G=EL_r(R) semidirect SL_d(Z),                 (CG20)
```

with `SL_d(Z)` acting by monomial substitution, `x^v |-> x^(ell v)` for
`v in Z^d`.  For `ell in SL_d(Z)` the copy `(1,ell)` conjugates `Gamma` into
itself exactly when `ell(N^d)<=N^d`, that is exactly when every entry of
`ell` is nonnegative.  Hence

```text
L_+=SL_d(Z) intersect M_d(N) <= P_Gamma,                         (CG21)
```

and in particular every positive elementary transvection
`u_(ij)(c)=I+c e_(ij)`, `i!=j`, `c in N`, is a compressor.  The same
description of the external projection of the compressor semigroup is proved
for this repository's monomial-cone framing in
`FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md`, `(ONO10)`, with `M_(3x2)(Z)` in
place of `Z^d`; both framings produce the same `L_+`.

Each `u_(ij)(1)` is a *strict* compressor: `u_(ij)(1)^(-1)=I-e_(ij)` sends
the exponent `e_j` to `e_j-e_i`, so the elementary matrix of `Gamma` with
entry `x_j` is conjugated to one with entry `x_j x_i^(-1) notin R_+`, and
matrix entries of members of `EL_r(R_+)` lie in `R_+`.  For `d>=3` the
Steinberg identity

```text
[u_(ik)(a),u_(kj)(b)]=u_(ij)(ab),      i,j,k distinct,           (CG22)
```

expresses one positive transvection as a commutator of two others, all three
lying in `L_+<=P_Gamma`.

The compressor this repository actually uses is `t=t_(u_12)`, `u_12=I+e_12`,
whose ring image is `S=F_q[x_1,x_1x_2,x_3,...,x_d]` and which satisfies
`[Gamma:t Gamma t^(-1)]=infinity` (`notes/NOTEPAD.md`, "The compressor has
infinite index").  By `(CG22)` with `i=1`, `k=3`, `j=2`,

```text
u_12=[u_13,u_32].                                                (CG23)
```

**Corollary 7.**  Let `pi:G->U(M)` be any homomorphism into a finite tracial
von Neumann algebra which admits a relative wall for the explicit compressor
`t=t_(u_12)`.  Then

```text
lambda(u_13)=infinity   or   lambda(u_32)=infinity.              (CG24)
```

More generally, if every positive elementary transvection has finite growth
index, then all of them have growth index `1` -- each is a commutator of two
others by `(CG22)`, using `d>=3` -- and no compressor in the monoid they
generate carries a wall.

**Proof.**  Immediate from Theorem 6 applied to `(CG23)`.  For the second
statement, apply Theorem 6 to each identity `u_(ij)=[u_(ik),u_(kj)]`, then
use multiplicativity of `lambda` on the generated monoid.  End proof.

### 5.1a A by-product for the invariant-graph lane

The same projection settles part of a question owned elsewhere.  The
invariant-graph classification asks whether the minimal member of the family
is nondegenerate, which at weight two is the question whether the setwise
stabilizer

```text
L={g in G : g Gamma h Gamma=Gamma h Gamma}                       (CG25a)
```

equals `Gamma`; the weight-two radical vectors through the base point are in
bijection with the nonidentity cosets of `Gamma` in `L`.  Two reductions are
immediate here.

First, `L` has no `SL_d(Z)` part.  The marked element
`h=e_12((x_1...x_d)^(-1))` lies in `EL_r(R)`, as does `Gamma`, so the
projection `G->SL_d(Z)` sends `Gamma h Gamma` to `{1}`; applying it to
`(CG25a)` gives `pi_L(g)=1` and hence

```text
L<=EL_r(R).                                                      (CG25b)
```

So the twin question carries no monomial-substitution content at all: the
compression semigroup and everything else in this note is irrelevant to it.

Second, `g in L` gives `gh in Gamma h Gamma`, so `L<=Gamma.(h Gamma h^(-1))`,
and since `Gamma<=L` one may factor to get
`L=Gamma.(L cap h Gamma h^(-1))`.  Twins therefore exist if and only if some
`k in h Gamma h^(-1)` outside `Gamma` stabilizes the double coset.

That second reduction locates the search but supplies no test, and the
reason is worth recording so it is not mistaken for a shortcut: writing
`k=h gamma_0 h^(-1)`, the first-order consequence `kh in Gamma h Gamma` is
*automatic*, since `kh=h gamma_0 in h Gamma`.  The content is therefore the
full two-sided condition
`h gamma_0 h^(-1) . Gamma h gamma_2 subset Gamma h Gamma` for all
`gamma_2`, which is not of the one-sided entry-test shape that the
infinite-degree argument for this pair runs on.  Deciding it needs
denominator combinatorics in `EL_r(R_+)` that are not attempted here.  The
useful output of this subsection is `(CG25b)`.

### 5.2 Comparison with the modular obstruction

`FALSE_FINITE_INDEX_BERNOULLI_TOWER_AUDIT.md`, Section 3, contains the
group-level ancestor of Theorem 6: for a *commensurated* subgroup the
modular homomorphism

```text
Delta_Lambda(g)=[Lambda:Lambda cap g Lambda g^(-1)]
               /[g Lambda g^(-1):Lambda cap g Lambda g^(-1)]     (CG25)
```

is a homomorphism into `Q_(>0)`, and property `(T)` of the ambient group
forces it to be trivial, so a Kazhdan group cannot be generated by strict
finite-index compressors.

Theorem 6 is the operator-algebra analogue, and it applies exactly where
`(CG25)` does not.  For the Kun--Thom pair `Gamma` is *not* commensurated --
`[Gamma:t Gamma t^(-1)]=infinity` -- so `Delta_Gamma` does not exist at all,
and the compressor semigroup is not Ore, so `lambda` does not extend to a
homomorphism on `G` either.  The Steinberg relation replaces both: it
cancels a multiplicative invariant without ever leaving the semigroup.

The comparison also explains why the finite-index Bernoulli prototype of that
same note *does* carry an exact wall.  There the ambient group
`P=Gamma_infinity semidirect <t>` surjects onto `Z` by the exponent of `t`;
`lambda` descends to that homomorphism and is free to be `8` at the
compressor.  The Kun--Thom ambient group is Kazhdan and its compressor is a
commutator, so the same invariant is pinned to `1` unless it is infinite.
That is the exact sense in which the sofic prototype and the target pair are
separated by one arithmetic invariant.

### 5.3 Consistency check inside the Clifford model

The theorems above are exact statements about arbitrary `M`, so they must
hold for the Clifford crossed product itself,

```text
M_Cl=Cl(X) crossed_product G,  X=G/Gamma,                        (CG26)
```

which is a genuine finite tracial algebra whether or not it is Connes
embeddable.  There `c_(t Gamma)` centralizes `pi(Gamma_1)` because `Gamma_1`
fixes the coset `t Gamma`, and it is moved by `pi(gamma)` because
`gamma t Gamma!=t Gamma`.  Hence `N!=N_t` and `lambda(t)>1` for every strict
compressor `t`.

Corollary 7 therefore *forces*, inside `M_Cl` and with no extra hypothesis,

```text
lambda(u_13)=infinity   or   lambda(u_32)=infinity.              (CG27)
```

Statement `(CG27)` is proved, not conjectured: it is Corollary 7 applied to
the algebra `M_Cl`, which exists unconditionally.  It has a direct
combinatorial explanation, because the `Gamma`-fixed part of the site set is

```text
X^Gamma={g Gamma : g^(-1) in P_Gamma}=P_Gamma^(-1) Gamma/Gamma,  (CG28)
```

and a site operator `c_y` lies in `N` exactly when `y in X^Gamma`, because
`Ad u_gamma(c_y)=c_(gamma y)` and distinct sites carry distinct Majoranas.
So `N_s` gains exactly the sites of `s X^Gamma \ X^Gamma`, and the
combinatorial input is now available unconditionally.

**Proposition 7a (fixed sites grow infinitely).**  For the Kun--Thom
Theorem E pair and `d>=3`, both elementary transvections of `(CG23)` satisfy

```text
#(u_13 X^Gamma \ X^Gamma)=#(u_32 X^Gamma \ X^Gamma)=infinity.    (CG28a)
```

**Proof.**  First, for `nu in SL_d(Z)` the copy `(1,nu) in G` satisfies

```text
(1,nu) in P_Gamma  <=>  nu(N^d)<=N^d  <=>  nu has entries in N.  (CG28b)
```

Indeed `(1,nu)Gamma(1,nu)^(-1)=EL_r(nu(R_+))`, and this lies in
`EL_r(R_+)` if and only if `nu(R_+)<=R_+`: one direction is trivial, and for
the other the elementary matrix with entry `nu(a)` has all its entries in
`R_+`, so `nu(a) in R_+`.  Since `nu` permutes monomials by `x^v |-> x^(nu v)`
and `R_+` is spanned by the `x^v` with `v in N^d`, this is `nu(N^d)<=N^d`,
i.e. nonnegativity of `nu`.

Now take `s=u_13` and, for `n>=1`, put `m_n=I+n e_12 in L_+` and
`g_n=(1,m_n^(-1))`.  Then `g_n^(-1)=(1,m_n) in P_Gamma` by `(CG28b)`, so
`g_n Gamma in X^Gamma` by `(CG28)`.  On the other hand

```text
(s g_n)^(-1)=(1,m_n u_13^(-1)),
m_n u_13^(-1)=m_n-m_n e_13,
```

and `m_n e_13` has its third column equal to the first column of `m_n`,
namely `e_1`; so `m_n u_13^(-1)` has entry `-1` in position `(1,3)` and is
not nonnegative.  By `(CG28b)` it is not in `P_Gamma`, so
`s g_n Gamma notin X^Gamma`, while `s g_n Gamma in s X^Gamma`.  Distinct `n`
give distinct `SL_d(Z)`-components, and `Gamma` has trivial `SL_d(Z)`-component,
so the cosets `s g_n Gamma` are pairwise distinct.  Hence the difference set
is infinite.

For `s=u_32` run the same argument with `m_n=I+n e_13`: then
`m_n u_32^(-1)=m_n-m_n e_32` replaces the second column by
`col_2(m_n)-col_3(m_n)=e_2-n e_1-e_3`, which has entry `-1` in position
`(3,2)`.  End proof.

The proof uses only `(CG28b)`, which is elementary; it does not invoke the
external-projection theorem of
`FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md`, whose argument is written for the
`M_(3x2)(Z)` framing and would need transplanting.

Proposition 7a gives infinitude at two specific transvections.  The graph node
`marked-double-coset-infinite-degree` supplies the complementary general fact,
which is worth recording because it needs no choice of compressor: for *every*
strict compressor `t`,

```text
X^(s Gamma s^(-1))=s X^Gamma  for all s in G,
X^Gamma proper-subset t X^Gamma.                                 (CG28c)
```

The identity is the observation that `y Gamma` is fixed by `s Gamma s^(-1)`
exactly when `s^(-1)y in P_Gamma^(-1)`, and strictness holds because
`t Gamma in t X^Gamma` while `t Gamma in X^Gamma` would give
`t^(-1) Gamma t<=Gamma`, which together with `t Gamma t^(-1)<=Gamma` forces
`t Gamma t^(-1)=Gamma`.  So the site set grows at every compressor, and
Proposition 7a says that at `u_13` and `u_32` the growth is infinite.

What Proposition 7a does *not* do is compute `lambda(s)`.  It shows that
`N_s` gains an infinite tensor-independent family of Majoranas over `N`, so
the growth is not finite-dimensional and both candidate compressors visibly
carry it; but `lambda(s)=2^(#(s X^Gamma \ X^Gamma))` is not claimed, since
that would need the full relative commutant of the crossed product and index
is not monotone under passage to intermediate subalgebras.  What `(CG28a)`
supplies is the mechanism behind `(CG27)`, not a second proof of it.

It is worth recording that `(CG27)` is *not* implied by the known infinite
index `[Gamma:t Gamma t^(-1)]=infinity` of `notes/NOTEPAD.md`.  That is a
group-side statement about `L(t Gamma t^(-1))<L(Gamma)`, whose basic
construction the same note shows to be semifinite.  Corollary 7 is a
commutant-side statement about `N<N_t`, and the two indices are logically
independent.

## 6. Where the approximation problem actually sits

Theorems 2 and 3 concern an exact homomorphism into a finite tracial
algebra.  For the matrix endpoint `(KCP12)--(KCP13)` of
`TRUE_KUN_THOM_CLIFFORD_PHASE.md` one starts instead from normalized
Hilbert--Schmidt almost representations `pi_n:G->U(d_n)`.  Passing to a
tracial matrix ultraproduct converts them into an honest homomorphism
`pi:G->U(M)` with `M` the tracial ultraproduct, and the wall conditions
become exactly `(CG4)` respectively `(CG10)`.  So the finite endpoint and
the exact endpoint are the *same* problem, and everything above applies
verbatim.  There is no rate-sensitivity in the existence question; the
rate-sensitive criterion of `FALSE_ONE_NUMBER_RELATIVE_COMMUTANT_CRITERION.md`
is about *building* a wall from imperfect data, not about whether one
exists.

What the ultraproduct does change is which finiteness is available.

* For **exact** finite-dimensional `pi_n`, the ambient of the adjoint action
  is `B(M_(d_n))` with normalized rank, a finite trace, and the fixed spaces
  of `Gamma` and `Gamma_1` are unitarily conjugate subspaces of a
  finite-dimensional space, one contained in the other.  They collapse.
* For **operator-norm** asymptotic representations the same collapse
  survives: the adjoint maps remain an operator-norm asymptotic
  representation on `(M_(d_n),||.||_2)`, approximate Kazhdan projections for
  `Gamma` and `Gamma_1` can be rounded spectrally in operator norm, the
  compressor conjugation preserves their rank exactly, and rank equality
  plus a one-sided operator-norm containment forces the two projections
  together.  This is the established claim
  `kazhdan-asymptotic-commutant-transport`, and it kills the wall outright
  in the norm-microstate sector.
* For **normalized Hilbert--Schmidt** almost representations the adjoint
  maps are still almost multiplicative -- if `D` is the defect unitary of a
  tested product then the adjoint defect operator `1-L_D R_(D^*)` on
  `(M_(d_n),||.||_2)` has normalized Hilbert--Schmidt norm
  `sqrt(2-2|tr(D)|^2)<=sqrt2 ||D-1||_2` -- but only in normalized
  Hilbert--Schmidt norm.  The spectral rounding then controls the two
  approximate Kazhdan projections only up to a *seam* of vanishing
  normalized rank, and a single unit Hilbert--Schmidt vector can live
  entirely inside a seam of normalized rank `o(1)`.

That is the precise place where the finite-dimensional and compact-closure
obstructions lose force, and it matches the exact statement on the other
side: by Corollary 5 the wall's relative commutant has infinite index, so
the seam is not a bounded-size defect but an infinite-index one.

**Corollary 8.**  Suppose `(pi_n,v_n)` is a relative wall in the sense of
`FALSE_RELATIVE_WALL_FORCES_FLEXIBLE_HS_INSTABILITY.md`, `(WFI2)--(WFI4)`.
Then there is no operator-norm asymptotic representation
`rho_n:G->U(D_n)` with `D_n>=d_n`, `D_n/d_n->1`, and

```text
||p_n rho_n(g) p_n-pi_n(g)||_(2,d_n)->0                          (CG29)
```

for every fixed `g in G`, where `p_n` is the projection onto the first `d_n`
coordinates.

**Proof.**  Put `V_n=v_n directSum 1_(q_n)`, `q_n=1-p_n`.  The leakage
estimate `(WFI7)--(WFI8)` uses only unitarity of `rho_n(g)` and `(CG29)`,
so it gives `||q_n rho_n(g)p_n||_(2,D_n)->0` and
`||p_n rho_n(g)q_n||_(2,D_n)->0`.  Writing `[V_n,rho_n(s)]` in
`p_n directSum q_n` blocks, the diagonal `q_n`-block vanishes identically,
the two off-diagonal blocks are bounded by twice the leakages, and the
`p_n`-block equals `[v_n,p_n rho_n(s)p_n]`, which by `(CG29)` is close to
`[v_n,pi_n(s)]`.  Hence

```text
||[V_n,rho_n(s)]||_(2,D_n)->0     for every s in Gamma.
```

Apply `kazhdan-asymptotic-commutant-transport` to the operator-norm
asymptotic representation `rho_n` and the uniformly bounded almost
commutant `V_n`: it gives `||[V_n,rho_n(h)]||_(2,D_n)->0`.  Compressing,

```text
p_n[V_n,rho_n(h)]p_n=[v_n,p_n rho_n(h)p_n]
```

exactly, so `||[v_n,p_n rho_n(h)p_n]||_(2,D_n)->0`; since `d_n/D_n->1` the
`d_n`-normalized norm converges as well, and `(CG29)` at `h` together with
unitarity of `v_n` replaces `p_n rho_n(h)p_n` by `pi_n(h)`.  This
contradicts `(WFI4)`.  End proof.

Corollary 8 strengthens `TRUE_CLIFFORD_HYPERLINEARITY_FORCES_AMBIENT_HS_
INSTABILITY.md`.  That note concludes that `G` is not flexibly
Hilbert--Schmidt stable, i.e. the wall models are far from honest
finite-dimensional representations.  Corollary 8 says they are far, still
after `o(d_n)` flexible padding, from the entire operator-norm asymptotic
(MF) sector, of which exact representations are only the zero-defect
members.  A wall model must therefore have multiplicative defect which is of
order one in operator norm on a corner of vanishing normalized trace, and
must remain so under every flexible correction.

An independent route reaches a compatible conclusion with a sharp constant.
`FALSE_ONE_INVOLUTION_INSTABILITY.md`, "Theorem (antipodal radical gap)",
observes that every honest finite-dimensional representation kills a
sofic-radical element `s`, and derives
`||U_n(s)-pi(s)||_(2,d_n)>=sqrt(2-eta_n)` from antipodality alone, so the
distance to the exact sector has lower limit `sqrt2` at that single
coordinate.  Corollary 8 and that theorem are complementary rather than
nested: the gap theorem gives a constant at the marked coordinate against
exact representations, while Corollary 8 gives no constant but rules out the
whole operator-norm asymptotic sector at `h`, flexibly.  They agree because
the marked coordinate is killed in the norm-microstate sector too, by
`finite-normal-compression-obstruction` applied to the finite normal
subgroup generated by the Clifford sign in the cover `E_S` of Section 8 --
note that the marked word has infinite order in `H` itself, so that
obstruction applies to the cover, not to the amalgam.

### 6.1 Relation to a published open problem

Alekseev--Thom, arXiv:2608.05362, Open Problem 6.2 asks whether the commutant
of a Kazhdan representation into a tracial matrix ultraproduct is the
ultraproduct of the coordinate centralizers of lifts.  (The statement is
recorded as checked against the full text in
`notes/CREDIT_AND_PRIORITY_AUDIT.md`.)  That question sits directly under
Theorem 2, and a positive answer would convert the wall into a
finite-dimensional problem.

Suppose the coordinate description holds for a wall model, so that

```text
N=prod^omega A_n,     N_t=prod^omega tilde A_n,                  (CG30)
```

where `A_n` is the exact centralizer in `M_(d_n)` of the lifted
`Gamma`-window and `tilde A_n` that of the lifted `Gamma_1`-window, with
`A_n<=tilde A_n` because `Gamma_1<=Gamma`.  The trace-preserving expectation
of `(CG30)` is the ultraproduct of the coordinate expectations, so the
Pimsner--Popa inequality passes to the limit and

```text
[N_t:N]<=lim_omega [tilde A_n:A_n].                              (CG31)
```

By Theorem 2 a wall forces `[N_t:N]>1`, hence
`lim_omega [tilde A_n:A_n]>1`: the exact centralizer of the compressed
window must be strictly larger than that of the full window, uniformly along
the ultrafilter.  This is a purely finite-dimensional demand on two nested
exact centralizers, and it is the form in which a positive answer to Open
Problem 6.2 would deliver the wall question.  Conversely, no version of
Corollary 5 or Theorem 6 is available in the coordinates without that
answer, because `N` may be strictly larger than `prod^omega A_n`.  The
implication `(CG30) => (CG31)` is proved; the hypothesis `(CG30)` is open and
is stated here as a hypothesis, not asserted.

### 6.2 The conditional-expectation form of the gap

The stability lane asks for the gap in the form "small commutator energy of a
projection implies small trace on one side", and observes that property `(T)`
hands one a vector-state statement instead.  The conditional-expectation form
is available, with explicit constants, and isolating it shows that the
missing ingredient is not a better form of `(T)`.

**Proposition 11.**  Let `Gamma` have property `(T)` with Kazhdan set `S` and
constant `kappa`, let `pi:G->U(M)` with `M` finite tracial, and put
`N=M cap pi(Gamma)'`.  For every projection `p in M` there is a projection
`q in N` with

```text
||p-q||_2<=(1+sqrt2) kappa^(-1) max_(s in S)||[pi(s),p]||_2.     (CG36)
```

**Proof.**  Write `alpha` for the trace-preserving action `Ad pi|_Gamma` of
`Gamma` on `M` and extend it to `L^2(M)`.  Its fixed-point space is
`L^2(N)`, and the orthogonal projection onto `L^2(N)` is the trace-preserving
conditional expectation `E_N`.  Since
`||alpha_s(p)-p||_2=||pi(s)p-p pi(s)||_2`, property `(T)` gives

```text
||p-E_N(p)||_2=dist_2(p,L^2(N))
              <=kappa^(-1) max_(s in S)||[pi(s),p]||_2.          (CG37)
```

Put `a=E_N(p)`, so `a in N` and `0<=a<=1`.  Because `E_N` is an
`N`-bimodule map preserving `tau`, one has `tau(pa)=tau(E_N(p)a)=tau(a^2)`
and `tau(a)=tau(p)`, whence the exact identity

```text
||p-a||_2^2=tau(p)-2tau(pa)+tau(a^2)=tau(a(1-a)).                (CG38)
```

Let `q=chi_([1/2,1])(a) in N`, a genuine projection.  On `[0,1]` one has
`|t-chi_([1/2,1])(t)|<=2t(1-t)` and the left side is at most `1/2`, so
`(t-chi(t))^2<=2t(1-t)`; applying `tau` and `(CG38)`,

```text
||a-q||_2^2<=2 tau(a(1-a))=2||p-a||_2^2.                         (CG39)
```

The triangle inequality with `(CG37)` and `(CG39)` gives `(CG36)`.
End proof.

So the gap does convert: a projection with small `Gamma`-commutator energy is
`L^2`-close to a projection **in the relative commutant**, at a rate
depending only on the Kazhdan constant, and its trace is correspondingly
close to `tau(q)`.

What `(CG36)` does *not* give is the trace dichotomy.  To conclude that
`tau(p)` is near `0` or near `1` one needs to know that `N` has no projection
of intermediate trace.  That is exactly a statement about the relative
commutant -- triviality, or atomicity with atoms of large trace -- and in a
diffuse `N` it is false, since a diffuse algebra carries projections of every
trace in `[0,1]`.

**Status of the redirection (superseded for the stability lane).**  This was
written as an answer to the question "convert the gap into: small commutator
energy implies small trace on one side", and as an answer to *that* question
it stands: the obstacle is the structure of the relative commutant, not the
vector-state form of `(T)`.  The stability lane no longer needs that
conversion.  Its fiberwise block gap turned out to be the Cheeger inequality,
lower-bounding boundary energy by `min(tau(P),tau(q-P))` rather than forcing
`tau(P)` toward an endpoint, and a threshold integral consumes the minimum
directly.  So no intermediate-trace dichotomy is required there and
diffuseness of `N` is not what blocks it.  Proposition 11 remains valid and
is recorded on its own merits; it is not load bearing for that lane.

Its placement is worth stating honestly, since it constrains reuse.  The
proof needs `pi` to be a genuine homomorphism, both for `L^2(N)` to be the
fixed space and for `(T)` to apply, so it lives on the ultraproduct side --
or, at finite level, on models that are genuine representations, for instance
through finite quotients, where the Kazhdan constant is uniform because it
depends only on `Gamma`.  For almost-representations at finite level it is
unavailable.

## 7. What is now open

The wall problem has been reduced to the following, in descending order of
concreteness.

1. Construct, in some Connes-embeddable finite tracial `M` with a
   homomorphism `pi:G->U(M)`, a self-adjoint involution `w` centralizing
   `pi(t Gamma t^(-1))` whose `pi(gamma)`-conjugate anticommutes with it
   (Theorem 3).  Equivalently, make `M intersect pi(Gamma)'` grow strictly
   under one compressor (Theorem 2).
2. The growth must have infinite index at `u_13` or `u_32` (Corollary 7).
   Any candidate whose commutant growth is finite index -- in particular any
   finite lamp added over a finite orbit -- is already excluded.
3. *Closed affirmatively by Proposition 7a*: the difference sets
   `s X^Gamma \ X^Gamma` are infinite at both `u_13` and `u_32`, so the
   mechanism behind Corollary 7 is visible in the model and not only in the
   index calculus.  What remains of this item is the strictly smaller task of
   computing the full relative commutant `N` of `M_Cl`, which would turn the
   Majorana lower bound into an identity for `lambda`.
4. Decide whether property `(T)` of `Gamma` interacts with `(CG17)`.  The
   tower `N<Ad pi(t)(N)<...` consists of mutually isomorphic algebras with
   constant index, and its union is `Ad pi(t)`-invariant.  No obstruction is
   known, but no construction is known either; this is the natural place for
   a rigidity theorem to enter.
5. Alekseev--Thom Open Problem 6.2.  A positive answer puts the whole wall
   question into finite dimensions in the form `(CG31)`; a negative answer
   for this particular model would itself be evidence that the wall is
   available.  Either way it is the published question closest to this
   endpoint.
6. **The sharpest available diagnostic, after Section 8.**  The weakly sofic
   model of Theorem 9 is built from finite groups `K_n` with bi-invariant
   metrics, in each of which the two centralizers
   `N^((n))=C_(K_n)(pi_n(Gamma-window))` and
   `tilde N^((n))=C_(K_n)(pi_n(Gamma_1-window))` are finite, so
   `[tilde N^((n)):N^((n))]` is a finite number.  Yet the ultraproduct
   inclusion is proper by Corollary 10.  Exactly one of two things must
   therefore happen in Glebsky's construction applied to `E_S`:

   ```text
   (i)  [tilde N^((n)):N^((n))] -> infinity, or
   (ii) the ultraproduct centralizers are strictly larger than the
        ultraproducts of the coordinate centralizers.                (CG33)
   ```

   **Correction (2026-08-14).**  An earlier version of this item called
   `(CG33)` a dichotomy and asked which case holds.  That was wrong, and the
   error is worth stating plainly.  Case (ii) is **automatic**: for any
   approximate coordinate maps,
   `prod^omega C_(K_n)(phi_n(window))` is contained in
   `C_(prod^omega K_n)(sigma(Gamma))` and the containment is strict as soon
   as the `phi_n` are not genuine homomorphisms, since an element commuting
   with `phi_n(gamma)` only to within `o(1)` need not commute exactly at any
   single `n`.  So `(CG33)` is a disjunction with a free disjunct, not a
   dichotomy, and asking "which case" is malformed.  This is the same fact
   that forces Kun--Thom to build a cluster groupoid of almost-equivariant
   partial bisections rather than use coordinate centralizers, and it is the
   content of Alekseev--Thom Open Problem 6.2.

   What survives is the conditional already recorded as
   `(CG30) => (CG31)` in Section 6.1: **if** the coordinate description holds,
   **then** the coordinate indices diverge.  Case (i) is therefore not an
   alternative to be decided but a consequence to be drawn once Open
   Problem 6.2 is answered positively.  The practical redirection is that
   item 5 is load-bearing now, and is not waiting on any verdict about
   Glebsky's construction.

   One refinement still narrows the search, for whoever wants case (i)
   directly.  Were `phi_n` an honest homomorphism
   into the finite group `K_n`, the finite-group instance of Lemma 1 in
   Section 2 would give `[tilde N^((n)):N^((n))]=1` exactly, by comparing
   orders.  So **every coordinate index above `1` is produced by the
   multiplicative defect of `phi_n`**, and case (i) asks precisely for the
   defect to inflate that index without limit.  Where in Glebsky's
   construction the defect is deposited is therefore where to look.

   A tempting sharpening does *not* work and is recorded so it is not
   retried.  One would like to say that the bi-invariant metrics `d_n` in
   any weak-soficity model cannot be Hamming metrics, by embedding `K_n` in
   `Sym(K_n)` and comparing.  The regular action is free, so its Hamming
   length is the discrete metric, and the comparison degenerates; what
   survives is only the tautology that weak soficity does not imply
   soficity.  Any genuine statement here has to constrain which
   conjugation-invariant length functions the construction produces, not
   merely observe that they are not the regular Hamming one.

## 8. Calibration: the wall already exists in the weakly sofic category

Because Lemma 1 and Theorems 2 and 3 hold for an arbitrary target group,
they can be tested against a target where the answer is known.  That test is
now available and it is decisive about what a no-go can look like.

**Theorem 9.**  Let `Gamma<G` be the Kun--Thom Theorem E pair, `X=G/Gamma`,
let `S` be a `G`-invariant graph on `X` with `b_S(o,y)=1` at the marked pair,
let `Vtilde_S` be the central `F_2`-extension of `directSum_X F_2` with
commutator form `b_S` as in `invariant-graph-clifford-phase`, and put

```text
E_S=Vtilde_S semidirect G.                                       (CG32)
```

Then `E_S` is weakly sofic and is not sofic.

**Proof.**  Every finitely generated subgroup of `Vtilde_S` is generated by
finitely many `c_u` together with `z`, and the relations
`c_u^2=z^2=1`, `[c_u,c_v]=z^(b_S(u,v))`, `z` central, make it a finite
`2`-group of order at most `2^(m+1)`.  So `Vtilde_S` is locally finite, hence
LEF, hence sofic, hence weakly sofic.  It is normal in `E_S` with quotient
`G`, which is residually finite by Kun--Thom Theorem E.  Glebsky's
permanence theorem -- `H` normal and weakly sofic with `K/H` residually
finite implies `K` weakly sofic, quoted in full in
`research/weakly-sofic-not-sofic-proof.md` -- gives weak soficity of `E_S`.

For nonsoficity, `invariant-graph-clifford-phase` (established) provides the
surjection `H->>E_S` from the free-lamp amalgam sending the marked word `x`
to `z^(b_S(o,y))=z!=1`, and `kun-thom-clifford-radical-phase` (established)
puts `x in Rad_sof(H)`.  A sofic `E_S` would make that surjection kill `x`.
End proof.

**Corollary 10.**  The Clifford wall of Theorem 3 -- an involution `w`
centralizing `pi(t Gamma t^(-1))` whose `pi(gamma)`-conjugate anticommutes
with it, in the group sense `[w,pi(gamma)w pi(gamma)^(-1)]=z` -- is realized
in a metric ultraproduct of finite groups with bi-invariant metrics, with
the marked radical word surviving.

**Proof.**  Weak soficity of `E_S` embeds it in such an ultraproduct; the
image of `c_o` is the required element by Theorem 3 read in the target group
`U` of that ultraproduct.  End proof.

Three consequences for this endpoint.

1. **No group-theoretic no-go is possible.**  Any argument that would refute
   the wall using only Lemma 1, the compressor semigroup, property `(T)`,
   infranormality, or the presentation of `H` would refute Corollary 10 too.
   Every no-go must be metric-specific.
2. **The index invariant is exactly such a metric-specific tool.**  The
   growth index `lambda` of Section 5 needs a trace and the Pimsner--Popa
   index; a metric ultraproduct of finite groups carries neither, so
   Theorem 6 has no counterpart there and Corollary 10 is no contradiction.
   That is the precise sense in which Corollary 7 is a genuinely tracial
   obstruction rather than a restatement of the known combinatorics.
3. **The whole difficulty is the metric, not the algebra.**  The algebraic
   target of `compressed-commutant-majorana` is realizable; what is not known
   is whether it is realizable when the finite groups with arbitrary
   bi-invariant metrics are replaced by `U(d)` with the one normalized
   Hilbert--Schmidt metric.  This is the same crux that
   `weakly-sofic-not-sofic` records at the level of permanence theorems --
   whether Glebsky's theorem has a normalized-Hilbert--Schmidt analogue --
   and Theorem 9 shows the two cruxes are the same one.

A related structural datum points the same way.  Gao--Kunnawalkam
Elayavalli--Patchell, arXiv:2402.17150, prove that every action of a LERF
group on a set is sofic; since the coset action `G act G/Gamma` is not sofic
(Kun--Thom Corollary D), `G` is not LERF and `Gamma` is not separable in `G`.
So no wall construction may implicitly manufacture finite-index separating
structure for `Gamma`.  Corollary 8 is the operator-side form of the same
warning: the models must avoid the entire operator-norm asymptotic sector, in
which such separating structure is exactly what is available.

### 8.1 Corollary 8 does not obstruct the Hilbert-embeddable route

Theorem 9 feeds a live route owned elsewhere in the graph.  The established
claim `hilbert-embeddable-length-hyperlinearity` says that a countable group
which is weakly sofic *with conditionally negative definite witnessing
lengths* is hyperlinear.  Composing it with Theorem 9:

```text
if the Glebsky witnesses for E_S have Hilbert embeddable lengths,
then E_S is hyperlinear and nonsofic.                            (CG34)
```

That is a complete answer to the universal-hyperlinearity question, so it is
worth checking that the present note's necessary conditions do not forbid it.
They do not, and the reason is instructive.

In that route the finite models are `rho_n circ phi_n`, where `phi_n:E_S->K_n`
is a weak-soficity approximation and `rho_n` is an honest finite-dimensional
representation of the finite group `K_n` with
`tr rho_n(k) approx exp(-t ell_n(k))`.  Let `d` be a multiplicative defect
element of `phi_n`, so `ell_n(d)->0`.  Then

```text
||rho_n(d)-1||_2^2=2(1-Re tr rho_n(d))
                  approx 2(1-exp(-t ell_n(d)))->0,               (CG35)
```

so the composite is normalized-Hilbert--Schmidt almost multiplicative.  But
the operator norm of `rho_n(d)-1` is *not* controlled by `(CG35)`: a unitary
whose normalized trace is near one may still have eigenvalues near `-1`, on a
subspace of vanishing normalized rank.  So the composite is generally **not**
operator-norm almost multiplicative, and its defect is of order one in
operator norm on a corner of vanishing trace.

That is exactly the defect profile Corollary 8 demands of any wall model.
The Hilbert-embeddable route therefore passes the necessary condition proved
here, rather than colliding with it, and the corner on which its defect lives
is the same seam that Section 6 identifies as the only place a wall can hide.
The two lanes are describing one mechanism from opposite ends.

Three scope conditions travel with `(CG34)` and are recorded so that the
composition is not overread.  The criterion is **sufficient only**:
hyperlinearity is not known to return a weak-soficity witness, so a negative
answer for Glebsky's witnesses would not show `E_S` nonhyperlinear.
Conditional negativity is **parametrization-sensitive**, so the usable
hypothesis is the existence of one increasing `f` with `f(0)=0`, independent
of `n`, making every `f o ell_n` Hilbert embeddable; naming `f` is where the
bookkeeping lives.  And there is a structural ceiling, which has a clean
consequence here.

**Corollary 10a (the witness family cannot be character-ratio bounded).**
Any Hilbert embeddable weak-soficity witness for `E_S` must run through
finite groups **without** a uniform character ratio bound
`|chi(x)|/chi(1)<=c<1`.

**Proof.**  On a family with such a bound, every Hilbert embeddable
invariant length is uniformly bi-Lipschitz to the discrete length (the Gluck
calibration in `hilbert-embeddable-length-hyperlinearity`), so the witness
would be an LEF witness and `E_S` would be LEF.  But LEF implies sofic, and
`E_S` is not sofic by Theorem 9.  End proof.

The same argument applies verbatim to the wreath `W`, since it too is
nonsofic, so this is a constraint on the whole family targeted by
`hilbert-embeddable-witness-for-kun-thom-wreath` rather than a peculiarity of
the cover.  It is a real restriction and not obviously an obstruction:
Glebsky's finite groups arise as projections of closed subgroups of products
of finite groups and carry large abelian quotients, which is the opposite of
the quasirandomness a uniform character ratio bound expresses.  But it does
say where a proof attempt must not look.

## References

* M. Pimsner and S. Popa, *Entropy and index for subfactors*, Ann. Sci.
  Ecole Norm. Sup. 19 (1986), for the index of an inclusion of finite von
  Neumann algebras with respect to the trace-preserving expectation, its
  behaviour in towers, and the characterization of index one.
* V. Jones, *Index for subfactors*, Invent. Math. 72 (1983).
* G. Kun and A. Thom, *Nonsofic wreath products of residually finite
  groups*, arXiv:2608.06222v1, Theorems A, C and E.  Theorems A and E are
  quoted verbatim from a PDF read in `research/wreath-not-sofic.md`; the
  Theorem C statement used in Section 3.1 is a paraphrase from the same read
  and carries no load here.
* V. Alekseev and A. Thom, *Centralizers of sofic approximations of Kazhdan
  groups*, arXiv:2608.05362, Open Problem 6.2; statement recorded as checked
  against the full text in `notes/CREDIT_AND_PRIORITY_AUDIT.md`.
* L. Glebsky, *Extensions of a residually finite group by a weakly sofic
  group are weakly sofic*, Rev. Mat. Iberoam. 39 (2023) 1097--1104,
  Theorem 1.1; quoted in full from the published PDF in
  `research/weakly-sofic-not-sofic-proof.md`.
* T. Gao, S. Kunnawalkam Elayavalli and G. Patchell, arXiv:2402.17150, for
  soficity of all set actions of LERF groups.
* In-repo: `TRUE_KUN_THOM_CLIFFORD_PHASE.md`,
  `FALSE_FINITE_INDEX_BERNOULLI_TOWER_AUDIT.md`,
  `notes/NOTEPAD.md` ("The compressor has infinite index"),
  `FALSE_RELATIVE_BICOMMUTANT_ENDPOINT.md`,
  `FALSE_RELATIVE_WALL_FORCES_FLEXIBLE_HS_INSTABILITY.md`,
  `FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md`,
  `FALSE_ONE_NUMBER_RELATIVE_COMMUTANT_CRITERION.md`,
  `FALSE_COMPACT_BOGOLIUBOV_APPROXIMATION_FOR_KUN_THOM.md`.

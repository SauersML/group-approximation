# Independent recheck, and the unconditional affine instantiation

Date: 2026-09-08. Companion to
`research/artifacts/compression-locally-finite-centralizer-criterion-2026-09-08.md`,
which transcribes the supplied criterion. This file is a second,
independent pass over that argument by a different session, plus the
one thing that note leaves undone: it discharges the conditional
hypotheses of its Sections 6--7 against a base this repository has
already established, and it says precisely which part of the resulting
statement was not previously reachable here.

No Lean endpoint is claimed. Nothing below is a literature-novelty claim.

## 1. What was rechecked, and how

Every displayed step of Sections 1--7 of the companion artifact was
re-derived from the hypotheses rather than read for plausibility. The
steps that carry weight, and the verdict on each:

* The spectrum of the ultraproduct operator `A` lies in
  `{0} union [kappa^2,infinity)`. Correct: `A` vanishes on the invariant
  vectors and the Kazhdan inequality bounds it below by `kappa^2` on
  their orthogonal complement.
* `||A_n P_n||->0` and `||(R_n(t)-I)P_n||->0`. Correct. Both
  contradiction arguments produce a genuine eigenvector, respectively a
  genuine `S`-invariant unit vector, in the ultraproduct; the second
  needs the observation that an `S`-invariant vector is `L`-invariant,
  which is the Kazhdan inequality applied to its component orthogonal
  to the invariant vectors.
* The spectral bound `||(I-P_n)zeta||^2 <= (2/kappa^2) sum_s
  ||R_n(s)zeta-zeta||^2`. Correct, using that `A_n` commutes with `P_n`
  so the two spectral pieces of `<A_n zeta,zeta>` are separately
  nonnegative.
* `||(R_n(s)-I)R_n(u)^* P_n||->0` from `u s u^-1 in L`. Correct; this is
  where `uLu^-1<=L` enters, and it is the only place it enters.
* The reversal `||(I-P)UP||=||(I-P)U^*P||`. Correct, and it is the step
  that forces finite dimension. See Section 2.
* Correction of a fixed finite group in the same matrix size. Correct,
  and this repository already carries it as an established claim; see
  Section 4.
* The rank normalization. Correct, and it is the step the whole theorem
  turns on. See Section 2.
* The exact averaging identity
  `|H|^-1 sum_(h in H) a_(h,n) = 0` and the resulting contradiction
  `sqrt(r_n)=o(sqrt(r_n))`. Correct.
* Sections 5--7: the wreath support calculations, the finite `L_j`-orbit
  count, residual finiteness of `B^X semidirect L_j`, the permutation
  soficity model, and both containments of `Rad_MF(W)=D_W(L)=B^X`. All
  correct. The lower containment in the defect computation uses only
  `[b_y,ell]=b_y b_z^-1` and `[a_y,b_y b_z^-1]=[a,b]_y`, both of which
  are direct calculations in the restricted direct sum.

What this recheck does not do: it is a reading of a written proof by a
model, not a kernel check and not an external referee report. No
declaration in `GroupApproximation/` corresponds to the criterion.

## 2. The two steps that are not bookkeeping

**The rank normalization.** With `p` the complement of the fixed-point
projection of `[F,F]`, `r=rank(p)`, and `T_c=rho(c)p`, the quantity that
must be shown small is `||V(s)T_c V(s)^*-T_c||_HS / sqrt(r)`. Writing
that difference as `[V(s),T_c]V(s)^*` exhibits it as a matrix of rank at
most `2r`, so its Hilbert--Schmidt norm is at most `sqrt(2r)` times its
operator norm. Dividing by `sqrt(r)` leaves `sqrt(2)` times an operator
norm that tends to zero. The ambient dimension `d_n` never appears. This
is why the argument survives `r_n/d_n->0`, and it is the reason the
criterion needs no uniform bound on the active dimension of the finite
subgroup -- the hypothesis that
`uniform-finitary-rank-compression-is-mf-compatible` and
`uniform-finite-support-rank-gap-upgrades-compression-collapse` are
about.

**The finite-dimensional reversal.** For a projection `P` and a unitary
`U`, the two off-diagonal blocks satisfy
`||(I-P)UP||^2=||P-B^*B||` and `||(I-P)U^*P||^2=||P-BB^*||` with
`B=PUP` on `ran(P)`. Equality of the two needs `B^*B` and `BB^*` to have
the same spectrum, which for a square matrix is automatic and in
infinite dimensions is false at `0`. The unilateral shift `S` with
`P=I` shows the gap concretely: `S^*S=I` while `SS^*=I-e_00`, so the two
sides would read `0` and `1`. So the word "finite-dimensional" in the
compression lemma is load-bearing, not a convenience, and any later
attempt to run this argument in a II_1 or B(H) setting must replace it.

## 3. The unconditional affine instantiation

The companion artifact states its Sections 6--7 conditionally: it
assumes a countable residually finite property-`(T)` group with a proper
finite-index injective endomorphism, and, for the radical computation,
residual finiteness of the resulting ascending HNN extension. It imports
no concrete base. This repository already has one.

Take the level-three affine congruence group of
`affine-congruence-source-is-kazhdan`,

```text
P = Gamma(3) ltimes Z^3,    Gamma(3) = ker(SL_3(Z)->SL_3(Z/3)),
```

finitely presented, torsion-free, with property `(T)`, and the
translation dilation `alpha(g,v)=(g,2v)`, injective with image
`Gamma(3) ltimes 2Z^3` of index `8`, and with `(1,e_1)` outside the
image. Realize its ascending HNN extension faithfully inside
`GL_4(Z[1/2])` as

```text
H = { [[2^h A, v],[0,1]] : h in Z, A in Gamma(3), v in Z[1/2]^3 },
t = [[2I,0],[0,1]],   t [[A,v],[0,1]] t^-1 = [[A,2v],[0,1]],
```

so that `H = (Gamma(3) ltimes Z[1/2]^3) semidirect Z` with the height
`h` as the retraction to `Z`, and `union_(n>=0) t^-n P t^n` is the whole
kernel of the height. Put

```text
L = P,   u = t,   X = H/L,   W = A_5^(X) semidirect H.
```

Then `uLu^-1=alpha(P)<L` properly with index `8`, and `ell=(1,e_1)` lies
in `L` outside `uLu^-1`, so `ell uL != uL`. Every hypothesis of the
companion's Sections 5--7 holds:

* `L` has property `(T)` and is residually finite;
* the self-embedding is injective, proper, and of finite index `8`;
* `H` is residually finite. Two independent reasons: `H` is a finitely
  generated subgroup of `GL_4(Q)`, so Malcev applies; and explicitly,
  reduction of `Z[1/2]` modulo an odd integer `q` is defined, and for a
  nonidentity element some entry of `2^h A - I` or of `v` has nonzero
  image for all large odd `q`.

So, unconditionally,

```text
W = A_5^(H/L) semidirect H
```

is a countable sofic group that is not MF, with

```text
Rad_MF(W) = D_W(L) = A_5^(H/L),      W/Rad_MF(W) ~= H.
```

The radical here is infinite, locally finite, perfect and residually
finite, and it is exactly the intrinsic compression-centralizer defect.

Nothing in this section is new mathematics on top of the companion
artifact and `affine-congruence-source-is-kazhdan`. It is the
composition, recorded because the companion explicitly declines to make
it.

## 4. What was, and was not, already reachable here

Two prerequisites of the criterion are already established claims in
this graph, and the criterion should be read as consuming them rather
than reproving them:

* `corona-representations-are-exact-on-locally-finite-subgroups`, item
  1, is the dimension-free exact correction of a finite subgroup that
  the companion's Section 3 proves again from scratch.
* `opnorm-packet-exactification-is-dimension-free` is the packet form of
  the same fact.

More importantly, the non-MF half of Section 3 above was **already
reachable** from `finite-dimensional-kazhdan-fixed-algebra-transport`,
and neither the supplied note nor the companion transcription says so.
Here is the argument, so that the novelty claim is not overstated. In
`W=B^X semidirect H` with `X=H/L`, let `O` be the `L`-orbit of `uL`. Its
size is `[L:uLu^-1]`, which is `8` in the instantiation above and finite
in every ascending-HNN application. So `F=B^O` is a **finite** subgroup
normalized by `L`, `A=C^*(rho(F))` is a finite-dimensional subalgebra
normalized by `rho(L)`, and the coordinate element `b_(uL)` is
centralized by `uLu^-1`. Fixed-algebra transport then gives
`rho(b_(ell uL))=rho(b_(uL))` for every `ell in L`; distinct coordinates
of a restricted direct sum commute, so the common image of `B` is
abelian, and perfectness of `B` kills it. That is the same conclusion.

So the genuine gains of the new criterion over what this repository
already had are these three, and only these:

1. **No finite index.** Fixed-algebra transport needs the `L`-orbit of
   the marked site to be finite, because it needs a finite-dimensional
   invariant algebra. The new criterion needs one element
   `ell in L \ uLu^-1` and nothing else, so it applies when
   `[L:uLu^-1]` is infinite and the orbit algebra is not
   finite-dimensional.
2. **No ambient structure.** The statement quantifies over a locally
   finite subgroup of a centralizer with a commuting-conjugate
   configuration. It mentions no wreath product, no normality, and no
   invariant algebra, so it is available to configurations that are not
   presented as lamp groups.
3. **A locally finite radical.** The radical computed in Section 3 is
   locally finite. The radical of
   `finite-block-perfect-lamps-have-exact-mf-radical` is the free
   product `*_j (A_5)^8`, which contains a free group of rank two and so
   is not locally finite. The two constructions trade against each
   other: the finite-block group is finitely presented and its radical
   is not locally finite; the ordinary wreath here is not finitely
   presented and its radical is.

The soficity half of Section 3 does use the finite index, through the
finite `L_j`-orbits, and makes no claim about infinite-index
self-embeddings.

## 5. Relation to the open locally finite normal question

`locally-finite-defect-subgroup-dies-in-every-corona` asks for every
locally finite **normal** `A <= D_G(L)` to die in every corona. The
group of Section 3 is a confirming instance of that statement, and the
first one recorded here in which `A` is infinite, locally finite,
noncentral, and equal to the whole defect: `A_5^(H/L)` is normal in `W`,
locally finite, contained in `D_W(L)`, and killed.

It is not a proof of the open claim, and the reason is exact. The
criterion consumes `[uCu^-1, ell uCu^-1 ell^-1]=1`. Normality of `A`
together with `A <= D_G(L)` does not produce that relation: it gives no
element of `L` moving a conjugate of `A` off itself, and in the intended
Jacobson and elementary-group applications the conjugates of the marked
root do not commute. The instance above supplies the configuration by
hand, from disjointness of lamp supports.

The provenance constraint recorded on that open node is respected: no
rescaled displacement cocycle and no Delorme--Guichardet step appears
anywhere in the criterion or in this file.

## 6. Provenance

The mathematics is the user-supplied note of 2026-09-08, transcribed in
the companion artifact by another session in this repository. This file
adds the second recheck of Sections 1--7, the counterexample motivating
Section 2, the instantiation of Section 3, and the reachability
comparison of Section 4.

The supplied note carries its own exposure qualification, which is not a
verification claim by this repository. One item in it needs a local
correction: the note presents the finite perfect lamp, and `A_5` in
particular, as the application of its criterion. That move is not new
here. It is already the content of
`finite-block-perfect-lamps-have-exact-mf-radical` and of Theorem B of
the 2026-09-07 finite-block artifact, whose own origin is recorded
separately as a generalization of Eckhardt's Theorem 4.3 from `Z/2`
lamps to arbitrary finite perfect lamps. Read against that record, the
new content of the supplied note is the criterion itself and the removal
of the finite-index hypothesis, not the choice of lamp.

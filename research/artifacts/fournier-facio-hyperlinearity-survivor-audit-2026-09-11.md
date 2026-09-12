# Fournier--Facio hyperlinearity: survivor audit and the wreath-shift core

Date: 2026-09-11.  Lane `ff-hyperlinear`.

**Status.**  No decision.  This artifact (1) lists every recorded witness
shape for hyperlinearity of the torsion-free Fournier--Facio group `G`,
together with what kills it and exactly which hypotheses the killer uses;
(2) proves that every surviving witness falls into one of two faces; and
(3) records a new group-theoretic core of `G` and its tracial consequence,
which apply to every nontrivial normalized-HS model, not just to one witness
architecture.  The negative side (a universal normalized-HS no-go) is owned
by lane `ff-hyperlinear-2` and is not authored here.

Notation from `fournier-facio-torsion-free-skeleton`: `G` is finitely
presented, torsion-free, Kazhdan; `Gamma=pi(P)<=G` is Kazhdan and infinite;
`t=t_1` has `t Gamma t^-1<=Gamma`; `S` is a finitely presented infinite simple
torsion-free group, `pi|_S` injective; `J=t^-1 pi(S) t` has `[Gamma,J]=1`,
`Gamma cap J=1`, `t J t^-1=pi(S)<=Gamma`.  The established strong form of
`defect-normally-generates-torsion-free-quotient` gives `<<pi(S)>>^G=G`.

## 1. The recorded witness shapes and their killers

| Witness shape (route) | Killer (established claim) | What the killer actually uses |
| --- | --- | --- |
| `fournier-facio-monomial-banach-limit-witness` | `fournier-facio-monomial-near-witness-impossible` | nonsoficity of `G` (Elek--Szabo) |
| `fournier-facio-induced-schreier-charge-extension` | `fournier-facio-compression-coset-charge-impossible` | property (T) of `G` plus `[G:Gamma]=infinity` (non-coamenability) |
| `fournier-facio-compactly-blurred-monomial-witness` | `fournier-facio-compact-monomial-near-witness-impossible` | pure singularity, then the monomial no-go |
| `fournier-facio-asymptotically-one-sparse-near-witness` | `fournier-facio-charge-null-monomial-perturbations-impossible` | the left null ideal of the charged state, then the monomial no-go |
| `fournier-facio-finite-band-block-near-witness` | `fournier-facio-bounded-block-near-witness-impossible` | compactness of `U(m)`, torsion-freeness, nonsoficity |
| `fournier-facio-tight-unbounded-block-near-witness` | `fournier-facio-block-dimension-escapes-every-charge-cutoff` | restriction to a bounded stratum, then the bounded-block no-go |
| `fournier-facio-tight-finite-component-overlap-witness` | `fournier-facio-generator-support-components-escape-cutoffs` | support components are reducing, then the bounded-block no-go |
| `fournier-facio-amenable-hyperfinite-exhaustion-closes-overlap` | `fournier-facio-hyperfinite-support-exhaustion-misses-cutoff` | an exact calibration: the bilateral shift of `Z` |
| `fournier-facio-null-boundary-cartanization-closes-overlap` | `fournier-facio-dimension-at-infinity-escape-is-sharp` | an exact calibration: signed-square cyclic splice of `Z` |
| `fournier-facio-bounded-spectral-type-block-witness` | `fournier-facio-fixed-block-spectrum-escapes` | nonsoficity, torsion-free power recurrence |
| `fournier-facio-biased-dense-spectrum-block-witness`, `fournier-facio-irrational-scalar-fixed-block-witness` | `fournier-facio-fixed-block-actor-is-charge-haar` | torsion-freeness and columnwise essential freeness |

**Calibration of the fence itself.**  Apart from the coset-charge killer,
every killer uses the group only through three facts: `G` is nonsofic,
torsion-free, and the witness is essentially free.  None of them uses the
compression letters `t_1,t_2`, the commuting simple group `J`, or property
(T) of `Gamma` except through nonsoficity.  The two calibrations are exact
models of `Z`.  So the recorded region is a fence for essentially free
amenable near representations of **any** torsion-free nonsofic group.  A
decision for `G` must use more of `G` than nonsoficity; Section 3 isolates
the first such structure.

## 2. The two surviving faces (exhaustive)

Let `(ell^2(X),mu,pi)` be any Kahl--Schneider witness for `G`, and take the
comparison unitaries `B_s=pi(s)` for a finite generating set.  Let `C(x)` be
the support component of `x`.
`fournier-facio-generator-support-components-escape-cutoffs` gives
`mu({|C(x)|<=m})=0` for every finite `m`.  The set `{|C(x)|=infinity}` is a
union of components, so it is invariant under all comparison words, and the
restriction-and-normalization step of that proof applies to it and to its
complement.  So every witness yields a witness of one of two kinds.

- **(S1) Infinite support components.**  Positive charge on components of
  infinite size.  The bilateral-shift calibration shows that amenability,
  pure singularity, regular character, and hyperfinite exhaustion are all
  compatible with this face.
- **(S2) Dimension at infinity.**  All charge on finite components, with
  sizes escaping every cutoff in charge.  The components then form a common
  finite-block system for all comparison words.  Some `g!=1` fixes positive
  block charge (nonsoficity), and on that sector its internal actor has Haar
  charged spectrum and asymptotically orthonormal Krylov windows
  (`fournier-facio-fixed-block-actor-is-charge-haar`).  The signed-square
  splice realizes this one-actor law.

**Caveat.**  Both faces are relative to the charged orthonormal basis of a
presentation of the witness.  The criterion lets the basis be chosen, so a
universal no-go cannot be a statement about one face; it has to be
basis-free.

**Calibration of face (S2)** (`fournier-facio-dimension-face-holds-every-approximation`).
Take any ordinary normalized-HS approximation `phi_n:G -> U(d_n)`.  Rotate
each block by a Haar unitary whose columns concentrate (Levy), and put the
ultralimit of uniform block charges on the disjoint union of the bases.  This
gives a Kahl--Schneider witness on face (S2) with trivial block action.  So
face (S2) contains every hyperlinear approximation.  Its recorded laws (block
dimension escape, spectral escape, Haar fixed-sector law) cost an actual
approximation nothing beyond the regular character.  No combinatorial fence on
(S2) can close the positive branch without proving nonhyperlinearity outright.
The exotic face is (S1); a universal no-go has to act on (S2), that is, on
ordinary normalized-HS approximations.

## 3. New core: a wreath shift inside `G`

Put `J_k=t^k J t^-k` for `k in Z`.  The following are proved in
`fournier-facio-simple-wreath-shift-proof` and
`fournier-facio-quotient-wreath-heredity-proof`.

```text
(W1)  J_k <= Gamma                              for k >= 1;
(W2)  [J_a,J_b]=1                               for a != b;
(W3)  J_-k <= C_G(Gamma)                        for k >= 0;
(W4)  the multiplication map  (+)_(k in Z) J_k -> G  is injective;
(W5)  S wr Z = ((+)_Z S) x| Z  embeds in G, with Z generated by t;
(W6)  Gamma x (+)_(k<=0) J_k <= G   (internal direct product);
(W7)  Gamma >= J_1 x ... x J_n x t^n Gamma t^-n  for every n >= 1.
(W8)  every homomorphism from G is trivial or injective on S wr Z.
```

The key step in (W4) is elementary: a normal subgroup of a restricted direct
sum of centerless groups that meets every summand trivially is trivial.
(W8) uses `<<pi(S)>>^G=G`: a kernel meeting `pi(S)` contains it (simplicity),
hence contains `G`.

(W7) is a **self-similar tail**, the same shape as the cylinder
self-similarity of Thompson's `V` in the Leavitt lane: the Kazhdan subgroup
`Gamma` contains one simple slot `J_1` times a conjugate copy of itself, and
iterates.  If `S` lacks property (T), as for Burger--Mozes lattices, which act
on a tree without a global fixed point, each inclusion in (W7) is proper,
because equality would make `S` a quotient of `Gamma`.

**Consequences for the positive branch.**  Every nontrivial quotient of `G`,
and in particular every hyperlinear nontrivial quotient, contains `S wr Z`.
So hyperlinearity of `G`, or even existence of one nontrivial hyperlinear
quotient, forces hyperlinearity of the chosen simple factor `S`.  The positive
branch therefore contains the question for `S`.

## 4. The tracial consequence: every model carries a Hilbert-hotel shift

`fournier-facio-regular-models-carry-commutant-shift`.  Let `(M,tau)` be a
finite von Neumann algebra with faithful normal trace and `u:G -> U(M)` a
nontrivial homomorphism.  Put `A=u(Gamma)' cap M` and
`theta(x)=u(t)^* x u(t)`.  Then

```text
theta(A) <= A cap u(J_0)',        u(J_-k) <= A        (k >= 0),
theta(u(J_-k)) = u(J_-(k+1)),     theta(A) != A,
theta^n(A)' cap A >= u(J_0 J_-1 ... J_-(n-1))''.
```

With the regular character, `u((+)_(k<=0) J_k)''` is the infinite tensor
product of copies of the II_1 factor `L(S)` (an infinite simple group is
ICC), `theta` shifts it, and `u(Gamma)''` contains `L(S)^(tensor n)` tensored
with `Ad(u(t))^n(u(Gamma)'')` for every `n`.

**Why this is the right differential.**  A finite-dimensional algebra has no
proper unital injective endomorphism.  In every nontrivial tracial model,
`theta` is proper and its relative commutants grow by one `L(S)` factor at
each step.  So an argument that reaches a contradiction by comparing
finite-dimensional commutants cannot be run directly on a normalized-HS
model: it first has to exactify an unbounded tensor tail at fixed precision.
This is the same uniform input recorded in
`conjugate-commuting-perfect-copies-force-exponential-dimension`, since the
`J_k` are pairwise commuting conjugate copies of the perfect group `S`.

## 5. Next attacks

- **Positive (this lane's recommendation).**  Build the witness on face (S1)
  with `t_1` acting as a bilateral shift of tensor slots indexed by `Z`, `J_k`
  on slot `k`, and `Gamma` on the tail `k>=1` through (W7).  The unresolved
  part is the part of `Gamma` outside `J_1 x t Gamma t^-1`, which must mix slot
  one with the tail while keeping near multiplicativity, together with the
  second compression letter `t_2`.  This is a self-similar tail equation for a
  model of `Gamma`, and it needs a hyperlinear model of `S` as input.
- **Negative (lane `ff-hyperlinear-2`).**  Any universal no-go has to forbid
  the Hilbert-hotel shift of Section 4 quantitatively in `R^omega`.
- **Correction (second pass).**  The bilateral-shift ansatz above is wrong for
  two compressors.  See Section 6.
- **Recorded sufficient condition.**  `fournier-facio-simple-factor-not-hyperlinear`
  closes the negative branch through (W8).  It is at least as hard as
  producing a first non-hyperlinear group, and is recorded only to make the
  permanence explicit in the graph.

## 6. Second pass: the positive construction and its gates

**Tree slots.**  `fournier-facio-compression-tree-lamp-group`.  The skeleton
has `P >= S x P_1 x P_2` with `u_i P u_i^-1 = P_i`.  Pushing that triple
through both stable letters gives independent pairwise commuting copies
`S_w = t_w pi(S) t_w^-1`, `w in {1,2}^*`, all inside `Gamma`, with `Ad(t_i)`
acting as the prefix map `w -> iw`.  Both parent copies
`t_i^-1 pi(S) t_i` centralize `Gamma`.  `S_2` commutes with every `J_k`, so
the Z-indexed slots of Section 5 cannot host it.  A model has to be a tensor
product over the rooted binary tree plus parents, with `t_1,t_2` acting as
the two child shifts.

**What blocks the model.**

1. *Simple factor.*  Any witness restricts to a hyperlinear model of `S`.
   None is recorded for any finitely presented infinite simple group.
   - A finitely presented simple group is isolated in the space of marked
     groups, so marked limits add nothing.
   - A residually amenable infinite simple group is amenable.
   - Amenable-amalgam permanence (Brown--Dykema--Jung) would need a splitting
     of `S` over an infinite amenable edge group; no such example is recorded.
2. *Kazhdan subgroup.*  `Gamma = pi(P)` is the image, under a quotient
   controlled only on finite sets, of an Osin small-cancellation Kazhdan
   group containing a universal finitely presented torsion-free group.  The
   elements outside `pi(S) alpha_1(Gamma) alpha_2(Gamma)` have no explicit
   description, so the self-similar formula cannot define them.
   Hyperlinearity of `Gamma` is gated by the peer node
   `fournier-facio-compression-subgroup-not-hyperlinear`.
3. *Joint model.*  With `N = u(Gamma)''`, a witness needs unitaries in
   `R^omega` compressing `N` onto commuting subalgebras, with
   `N >= L(S) tensor Ad(v_1)(N) Ad(v_2)(N)`, compatible with the extra
   relations of `G`.  `G` is a proper quotient of the double ascending HNN
   extension of `Gamma`, because it is Kazhdan and that extension surjects
   onto `F_2`.  The double HNN kernel is a tree of groups amalgamated over
   the Kazhdan group `Gamma`, so amenable-amalgam permanence does not apply
   even when `Gamma` is hyperlinear.

`L(Gamma) >= L(S) tensor L(Gamma) tensor L(Gamma)` exists as an abstract
inclusion of II_1 factors, because the group inclusion exists.  So the only
obstruction is `R^omega`-embeddability itself, and no finite bookkeeping in
the tensor model can decide it.

**Recommendation.**  Put the positive tensor model on hold.  It becomes
actionable only after gate 1 (a hyperlinear finitely presented infinite simple
torsion-free group) and gate 2 (a hyperlinear model of `Gamma`) are resolved.
Neither is specific to this group.

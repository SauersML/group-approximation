# Finite-rank compression defects: three boundaries of the criterion (ingestion, 2026-09-09)

## 0. Provenance and scope

Source: a user-supplied note of 2026-09-09 titled "Finite-rank compression
defects: a characteristic dichotomy", written against the manuscript's
compression criterion and its four-coordinate torsion proposition.  Every
statement below was re-derived here before being wired; the note's
identities for the four-coordinate configuration were checked exactly in
the normal form `s^i t^j` of `Z<s,t | ts = 1>`.

Mechanisms used: finite-group cardinality, finite-dimensional linear
algebra, the faithful shift model of the Jacobson algebra, Kaplansky's
trace argument for group rings, and a two-line Hilbert--Schmidt
computation on permutation matrices.  No cocycle, coboundary, weighted or
rescaled Hilbert--Schmidt norm, rank metric, or lifting theorem occurs
anywhere in this file or in the nodes that cite it.  The excluded external
manuscript is not a premise of anything here.

Throughout, for `L <= G`,

```text
D_G(L) = << [u c u^-1, l] : u L u^-1 <= L,  c in C_G(L),  l in L >>_G,
```

the compression--centralizer defect of the manuscript, and "criterion (2)"
is `normal-kazhdan-defect-non-mf`: `L <= G` Kazhdan, `K <| G` Kazhdan,
`K <= D_G(L)` implies every homomorphism from `G` to an MF group kills `K`.

## 1. Locally residually finite targets kill every compression defect

Node: `locally-residually-finite-targets-kill-compression-defects`.

If `L <= G` is finitely generated, `Q` is locally residually finite (every
finitely generated subgroup residually finite), and `phi : G -> Q`, then
`phi(D_G(L)) = 1`.  Proof: for a defining generator `d = [u c u^-1, l]`,
the group `Q_0 = <phi(L), phi(u), phi(c)>` is finitely generated, hence
residually finite; in a finite quotient with images `A, v, b` of
`L, u, c`, the inclusion `v A v^-1 <= A` of finite sets of equal size is
an equality, so `v b v^-1` centralizes `A` and the image of `d` is `1`.
Residual finiteness gives `phi(d) = 1`; normality of the kernel finishes.
No property (T), finiteness, or centrality is used.

## 2. The finite-rank kernel theorem

Node: `finite-rank-kernel-forces-abelian-defect-subgroups`.

Let `k` be a field, `G <= GL_k(V)` (faithful, `V` arbitrary), `N <| G`
with `a - I` of finite rank for every `a in N`, `G/N` locally residually
finite, `L <= G` finitely generated, and `K <| G` finitely generated with
`K <= D_G(L)`.  Put `E = sum_(a in K) (a - I)V`.  Then `E` is finite
dimensional and `G`-invariant, `K` acts trivially on `E`, and

```text
K -> Hom_k(V/E, E),   a |-> a - I
```

is an injective additive homomorphism.  So `K` is free abelian of finite
rank when `char k = 0`, and finite elementary abelian of exponent `p`
when `char k = p`.  In particular a normal Kazhdan `K <= D_G(L)` is
trivial in characteristic zero, and is a finite elementary abelian
`p`-group in characteristic `p`.

Proof sketch (the route carries the full argument).  Section 1 applied to
`G -> G/N` gives `K <= N`.  For generators `a_1..a_r` of `K`, the space
`E_0 = sum_i (a_i - I)V` is finite dimensional and each `a_i` maps it into
itself, hence onto itself; the identities `ab - I = (a - I) + a(b - I)` and
`a^-1 - I = -a^-1(a - I)` give `(a - I)V <= E_0` for all `a in K`, so
`E = E_0`.  Normality of `K` makes `E` `G`-invariant, and the restriction
`G -> GL_k(E)` kills `D_G(L)` by `compression-defect-dies-in-finite-dimensions`
(no Malcev theorem is needed).  With `T_a = a - I` one gets `T_a T_b = 0`
and `T_(ab) = T_a + T_b`; injectivity is faithfulness of `G` on `V`.

## 3. The integral Toeplitz--Jacobson algebra: no normal Kazhdan witness

Node: `integral-jacobson-defect-has-no-normal-kazhdan-subgroup`.

`J_Z = Z<s,t | ts = 1>` acts faithfully on `V = Q^((N_0))` by the shift
(`jacobson-shift-representation-is-faithful`), `e = 1 - st` is the
projection onto `Q v_0`, `f_(ij) = s^i e t^j` are matrix units, the ideal
`I = J_Z e J_Z = M_fin(N_0, Z)`, and `J_Z / I = Z[z, z^-1]`.  For
`Delta <= GL_n(J_Z)` put `N = Delta cap ker(sigma)`, `sigma` the symbol
map to `GL_n(Z[z,z^-1])`; every element of `N` differs from `I` by a
finite-rank operator on `V^n`, and `Delta/N` embeds in the residually
finite group `GL_n(Z[z,z^-1])`.  Section 2 applies:

> For every `n >= 1`, every `Delta <= GL_n(J_Z)`, every finitely generated
> `L <= Delta`, and every finitely generated `K <| Delta` with
> `K <= D_Delta(L)`, the group `K` is free abelian of finite rank.  If `K`
> has property (T), or merely finite abelianization, then `K = 1`.

So criterion (2) has no nontrivial instance inside `GL_n(J_Z)` at any
matrix size, in any subgroup, and for any homomorphic encoding of a
witness.  The defect itself is not trivial: the manuscript's
four-coordinate configuration (`prop:torsion-defect-ring`) gives, over
`J_Z`, a central `z = diag(1,1,1,1 + f_12)` in `D_B(L)` with
`z^m = diag(1,1,1,1 + m f_12) != 1`, so `<z> = Z`; and the extraction
identities `[z, e_41(f_20)] = e_41(f_10)`, `[e_24(t), e_41(f_10)] = e_21(e)`
put every `e_(ij)(e)` into `D_G(L)` for `G = EL_4(J_Z)`, where the
`e_(ij)(e)` with `i, j <= 3` generate a copy of `SL_3(Z)` -- a Kazhdan
subgroup of the defect that, by the theorem, is not normal.  Over
`J_(F_p)` the same `z` has order `p`, which is exactly the finite central
witness the torsion theorem consumes.

## 4. The ring equivalence is false

Node: `stably-finite-group-ring-with-non-mf-elementary-groups`.

`R = Z[H]`, `H = L_(F_2)(1,2)^x`, is a finitely generated stably finite
unital ring (`Z[H] <= C[H] <= C*_r(H)`, whose faithful trace makes every
one-sided inverse in every matrix size two-sided), while `EL_n(Z[H])` is
not MF for every `n >= 2`: `diag([a,b],1) = [diag(a,a^-1), diag(b,1)]`
lies in `EL_2(R)` for units `a, b`, `H` is perfect, so
`h |-> diag(h,1)` embeds the non-MF group `H` into `EL_2(R)`, and MF
passes to subgroups.  Hence "`EL_n(R)` MF iff `R` directly finite" fails
in the direction "finite ring implies MF group", even with stable
finiteness.  Only the implication "`EL_n(R)` MF implies `R` directly
finite" remains a target; it is established in positive characteristic at
`n >= 4` (`finite-additive-order-one-sided-defects-are-mf-invisible`) and
open in characteristic zero
(`integral-jacobson-elementary-group-is-not-mf`).

## 5. The normalized Hilbert--Schmidt analogue of criterion (2) is false

Node: `hs-analogue-of-normal-kazhdan-criterion-is-false`.

The manuscript's `W = Cl(X) x| V` is sofic (`sofic-non-mf-witness`), its
level-zero `Gamma = Z^3 x| SL_3(Z)` is Kazhdan, and the central involution
`epsilon` lies in `D_W(Gamma)` via `d = [t c t^-1, a]`, `d^2 = epsilon`.
The permutation matrices `V_n` of a sofic approximation satisfy
`||V_n(gh) - V_n(g)V_n(h)||_2 -> 0` and
`||V_n(epsilon) - 1||_2^2 = 2 (1 - #Fix(sigma_n(epsilon))/d_n) -> 2`.
So a normalized-HS asymptotic representation of `W` keeps the central,
normal, finite, Kazhdan witness `epsilon` at distance `sqrt 2`, although
every group hypothesis of criterion (2) holds.  The statement obtained by
replacing operator-norm multiplicativity by normalized-HS multiplicativity
is therefore false.  Mechanism: `||diag(-1,1,..,1) - I||_2 = 2/sqrt d`
while `||Ad(diag(-1,1,..,1)) - 1|| = 2` on `(M_d, ||.||_2)`, so
conjugation is not controlled by the 2-norm multiplicative defect; that
control is exactly where operator norm enters the manuscript's
Corollary on HS collapse of the defect.  Landed in the manuscript as the
remark following the soficity proof of `W` (commit `4e3024d36`).  This
says nothing about whether `H` is hyperlinear.

## 6. Already in the archive

* The rank-four torsion proposition itself.  Its one-auxiliary-coordinate
  derivation was recorded in
  `research/artifacts/jacobson-unit-group-and-rank-four-recheck-2026-09-08.md`
  Section 4 and shelved because the statement was "already established";
  the establishing route consumed the rank-weighted transport lineage,
  which the manuscript excludes on provenance grounds.  The derivation is
  now the route `torsion-defect-one-auxiliary-coordinate-proof`, the proof
  printed as `prop:torsion-defect-ring`.
* Kirchberg: property (T) plus the factorization property implies
  residual finiteness, so `H` lacks the factorization property
  (`binary-leavitt-unit-group-fails-factorization-property`).  Hence
  hyperlinearity of `H` would not make its canonical trace amenable, and
  `W`'s locally-residually-finite-by-`Z` trace argument is not replaceable
  by a hyperlinearity statement about `H`.

## 7. What is not decided

* Whether `EL_n(J_Z)` is MF for any `n >= 2`.  The same day's second
  note sharpened this to an all-or-nothing statement, `Rad_MF` is `1` or
  `SL_fin(Z)` for `n >= 4` (`integral-jacobson-mf-radical-is-all-or-nothing`,
  `research/artifacts/jacobson-exact-torsion-radical-and-integral-dichotomy-2026-09-09.md`).
  Both known mechanisms are dead there: criterion (2) by Section 3, and the properly infinite corner
  route because no matrix ring over `J_Z` has a properly infinite
  idempotent (the symbol image of such an idempotent in a matrix ring over
  a field is zero, so the idempotent has finite rank on `V^n`, and rank is
  additive).  Note that `EL_n(J_Z)` is (locally residually finite)-by-
  (residually finite), the same shape as the non-MF group `W`.
* The torsion theorem at ranks `2` and `3`, and equality
  `Rad_MF(EL_n(R)) = EL_n(R, ReR)`.
* Hyperlinearity of `H`.

## 8. Manuscript status

`prop:torsion-defect-ring` (commit `a157b60fe`) and the 2-norm remark
(commit `4e3024d36`) are in `non_mf_groups_exist.tex`.  The integral
Jacobson exclusion of Section 3 is deliberately not in the manuscript.

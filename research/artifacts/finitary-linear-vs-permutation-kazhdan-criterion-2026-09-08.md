# Where the normal-Kazhdan criterion works and where it provably cannot

2026-09-08.  Ingestion record for a two-note dossier ("finitary linear sofic
non-MF" and "torsion-defect elementary non-MF").

**Most of this dossier is already in the graph, in stronger form.**  That is
the first thing to record, because two of its four results would otherwise be
landed twice, and one of them would be landed at a worse constant.  What is
genuinely additive is a criterion-level dichotomy, and it is additive
precisely because it explains a choice the graph already made without saying
why.

## What was already here

| dossier | already established here | comparison |
|---|---|---|
| Note 2, Theorem 1: `R` countable unital, `ts=1`, `e=1-st` of finite additive order `=> E_n(R,ReR) <= Rad_MF(EL_n(R))`, `n>=6` | `finite-additive-order-one-sided-defects-are-mf-invisible` | same hypotheses, **`n>=4`** and stated per elementary generator `e_ij(Q)`; the archive's is strictly stronger |
| Note 2, Theorem 2: `EL_n(J)` non-MF with `Rad_MF = GL_fin`, `n>=6` | `binary-jacobson-steinberg-head-root-is-mf-invisible` (+ `binary-jacobson-mf-radical-dichotomy`) | archive proves it at **rank five**, and `binary-jacobson-mark-dichotomy-holds-from-rank-two` pushes the dichotomy lower |
| Note 1, the dyadic sofic non-MF instance with no finite normal subgroup and exact radical | `dyadic-perturbation-group-is-sofic`, `dyadic-perturbation-group-mf-radical-is-finitary-alternating`, and the rest of the `dyadic-*` region | the archive's is `Sym_fin(X) x| H` for the **same** `X` and `H`; radical `Alt_fin(X)`, quotient `C_2 x H` |
| property (T) of `Z^3 x| SL_3(Z)` (dossier cites Cornulier Prop. 1.1) | `affine-semidirect-sl3-source-has-property-t` | archive gets it by finite-index permanence from `affine-congruence-source-is-kazhdan`, which has Lean backing; Cornulier and Ershov--Jaikin-Zapirain are both already recorded there as checks |
| soficity of a finitary extension | `sofic-set-action-finitary-extension-is-sofic`, and Elek--Szabo permanence already cited across the corpus | -- |

So Note 2 is entirely a corroborating independent derivation, and the concrete
example of Note 1 is the linear analogue of an example the graph already
carries in the permutation category.  None of that is landed again below.

The one correction worth making to the dossier's own framing: it presents the
ring criterion as "a ring criterion applying to ordinary elementary groups",
which is right, and as new here, which is not.  It also does not know that the
archive's version reaches rank four, so a reader comparing the two should take
`n>=4`.

## What is additive: a dichotomy between two finitary kernels

The graph contains two separate killing criteria and uses them in two separate
places without recording that the choice is forced:

- `normal-kazhdan-defect-non-mf` (the *Kazhdan* criterion): a nontrivial
  normal property-(T) subgroup inside the compression defect is killed by
  every corona homomorphism.
- `locally-finite-centralizer-derived-subgroup-is-mf-invisible` (the *locally
  finite* criterion): a locally finite centralizer with commuting compressed
  conjugates has its derived subgroup killed, with no normality and no
  Kazhdan subgroup.

The dyadic permutation example uses the second.  The dossier proves that it
had no choice.

### The obstruction (Note 1, Proposition)

Let `V` be MF, `P = Sym_fin(X) x| V`, and `H <= P` any subgroup.  If `L <= H`
has property (T) and `A ⊲ H` has property (T) with `A <= D_H(L)`, then
`A = 1`.

The proof is three steps and uses the Kazhdan criterion twice.  The projection
`H -> V` lands in an MF group, so it kills `A`; hence `A <= Sym_fin(X)`.  An
infinite locally finite group is a directed union of finite subgroups, hence
amenable, and an infinite amenable group has no property (T); so `A` is
finite.  Its finitely many supports have a finite union `S`, which is
`H`-invariant because `A` is normal in `H`, so restriction gives
`H -> Sym(S)` injective on `A`; `Sym(S)` is finite hence MF, so the criterion
kills `A` there too, and an injective map with trivial image forces `A = 1`.

So the Kazhdan criterion is **inert** on finitary permutation extensions of MF
groups, and passing to subgroups does not rescue it.  That is exactly why the
dyadic example needed the locally finite criterion.

### The complement (Note 1, action theorem)

Replace `Sym_fin(X)` by `GL_fin` over `F_2` and the Kazhdan criterion becomes
available again.  Adjoin two `V`-fixed points `a,b` to `X`, put
`W = F_2^(X u {a,b})`, `K = GL_fin(W)`, `G = K x| V`, and suppose there are
`L <= V` with property (T), `u in V`, `x in X`, `ell in L` with

```text
uLu^-1 <= L,      Lx = {x},      ell u x != u x.
```

With `T_(pq) = I + E_(pq)` and

```text
c = T_(xb),   y = T_(a,ux),   z = T_(ab),   H = <L, u, c, y>,
```

`c` centralizes `L` because `L` fixes `x` and `b`; then

```text
d = [u c u^-1, ell] = T_(ux,b) T_(ell u x, b)^-1,     [y, d] = T_(ab) = z,
```

the two row indices being distinct by the third hypothesis.  Setting
`A = E_(a,ux)` and `B = E_(ux,b) + E_(ell u x, b)` gives
`A^2 = B^2 = BA = 0` and `AB = E_(ab)`, so `[I+A, I+B] = I + E_(ab)`
directly.  Since `a` and `b` are `V`-fixed and the other generators miss those
indices, `<z> = C_2` is central in `H`, and it lies in `D_H(L)`.  Finite
groups have property (T), so the Kazhdan criterion applied **to `H`** kills
`z`; restriction of any homomorphism `G -> M` to `H` kills it too; and the
normal closure of `z` contains every transvection, which generates `K`
(Gaussian elimination over `F_2` needs only row additions, a swap being three
of them).

**The mechanism worth naming.**  The finite central subgroup is normal in the
subgroup where the criterion is applied, not in the ambient group.  Every use
of `normal-kazhdan-defect-non-mf` in this archive so far has taken the normal
Kazhdan subgroup normal in the group being killed.  The criterion does not ask
for that: apply it in `H`, then take the normal closure in `G`.  `G` here has
no nontrivial finite normal subgroup at all, so no ambient-normal version of
this argument exists.

The difference between the two cases is exactly characteristic two: the defect
element is a unipotent transvection, which is an involution and generates a
finite central subgroup of `H`.  A finitary permutation cannot play that role,
and the Proposition says nothing can.

## What is not landed, and why

- The ring criterion and the Jacobson instance: duplicates, see the table.  A
  note recording the independent corroboration has been added to
  `finite-additive-order-one-sided-defects-are-mf-invisible` instead.
- The concrete dyadic instance of the linear action theorem: the base `V`,
  its property (T), its residual finiteness, its transitivity and its finite
  generation are all already established for the permutation example, and the
  soficity argument is the same local-residual-finiteness argument with
  `GL(F_2^O) x| N_0` in place of `Sym(O) x| N_0`.  The action theorem below is
  stated with its hypotheses, and the dyadic base is cited as the instance
  that satisfies them rather than re-verified.
- The reduced C*-algebra remarks: the dossier proves `C*_r(G)` is neither
  simple nor uniquely tracial by exhausting `K` with finite subgroups.  It
  says itself that this "gains nothing" over the lamp construction, and the
  archive already carries that conclusion for the locally finite radical
  family.

## Provenance

The dossier worked from the supplied Kazhdan criterion as a black box plus
three published statements (Ershov--Jaikin-Zapirain Theorem 1.1, Cornulier
Proposition 1.1, Elek--Szabo Theorem 1), all three of which the archive
already cites elsewhere.  It states that it did not open the excluded paper or
the archive, and that a Jacobson-ring application had already appeared in its
visible context so it cannot certify uncontaminated candidate selection; it
makes no novelty claim.

Re-derived here before landing: the `[I+A, I+B] = I + E_(ab)` computation and
the vanishing products it rests on, the centralization of `L` by `c`, the
distinctness of the two row indices, the three steps of the Proposition
including the finiteness of `A`, and the transvection generation of `GL_fin`
over `F_2`.  The duplication table was checked node by node against the
current tip.  No Lean was written or built.

# Arithmetic single-defect saturation — ingestion audit, 2026-08-23

An external dossier ("Arithmetic single-defect saturation") proposes a
**Fournier--Facio-free** construction of a 2-generated, finitely presented,
torsion-free, acylindrically hyperbolic, Kazhdan group `Q` with
`Rad_MF(Q) = Q`, quotient-hereditarily.  This file records the argument, the
audit of which parts the repository already carried, and the three statements
that were genuinely missing from the Cairn graph.

## 0. Verdict up front

The dossier is **correct and its headline is real**: the compression source can
be a classical arithmetic group, and no simple subgroup, no universal
torsion-free host, and no Fournier--Facio input is needed anywhere.

It is however **substantially already in this repository**, and in a stronger
form than the dossier states, because sections 1--3 are machine-checked here:

| Dossier section | Repository state on 2026-08-23 |
|---|---|
| §1 `P = Gamma(3) ltimes Z^3`, dilation endomorphism, f.p. + torsion-free | already `concrete-compression-source`, kernel-checked in `LiteralAffineCongruenceSource.lean`; the repo dilates by `2`, the dossier by `3` — immaterial, any `m >= 2` works |
| §1 `P` is Kazhdan | in Lean as `LiteralAffineCongruenceBase.p_hasKazhdanPropertyT`, but **stated in no Cairn claim** — `concrete-compression-source` says in terms that property (T) is *not* involved |
| §2 HNN, Britton-certified `w = [tct^-1, p_0] != 1` | already `concrete-compression-source-proof` (Britton on the length-four commutator word); torsion-freeness of the extension is `hnn-torsion-theorem` |
| §3 free-product AH forcing, `N = <<w>>` suitable | already `LiteralAffineFreeProductSource.amplifiedDefectData` + `amplifiedDefect_isSuitable`; the repo amplifies by `Z`, the dossier by `F_2` — immaterial |
| §4 Theorem 4.1 router | reservoir confinement is `common-quotient-onto-normal-subgroup`; the **two-generation clause and the single-element reservoir were used but never stated** |
| §5 Kazhdan AH partner | **used everywhere, stated nowhere**, and the unqualified form is degenerate (see §D below) |
| §6--7 saturation and the analytic kill | `normal-kazhdan-defect-non-mf`, kernel-checked |
| §8 consequences | already in `defect-saturation-full-mf-radical` and in the addenda of `defect-normally-generates-torsion-free-quotient` |

So the ingestion adds three claims and one route, and does **not** re-author
the source.

## 1. The arithmetic self-compressor

Let `Lambda = Gamma(3) = ker(SL_3(Z) -> SL_3(Z/3))` act on `Z^3` and put

```text
P = Lambda ltimes Z^3.
```

`P` is finitely presented (finite index in `SL_3(Z) ltimes Z^3`), torsion-free
(Minkowski for `Lambda`, then `(g,v)^n = 1` forces `g = 1` then `v = 0`), and
Kazhdan: the pair `(SL_3(Z) ltimes Z^3, Z^3)` has relative property (T),
`SL_3(Z)` has property (T), so the affine group has property (T), and (T)
passes to the finite-index subgroup `P`.

```text
alpha : P -> P,   alpha(g,v) = (g, m v)      (m >= 2)
```

is an injective endomorphism with `alpha(P) = Lambda ltimes m Z^3` of index
`m^3`, so it is proper; fix `p_0 = (1, e_1) notin alpha(P)`.

The dossier takes `m = 3`.  The repository's certified instance takes `m = 2`
(`LiteralAffineCongruenceSource.compression`, `omitted`,
`omitted_not_mem_range`).  Nothing downstream distinguishes the two.

**Why this beats the co-Hopfian obstruction.**  `defect-forces-proper-self-
embedding` shows a nontrivial compression defect forces `alpha(Gamma) != Gamma`,
and observes that higher-rank lattices and torsion-free hyperbolic (T) groups
are all co-Hopfian.  `P` evades this because it is *not* a lattice in a
semisimple group: the dilation acts on the translation factor only, and the
arithmetic linear part is untouched.  That is the whole trick, and it is what
makes the Fournier--Facio universal-group machinery unnecessary.

## 2. One HNN extension gives a nonzero compression defect

Let `B = P x <c>` with `c` of infinite order and

```text
E = <B, t | t p t^-1 = alpha(p) for p in P>.
```

`E` is finitely presented, and torsion-free because every finite-order element
of an HNN extension is conjugate into the base (Lyndon--Schupp IV.2; in-repo as
`hnn-torsion-theorem`, unconditional).  Put

```text
d = t c t^-1,   w = [d, p_0] = t c t^-1 p_0 t c^-1 t^-1 p_0^-1.
```

This word is Britton-reduced: `c^{\pm 1} notin P` kills the `t (-) t^-1`
pinches, and `p_0 notin alpha(P)` kills the `t^-1 (-) t` pinch.  Hence
`w != 1`.  The compression core is `(P hookrightarrow E, t, c)` with
`t P t^-1 = alpha(P) <= P` and `[c, P] = 1`, and `w` is one explicit generator
of its defect normal subgroup

```text
D_E = << [t c t^-1, p] : p in P >>^E.
```

No simple subgroup certifies the defect, and no simplicity-protection argument
is ever used.

## 3. Acylindrical hyperbolicity is imposed, not requested

`R = E * F_2` (repo: `E * Z`).  The Bass--Serre action on the free-product tree
has trivial edge stabilizers, so it is acylindrical and non-elementary; `R` is
finitely presented, torsion-free and AH with trivial finite radical.  `w != 1`
survives the factor embedding, `N = <<w>>^R` is infinite (torsion-freeness makes
`w` of infinite order), normal hence s-normal, hence non-elementary by Osin's
s-normality lemma, hence suitable in Hull's sense.

**The reservoir is the normal closure of one explicit word.**  Nothing asks the
compression subgroup itself to be suitable for an HNN Bass--Serre action.

## 4. The router: one element fills a two-generated common quotient

> **Theorem (two-generator single-defect router).**  Let `A, B` be finitely
> presented torsion-free acylindrically hyperbolic groups, `1 != u in B`,
> `D = <<u>>^B`, and `F_A subset A`, `F_B subset B` finite.  Then there are
> `Q` and surjections `q_A : A ->> Q`, `q_B : B ->> Q` with `Q` acylindrically
> hyperbolic, torsion-free, finitely presented, **two-generated**, with
> `q_A, q_B` injective on `F_A, F_B`, and `q_B(D) = Q`.

Proof, following Hull.  `D` is infinite normal in a torsion-free AH group, so
suitable (Osin s-normality plus the vacuity of Hull's finite-radical clause);
this is exactly the content already established as
`common-quotient-onto-normal-subgroup`, whose clause 2 gives `alpha_2(D) = Q`.

The two additions are bookkeeping inside Hull's two-stage proof of Corollary
7.4.  Take `f_1, f_2 in A` and `h_1, h_2 in D` by Corollary 5.7, promote the
four cyclic subgroups to the hyperbolically embedded family in `F = A * B` by
Lemma 3.5, and run Theorem 7.1 the first time with suitable subgroup
`S_D = <h_1, h_2> <= D`, prescribing a finite generating set of `A`.  This gives
`gamma : F ->> F'` with `gamma(A) <= gamma(S_D) <= gamma(D) <= gamma(B)`, hence
`F' = gamma(B)`.

At the second stage, use the **two-generated** suitable subgroup
`S_A = <gamma(f_1), gamma(f_2)>` rather than the whole image `gamma(A)`; Lemma
4.4 preserves the hyperbolically embedded cyclic pair through the first
quotient, and Lemma 5.8 then makes `S_A` suitable.  Prescribing a finite
generating set of `F'` gives `eta : F' ->> Q` with `Q = eta(S_A)`, so `Q` is
generated by `eta gamma(f_1), eta gamma(f_2)`.  Chaining the inclusions gives
`q_B(D) = Q`.  Torsion lifts by Theorem 7.1(e); finite presentability holds
because each of the two stages adds one relator per prescribed element and the
finitely generated case never invokes the direct limit of Corollary 7.3.

**Trust boundary.**  This is paper-level, not formalized.  It is the same
reading of Hull that the repository already audited adversarially for the
Fournier--Facio instance (`defect-normally-generates-torsion-free-quotient`
Addendum 2026-08-15, GitHub issue #1), where two-generation is likewise
obtained as the image of a two-element suitable subgroup.  The generalization
changes which suitable subgroup Hull's theorem is handed, and touches no
small-cancellation estimate.

## 5. Assembly

Let `H` be a finitely presented, torsion-free, **non-elementary** hyperbolic
group with property (T).  Apply the router with `A = H`, `B = R`, `u = w`,
protecting `w`.  This gives `q : R ->> Q` with `Q` 2-generated, finitely
presented, torsion-free, AH, Kazhdan (a quotient of `H`), and

```text
<<q(w)>>^Q = Q.
```

Write `bar t = q(t)`, `bar c = q(c)`, `iota = q|_P`.  The compression relations
survive: `bar t iota(P) bar t^-1 = iota(alpha(P)) <= iota(P)` and
`[bar c, iota(P)] = 1`.  (`iota` need not be injective; the machine-checked
kill theorem takes the existential compression form and asks nothing of it.)
Since `q(w) = [bar t bar c bar t^-1, iota(p_0)]` lies in the defect `D_Q`,

```text
Q = <<q(w)>>^Q <= D_Q <= Q,   so   D_Q = Q.
```

Now apply the kernel-checked normal-Kazhdan compression theorem
(`normal-kazhdan-defect-non-mf`) with source `P` — Kazhdan by §1 — and normal
Kazhdan subgroup `K = Q`.  Every homomorphism from `Q` to the unitary group of
a norm matrix corona is trivial, so `Rad_MF(Q) = Q`; and full MF residual
passes through surjections, so every nontrivial quotient of `Q` again has full
MF radical.  Consequences already recorded elsewhere in the graph: no
nontrivial homomorphism to any MF group, no nontrivial finite quotient, no
proper finite-index subgroup, no nontrivial finite-dimensional unitary
representation, and `Q` perfect.

## 6. What the dossier does and does not remove

Removed from the dependency set, genuinely:

- Fournier--Facio, *A torsion-free non-sofic group* (arXiv:2608.02025);
- any finitely presented simple torsion-free group (Burger--Mozes, Hyde--Lodha);
- any universal torsion-free host (Higman, Belegradek--Szczepanski, Chiodo);
- every simplicity-protection argument for survival of the marked element.

**Not** removed, and the dossier's §9 comparison table slightly under-states
this: Hull's small-cancellation machinery, Osin's s-normality lemma, and a
finitely presented torsion-free **non-elementary** hyperbolic Kazhdan group are
all still required.  The last of these is the partner `H` of §5; it is exactly
the input the repository's `HyperbolicKazhdanPartner` records as a typed
literature premise, and the dossier inherits it unchanged.

The dossier's own §10 is correct and worth keeping verbatim in spirit: property
(T) has been removed from the *construction and routing* problem but not from
the *detector*.  A (T)-free version needs a new operator-norm rigidity theorem
replacing the normal-Kazhdan detector, not a further rearrangement of the group
theory.  Sections 1--6 would survive such a theorem unchanged.

## D. The degeneracy guard on the partner

The literal sentence "a torsion-free hyperbolic group with property (T)
exists" is satisfied by the **trivial group**: finite implies hyperbolic,
finite implies (T), and torsion-free plus finite implies trivial.  The
repository has been bitten by this before, so the partner claim
`torsion-free-hyperbolic-kazhdan-partner-exists` is stated with *infinite* and
*non-elementary* in the conclusion, and its route says why.  Never discharge
the partner with a finite group.

## Sources

- Michael Hull, *Small cancellation in acylindrically hyperbolic groups*,
  Groups Geom. Dyn. **10** (2016), 1077--1119, DOI 10.4171/GGD/377 —
  Definition 1.4, Lemmas 3.5, 4.4, 5.8, Corollary 5.7, Theorem 7.1, and the
  finitely generated case of Corollary 7.4.
- Denis Osin, *Acylindrically hyperbolic groups*, Trans. Amer. Math. Soc.
  **368** (2016), 851--888, DOI 10.1090/tran/6343 — the s-normal subgroup
  lemma.
- Bekka, de la Harpe, Valette, *Kazhdan's Property (T)*, CUP 2008,
  DOI 10.1017/CBO9780511542749 — relative (T) for the affine pair, (T) for
  `SL_3(Z)`, finite-index and quotient permanence, and (T) for `Sp(n,1)`.
- Serre, *Trees*, and Lyndon--Schupp — Britton normal forms and torsion in HNN
  extensions.
- In-repo: `research/normal-kazhdan-defect-non-mf.md` and the Lean modules
  cited by the nodes of this region.

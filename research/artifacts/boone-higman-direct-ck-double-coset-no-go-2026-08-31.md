# Boone--Higman: the direct CK corner has infinite bi-index, 2026-08-31

## Result

The explicit direct Chatterji--Kassabov envelope introduced by the
universal-sandwich improvement cannot close Cairn's finite-bi-index route to
Boone--Higman.

More generally, let `U` be a unital ring, `n >= 3`, and let `H <= U^x` be a
subgroup for which

```text
D = {diag(h,1,...,1) : h in H} <= EL_n(U).
```

Then

```text
U -> D \ EL_n(U) / D,
a |-> D e_23(a) D                                      (1)
```

is injective.  Consequently the bi-index of `D` is at least `|U|`.

In the direct CK construction

```text
U = Z[Gtilde]<p,q>/(p(1-g)q-1),    Gamma = EL_4(U),     (2)
```

the simple core `S` is contained in `[Gtilde,Gtilde]` and enters the
elementary group through this upper-left corner.  The established injection
`Z[Gtilde] -> U` makes `U` infinite.  Thus

```text
|S \ Gamma / S| >= |U| >= aleph_0.                    (3)
```

By the already established double-coset/orbital dictionary, the action of
`Gamma` on `Gamma/S` has infinitely many pair-orbits and is not of type (A).

This is a construction-specific no-go, not a proof or disproof of the
Boone--Higman conjecture.

## Proof

Put `x_a=e_23(a)`.  The upper-left corner `D` acts only on coordinate `1`,
whereas every `x_a` acts only in the `(2,3)` root position.  Direct matrix
multiplication gives

```text
[D,x_a]=1                                                (4)
```

for every `a in U`.  It also gives

```text
D cap {x_a:a in U}={1}.                                  (5)
```

For if `diag(h,1,...,1)=e_23(a)`, the `(1,1)` entry first forces `h=1`, and
the `(2,3)` entry then forces `a=0`.

If the two double cosets in (1) indexed by `a,b` agree, there are
`d_1,d_2 in D` such that `x_b=d_1 x_a d_2`.  Using (4),

```text
x_(b-a)=x_a^(-1)x_b=d_1d_2 in D.
```

Equation (5) implies `b-a=0`.  This proves (1).

For (3), Chatterji--Kassabov's proof of Theorem 3 says that
`[Gtilde,Gtilde]` embeds into the elementary group by putting `g` in the
upper-left corner.  Cairn's universal-sandwich lemma replaces their
unspecified ring extension by (2) while preserving the injection of
`Z[Gtilde]`.  Therefore the preceding argument applies verbatim to the
embedded simple core.  Nothing about the sandwich generators `p,q` is
needed.

## Dependency audit

The proof uses exactly the following inputs.

1. **Corner placement.**  The CK construction places the input commutator
   subgroup in the upper-left matrix corner.  This is explicit in the proof
   of their Theorem 3, immediately before the displayed commutator producing
   `E_12(1-g)`.
2. **A spare root.**  Rank at least three leaves the root subgroup
   `{e_23(a)}` disjoint from and centralized by that corner.  The direct
   envelope uses rank four.
3. **Infinitude of the coefficient ring.**  The universal-sandwich result
   gives an injective map `Z[Gtilde] -> U`, so `U` is infinite.
4. **The orbital dictionary.**  Pair-orbits of the coset action correspond
   to `S`-double cosets.

It does **not** use simplicity of `S`, property (T), finite presentability of
`U` or `Gamma`, fullness of `1-g`, or any normal-subgroup classification.
The obstruction is therefore stable under changing the sandwich relation or
adjoining further ring generators, as long as the coefficient ring remains
infinite and the core stays in a single matrix corner.

Primary-source boundary checked against Chatterji--Kassabov, *Examples of
finitely presented groups with strong fixed point properties and property
(T)*, arXiv:2601.22907v1, current manuscript date 24 August 2026, proof of
Theorem 3.  The repository dependencies are
`universal-sandwich-ring-is-finitely-presented-and-injective` and
`simple-core-bi-index-counts-coset-action-pair-orbits`.

## Countermodel search

Four possible leaks were checked.

* **Two-sided multiplication could identify parameters.**  It cannot:
  centralization converts any such identification into an element of the
  literal intersection (5).
* **A nontrivial diagonal element could equal a transvection.**  Entrywise
  comparison rules this out over every unital ring, including rings with
  zero divisors.
* **The sandwich relation could collapse the parameter family.**  The proof
  does not use powers of `p`; it indexes the family by all of `U`, and the
  established coefficient-ring injection already makes that set infinite.
* **Changing coordinates could help.**  Conjugating both the core and the
  root family preserves the double-coset injection.  What can help is an
  embedding that genuinely occupies all spare roots, not a coordinate
  relabeling of the corner embedding.

The original CK finitely presented *cover* is not covered by this theorem:
its kernel and chosen lifts can destroy the literal commuting root subgroup.
Likewise, a quotient of `Gamma` can collapse the `x_a`.  Neither is a
countermodel to the statement, which concerns the direct elementary
envelope before taking a quotient.

## Exact remaining gate

The finite-bi-index route now has a sharper gate.  It cannot use the direct
universal-sandwich envelope with the canonical corner embedding.  To survive,
it must produce at least one of:

1. a different finitely presented normal-generator envelope in which the
   simple core has finite bi-index and is not trapped in a proper matrix
   corner;
2. a different faithful type-(A) action of the direct envelope, not the
   coset action on `Gamma/S`; or
3. a quotient/cover with controlled kernel that kills the spare-root
   orbital invariant while preserving the core and finite presentation.

No such construction is supplied here.  The independent maximal-kernel,
BFFHZ action-image, fiber-product, and shift-compiler routes remain open.

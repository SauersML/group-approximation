# The Jacobson unit group is MF, and a ledger against the archive

Date: 2026-09-08. Ingestion of a supplied note offering (i) a rank-four
torsion-defect theorem replacing a rank-six one, (ii) a unit-group
theorem from a properly infinite corner, and (iii) the computation of
`J^x` for `J = F_2<s,t | ts = 1>`.

**Only (iii) is new to this archive.** The ledger is in Section 1 and it
is the point of this file: two of the three headline results were already
established here, one of them in a strictly stronger form. Section 2
records the one new theorem, Section 3 its consequences, Section 4 the
third derivation of the rank-four statement.

## 1. Ledger

**(i) The rank-four theorem is already here, at rank four.** The supplied
note's Theorem A -- `R` countable unital, `ts = 1`, `e = 1 - st != 0` of
finite additive order, no fullness, and `E_n(R,ReR) <= Rad_MF(EL_n(R))`
for `n >= 4`, with the corollary that `char(R) > 0` and `EL_4(R)` MF
force direct finiteness -- is verbatim the established claim
`finite-additive-order-one-sided-defects-are-mf-invisible`, including
that corollary.

The note presents this as an improvement from six coordinates to four.
The six-coordinate statement it is improving on is **its own earlier
derivation**, which this archive already ingested and already annotated:
that node records the rank-six derivation and says "the rank there is 6
and the rank here is 4, so nothing is gained by adopting it and a reader
comparing the two should take `n >= 4`." So the new note closes its own
gap and arrives where the archive already stood. Its compressor is
genuinely different and is worth recording (Section 4), but the
statement is not new and its rank is not an improvement on anything here.

**(ii) The unit-group theorem is already here, and stronger.** The note's
Theorem B has two halves, and the archive has both:

* "full torsion defect implies `R^x` not MF" is
  `properly-infinite-unit-group-is-not-mf`, which assumes only `ts = 1`
  and `R(1-st)R = R` -- **no torsion, no positive characteristic** -- and
  concludes that `R^x` and every `GL_n(R)` fail to be MF.
* "a nonzero properly infinite corner in positive characteristic forces
  the unit group to be non-MF" is the weaker form of
  `properly-infinite-corner-forces-non-mf-from-rank-two`, which needs
  **no characteristic hypothesis and reaches rank two**, where the note
  goes through rank four in positive characteristic.
* the note's "a full defect produces two split copies" is exactly
  `full-idempotent-ring-has-properly-infinite-unit`, the equivalence of
  `R(1-st)R = R` with proper infiniteness of `1`.
* the note's `GL_4(S) ~= S^x` for the Leavitt algebra, and the resulting
  non-MF unit group, is `binary-leavitt-all-ranks-full-mf-radical`
  together with `corner-unitization-embeds-elementary-groups`.

So on (ii) the archive dominates the note on both hypotheses at once.

**(iii) The `J^x` computation is new.** Nothing here computes the unit
group of the binary Jacobson algebra. It is recorded below as
`jacobson-unit-group-is-locally-finite-and-mf`.

## 2. The unit group of the binary Jacobson algebra

**Theorem.** Let `J = F_2<s,t | ts = 1>` and `e = 1 - st != 0`. Then

```text
J^x = union_N GL_N(F_2)
```

along the identity-block inclusions, so `J^x` is countable, locally
finite and **MF**, while `J` is not directly finite.

**Proof, rechecked in full.** Let `V = F_2^(N_0)` with basis
`v_0, v_1, ...`, and `s v_i = v_(i+1)`, `t v_0 = 0`, `t v_i = v_(i-1)`
for `i > 0`. Then `ts = 1` and `st` kills `v_0` and fixes every other
basis vector, so `e = 1 - st` is the projection onto `v_0`, nonzero.

*Faithfulness.* Cancelling `ts` reduces every word to `s^i t^j`, and
`s^i t^j` sends `v_k` to `v_(k-j+i)` for `k >= j` and to zero otherwise.
Group a finite combination by the offset `d = i - j`; distinct offsets
land in distinct rows, so they cannot cancel each other, and within one
offset the coefficient at column `k` is
`sum_(j <= k, j >= max(0,-d)) c_(j+d,j)`. Vanishing for every `k` gives,
by successive differences, every `c_(ij) = 0`. So the reduced monomials
are linearly independent as operators.

*The finitary ideal and the symbol.* `f_(ij) = s^i e t^j` is the matrix
unit sending `v_j` to `v_i`, and multiplying `e` by reduced monomials on
either side gives either zero or such a matrix unit, so `I = JeJ` is
exactly the algebra of finitely supported matrices. Killing `e` makes
`s,t` mutually inverse, and the universal property gives
`J/I ~= F_2[z, z^-1]`. In particular `I != J`, so the defect is **not**
full -- which is why the archive's fullness theorems do not apply here.

*Units.* For `g` in `J^x`, its symbol is a unit of `F_2[z,z^-1]`, hence
`z^k`: in a product the lowest and the highest exponents add, so a
product equal to one forces each factor to be a single monomial, with
coefficient `1` over `F_2`. Since `I` is finitely supported, there is
`N` with `N + k >= 0` and `g v_i = v_(i+k)` for all `i >= N`. Writing
`V_N` for the span of `{v_i : i >= N}`, this gives `g V_N = V_(N+k)`, and
`g` is bijective, so it induces `V/V_N ~= V/V_(N+k)`. Those have
dimensions `N` and `N + k`, so **`k = 0`**.

So every unit differs from `1` by a finitely supported matrix and is an
invertible finite block extended by the identity; conversely every such
element is a unit. That is the displayed union.

*MF.* A countable increasing union `F = union F_N` of finite groups is
MF directly: at stage `N` use the left regular representation of `F_N`
and send everything outside `F_N` to the identity. Each fixed
multiplication relation holds exactly for all large `N`, and for `g != 1`
the eventual regular action moves the identity basis vector to an
orthogonal one, so the operator distance to `I` is at least `sqrt 2`.
This gives an injective homomorphism into the operator-norm matrix
corona. No amenable-approximation theorem is imported.

Finally `ts = 1 != st` because `e != 0`, so `J` is not directly finite.
QED

Every step above was re-derived rather than read. The step that carries
the theorem is the index count `dim V/V_N = N` against
`dim V/V_(N+k) = N+k`: it is what rules out a unit with nonzero symbol,
and it is exactly the place where a naive expectation ("the shift `s`
should be a unit") fails.

## 3. What it settles, and what it does not

**The rank-one statement is false.** "`R^x` MF implies `R` directly
finite" fails, with a counterexample inside this archive's own running
example. So the fullness hypothesis of
`properly-infinite-unit-group-is-not-mf` and the properly-infinite-corner
hypothesis of `properly-infinite-corner-forces-non-mf-from-rank-two`
cannot be dropped, and no argument can hope to derive non-MF of a unit
group from failure of direct finiteness alone.

**It reproves the `d = 1` case of an established claim, independently.**
If `J` had a nonzero properly infinite idempotent `p`, then
`properly-infinite-corner-forces-non-mf-from-rank-two` would make
`EL_2(pJp)` non-MF, and `corner-unitization-embeds-elementary-groups`
followed by `v |-> 1 - p + v` would embed a non-MF group into `J^x`,
contradicting the theorem. So `J` has no nonzero properly infinite
idempotent -- which is the `d = 1` case of
`binary-jacobson-matrix-rings-have-no-infinite-corner`, reached from the
unit group rather than from the symbol-and-finitary-corner argument
recorded there. The general `d` is not recovered this way, since MF-ness
of `J^x` says nothing directly about `GL_d(J)`.

**It sharpens the picture with the rank-four theorem.** For `J` the
defect `e` has additive order two, so
`finite-additive-order-one-sided-defects-are-mf-invisible` makes
`E_n(J)` non-MF for `n >= 4`, while `J^x` is MF. Hence **there is no
embedding of `GL_4(J)` into `J^x`**, equivalently the unit of `J` is not
properly infinite -- consistent with, and a second route to, the
previous paragraph. Sizes two and three stay open, as they already were.

**It does not touch** the unrestricted locally finite defect question, or
soficity or hyperlinearity of anything.

## 4. The third derivation of the rank-four statement

Recorded because the compressor differs from both derivations already on
file, not because the statement is new. The note's internal matrix units

```text
f_(ij) = s^i e t^j,     f_(ij) f_(kl) = delta_(jk) f_(il),
```

let **one** auxiliary coordinate hold all the finite witnesses, leaving
three coordinates for the Kazhdan subgroup, which is what buys rank four
directly rather than rank six. The compressor is
`u = U P` with `U` the four-by-four matrix having `s` on the first three
diagonal entries, `t^3` in the corner, and `e, et, et^2` in the last
column, inverted using `e + set + s^2 e t^2 = 1 - s^3 t^3`; `P` is
`diag(1,1,1,r)` with `r = w_(1,4) w_(2,5)` and
`w_(ij) = (1+f_(ji))(1-f_(ij))(1+f_(ji))`. The finite central witness is
`z = I + s e t^2 E_44`, and the extraction is

```text
[z, x_41(s^2 e)] = x_41(se),    [x_24(t), x_41(se)] = x_21(e).
```

These two identities and the centrality of `z` were checked here by hand
in the normal form `s^i t^j`. The analytic input is unchanged:
`normal-kazhdan-defect-non-mf` applied inside the subgroup generated by
the configuration, with property (T) from Ershov--Jaikin-Zapirain
Theorem 1.1 for the elementary group over a finitely generated subring.
Since the target statement is already established at `n >= 4`, no route
is wired from this; it is a remark on the existing node.

## 5. Provenance

The mathematics is a user-supplied note of 2026-09-08. This file adds the
ledger of Section 1, the recheck of Section 2, the consequences in
Section 3, and the restriction of Section 4 to a remark.

**This is the fourth consecutive supplied note whose headline result was
already in the archive.** In this one, two of three were, and one of
those two was here in a strictly stronger form -- weaker hypotheses and a
lower rank. The recurring failure is not in the mathematics of the notes,
which checks out; it is that a note's own sense of what it improves is
calibrated against its own previous draft, not against this archive. Grep
the archive for the theorem statement before accepting a stated
improvement, and specifically compare hypotheses and ranks rather than
conclusions.

Ershov--Jaikin-Zapirain Theorem 1.1 is used only through the already
established rank-four node and is not independently verified here.
Cairn validates the dependency graph; it does not kernel-check the
theorem of Section 2, and no `GroupApproximation/` declaration
corresponds to it.

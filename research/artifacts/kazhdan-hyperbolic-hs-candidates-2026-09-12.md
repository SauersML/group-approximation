# Kazhdan hyperbolic HS stability: candidate screen and Kazhdan-kernel quotients

Lane `nh-kazhdan-hyperbolic-hs`, 2026-09-12. This lane looks for a non-hyperlinear
group, independent of L^×, through
`kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` (reviewer PASS). Its premise
is that one hyperbolic Kazhdan group with `b_2 >= 1` is flexibly Hilbert--Schmidt
stable: `kazhdan-hyperbolic-b2-group-flexibly-hs-stable`, which is open.

## 1. New theorems landed

- **`flexible-hs-stability-passes-to-kazhdan-kernel-quotients`.** If `Γ` is finitely
  generated and flexibly HS stable, and `N ◁ Γ` has property (T), then `Γ/N` is
  flexibly HS stable. This is a direct proof, the unitary analogue of Alekseev--Thom
  arXiv:2512.15494 Theorem A(ii), which concerns stability in finite actions.
- **`flexibly-hs-stable-kazhdan-kernel-quotient-rf-or-nonhyperlinear`.** `Γ/N` is then
  residually finite or not hyperlinear. If it is infinite and minimally almost
  periodic, it is not hyperlinear.
- **`classwide-hyperbolic-kazhdan-hs-stability-covers-fp-kazhdan`.** Suppose every
  hyperbolic Kazhdan group is flexibly HS stable. Then every finitely presented
  Kazhdan group is stable. So every infinite finitely presented minimally almost
  periodic Kazhdan group is not hyperlinear, including the binary Leavitt unit group
  and the Caprace--Rémy lattices.

**Proof idea of the first theorem.**
1. Compose an asymptotic representation of `Q` with the quotient map, and stabilize
   in `Γ`. The stable corner is almost invariant, and the kernel acts almost trivially
   on it.
2. A Kazhdan pair `(S_N, κ)` gives `||(1-E)P||_HS^2 <= κ^(-2) Σ_s ||(ρ(s)-1)P||_HS^2`,
   where `E` projects onto the `N`-fixed vectors. So the corner lies almost inside
   `E`, where `ρ` factors through `Q`.
3. Polar decomposition moves the corner into `E`. The `o(d)`-dimensional kernel of
   `EP` goes into a trivial summand.

**Novelty check (bounded).** I checked:
- the Cairn graph: no HS quotient-permanence node;
- arXiv:2512.09180 (Fournier-Facio), which is about (T_2) and does not treat HS
  quotients;
- the Becker--Lubotzky abstract, arXiv:1809.00632;
- the Dogon--Vigdorovich abstract, arXiv:2506.20843.

No printed unitary version turned up. This is not an exhaustive search.

## 2. Candidate screen

| candidate | hyperbolic | (T) | `b_2 >= 1` | RF / hyperlinear | stability input | verdict |
| --- | --- | --- | --- | --- | --- | --- |
| Gromov density model, `d ∈ (1/3,1/2)` | yes, w.o.p. | yes | yes, w.o.p. (`|R| - m`) | unknown | none | no certified presentation; not closed under Belegradek--Osin covers, so the class-wide screen does not reach it directly |
| cocompact `Sp(2,1)` lattices | yes | yes (Kostant) | not verified from a source | linear, so RF and hyperlinear | none | stability would force a persistent prime `H^2` class (not good) |
| `GHB(7)` (CCKW Kac--Moody--Steinberg, `p = 7`) | not re-checked here | yes (CCKW Thm 1.3; `EJZAngleGHB.lean`) | only on a torsion-free finite-index subgroup | unknown | none | torsion from finite vertex groups `U_3(7)`, `U_4(7)`; needs virtual torsion-freeness first |
| `Ã_2` Ballmann--Świątkowski groups | no (Euclidean buildings, `Z^2` flats) | yes for large `q` | n/a | n/a | n/a | excluded |
| Belegradek--Osin covers of f.p. Kazhdan `Q` | yes | yes | not checked | as `Q` | cover stable ⟹ `Q` stable | never easier than `Q` itself |

**Why no candidate has a stability input.**
- Becker--Lubotzky exclude strict HS stability for infinite hyperlinear Kazhdan
  groups.
- Fournier-Facio--Gerasimova--Spaas exclude local HS stability for them.
- For hyperlinear Kazhdan groups, weak ucp stability equals flexible stability
  (`kazhdan-weak-ucp-stability-is-flexible-stability`).
- No source read in this lane exhibits a flexibly HS-stable infinite property (T)
  group. Dogon--Vigdorovich's explicit target is `SL_2(Z[1/p])`, which has (T;FD)
  but not (T).

## 3. What the screen shows

- **Hyperlinear candidates.** A stable hyperlinear candidate is residually finite and
  not good (`hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class`).
  That is Gromov's question in cohomological form.
- **Class-wide arguments.** Any argument that works for a class closed under
  Belegradek--Osin covers proves non-hyperlinearity of the Leavitt unit group and the
  Kac--Moody lattices outright. So a proof for a candidate has to use a property that
  those covers lack, specific to the candidate.
- **Named covers.** The hyperbolic Kazhdan cover of L^× being stable would make L^×
  non-hyperlinear. But that is strictly harder than `leavitt-unit-hs-stable-iff-nonhyperlinear`'s
  premise, so it is not recorded as a route.

## 4. Not done

- `b_2` of cocompact `Sp(2,1)` lattices, from the Vogan--Zuckerman / Borel--Wallach
  classification. The Kim--Pansu local rigidity note read in this lane does not state it.
- Hyperbolicity, virtual torsion-freeness and `b_2` of `GHB(7)`.
- A stability input specific to a candidate class, as required by the screen above.

# Kaplansky finiteness in positive characteristic on main's nonsofic witnesses (2026-09-13)

This is lane solve-direct-finiteness-charp. Every positive entry below is ESTABLISHED in the graph and has not been independently reviewed.

## What forces stable finiteness (fields unless stated)

- **Characteristic 0, all groups.** Kaplansky's theorem, quoted in Ceccherini-Silberstein--Coornaert--Phung, GGD 19 (2025), Section 1, from the PDF. It is not imported as a node.
- **Linear sofic groups, hence sofic groups.** `linear-sofic-group-algebra-is-stably-finite`: Arzhantseva--Paunescu, which recovers Elek--Szabo.
- **Surjunctive groups.** Phung's theorem, as Theorem 1.1 of the GGD paper above. It is not imported.
- **Free-by-amenable groups, over division rings of every characteristic.** Ara--O'Meara--Perera, Adv. Math. 170 (2002). Checked from the abstract via web search only.
- **{f.g. residually finite}-by-sofic groups, over noetherian rings.** Berlai, arXiv:1501.02893, from the abstract.
- **(residually finite p)-by-(stably finite), over fields of characteristic p.** `residually-p-kernels-preserve-modular-stable-finiteness`.
- **New here: the same over division rings of characteristic p.** This adds free and free abelian kernels of any rank, sofic quotients over division rings, and the fold isomorphisms for doubles and centralizing HNN extensions: `free-kernel-extensions-keep-modular-stable-finiteness`.
- **Permutational wreaths with residually finite lamps and base.** `rf-lamp-permutational-wreaths-satisfy-stable-finiteness`.

## Census

| Nonsofic group on main | Kaplansky finiteness in characteristic p | Source |
|---|---|---|
| Kun--Thom wreath `Z/2 wr_(G/Gamma) G`, Theorem E | stably finite, all fields | `kun-thom-wreath-stably-finite` |
| Kun--Thom double `G *_Gamma G`, Theorem E | stably finite, all division rings of char p | new, `nonsofic-witness-finiteness-over-modular-division-rings` (1) |
| free wreath `(*_X Z) x| H`, amenable action | stably finite, all division rings of char p | new, same node (2) |
| Clifford cover `E_S`, char 3 | iff the skew ring `A_S` is directly finite: OPEN | `clifford-cover-group-algebra-splits-into-wreath-and-skew-ring` |
| torsion-free `D_3 = G_OW *_(Gamma_hat) G_OW` | iff the same for `G_OW`: OPEN | new, same node (3) |
| torsion-free `W_hat` | iff the same for `G_hat`: OPEN | new, same node (4) |
| Fournier--Facio torsion-free Kazhdan group | OPEN, no reduction on record | `fournier-facio-group-is-nonsofic` |
| `R^x = L_(F_2)(1,2)^x`, equivalently the 18-relator group | OPEN in both directions; direct iff stable | `leavitt-unit-group-algebra-is-directly-finite`, `leavitt-stable-finiteness-equals-direct-finiteness` |
| fp simple nonsofic hosts containing `R^x` | OPEN; a positive answer would give `R^x` | subgroup heredity |

## Why the mechanisms stop

- The extension step needs a normal residually-p subgroup whose quotient is already known to be stably finite.
  - None is recorded for `R^x`, for `G_OW`, for `G_hat` or for the Fournier--Facio group.
  - All four are Kazhdan; `R^x` is perfect (`leavitt-gl-equals-el-and-perfect-unit-group`).
- For `E_S` in characteristic 3 the lamp kernel is a 2-group. Its augmentation ideal in characteristic 3 is idempotent, not separated. The anti-central factor `A_S` is a Clifford crossed product with no algebra maps to finite site pieces (see its node).
- **Division-ring routes to stable finiteness.**
  - Malcev--Neumann needs a bi-order.
  - Hughes-free fields need local indicability.
  - A (T) group has finite abelianization, so it is not locally indicable.
  - Left-orderability of these Kazhdan covers is the open `infinite-left-orderable-kazhdan-group`.

## What a counterexample must look like (reverse direction)

If `BA = I != AB` over `F_p[W]`, then:
- the supports generate a nonsofic subgroup (known filter);
- by the extension step, the failure survives in `F_p[W/N]` for every normal residually-p `N`, so it descends to such quotients;
- the defect `E = I - AB` is an idempotent of Hattori--Stallings rank `0`, with `tau(E) = 0` in `F_p`.

## Exact gap

Kaplansky direct finiteness in characteristic p remains undecided on main for:
1. `R^x` and every Leavitt-containing or simple Kazhdan host;
2. the torsion-free Kazhdan covers `G_OW` and `G_hat`, and the Fournier--Facio group;
3. the Clifford skew ring `A_S` in characteristic 3.

Each needs a mechanism beyond residual-p kernels, soficity, surjunctivity and division rings of fractions.

## Sources

- https://www.sciencedirect.com/science/article/pii/S000187080292075X (AOP; abstract only)
- https://arxiv.org/abs/1501.02893 (Berlai; abstract)
- https://ems.press/content/serial-article-files/51166 (Ceccherini-Silberstein--Coornaert--Phung; PDF pp. 495--497 read)

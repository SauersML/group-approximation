# BH swarm, lane bh-permanence: closure properties of the Boone–Higman class (2026-09-18)

`𝓑` = groups embedding in some finitely presented simple group. All results below are
elementary lane proofs, not independently reviewed; no priority claimed.

## What was already on main (read first)
- Direct products: OPEN; ⟺ (JE) ∧ (SQ) (Attempt 10 of `boone-higman-closed-under-finite-direct-products`).
- Decidable-edge HNN: OPEN (`bh-embeddability-survives-decidable-edge-hnn`); the decidability
  hypothesis is necessary (`bh-embeddability-forces-decidable-edge-membership`).
- HNN permanence + the OPEN tower claim `decidable-groups-embed-in-decidable-edge-towers` ⇒ BH
  (`boone-higman-via-decidable-edge-towers`).
- Finite extensions and products: known only for the permutational class `B_A`
  (`boone-higman-type-a-class-closed-under-finite-extensions`).

## New nodes
| node | content |
|---|---|
| `fp-simple-groups-have-the-joint-embedding-property` | OPEN statement (JE); common core of three closure questions |
| `bh-class-free-products-iff-joint-embedding-and-free-z` | (FP) ⟺ (JE) ∧ (FZ), with (FZ): `U * Z ∈ 𝓑` for fp simple `U` |
| `bh-class-decidable-amalgams-from-free-products-and-hnn` | (FP) + decidable-edge HNN ⇒ decidable amalgams and finite graphs of groups |
| `bh-class-finite-extensions-reduce-to-finite-simple-wreaths` | (FW) ⟺ (FE) ∧ (SQ); products + finite extensions ⟺ (JE) ∧ (FW) |

(FW): `S ≀ Q ∈ 𝓑` for every fp simple `S` and finite simple `Q` (regular wreath).

## The picture
Every closure property of `𝓑` studied here is (JE) plus one "self-closure" of fp simple groups:
- direct products: (JE) + (SQ) `U x U`;
- free products: (JE) + (FZ) `U * Z`;
- products and finite extensions: (JE) + (FW) `U ≀ Q`;
- decidable amalgams and graphs of groups: (JE) + (FZ) + decidable-edge HNN.

All of (JE), (SQ), (FZ), (FW) hold for fp simple groups in `B_A` (BFFHZ Corollary F; closure of
`B_A` under products and commensurability). So each closure property can fail only through a
finitely presented simple group without the permutational property, i.e. only if BFFHZ
Question 3.4 fails (`bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`).

## Not done
- No unconditional closure theorem for `𝓑`. The single-explicit-group reduction of BH is excluded
  on main by complexity (`complexity-bounded-host-classes-are-not-universal`,
  `no-decidable-group-contains-every-polynomial-dehn-fp-group`), so it was not attempted.
- Wreath products `A ≀ Z` for the full class: not attempted beyond noting they need a host with
  commuting shifted copies (compare `bh-type-a-class-closed-under-permutational-lamp-wreaths`).
- A test of (JE) on a hard pair (a Kazhdan Kac–Moody lattice and `V`) is suggested, not tried.

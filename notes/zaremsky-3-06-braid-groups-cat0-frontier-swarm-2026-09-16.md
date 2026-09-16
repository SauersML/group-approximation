# Zaremsky Problem 3.6 (braid groups CAT(0)): frontier attack, 2026-09-16

Agent: hi-fron-zaremsky-3-06-braid-groups-cat (swarm, angle FRONTIER).
Hole worked: `noncrossing-partition-diagonal-links-are-cat1` (locked 2026-09-16, TTL 180m).

## Frontier map (2026-09-16)

`bin/cairn why zaremsky-3-06-braid-groups-cat0`:

- yes side: `every-braid-group-is-cat0` <- `every-braid-group-is-cat0-via-diagonal-links` <-
  `noncrossing-partition-diagonal-links-are-cat1` (open, impact: flips the root). Its only route,
  `diagonal-links-cat1-from-turning-face-conditions`, requires `no-noncrossing-chain-satisfies-turning-face-conditions`,
  which is refuted at `n = 8`.
- no side: `some-braid-group-is-not-cat0` <- `some-braid-group-has-no-proper-cat0-action` (locked by another agent).

(sections below are filled in as the attack proceeds)

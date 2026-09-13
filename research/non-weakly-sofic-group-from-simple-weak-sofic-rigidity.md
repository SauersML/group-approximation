---
rg: 2
id: non-weakly-sofic-group-from-simple-weak-sofic-rigidity
kind: route
title: Put the Kun--Thom wreath inside a finitely generated simple Kazhdan group and apply simple weak-sofic rigidity
target: non-weakly-sofic-group-exists
requires: [fg-simple-weakly-sofic-groups-are-sofic, countable-group-embeds-in-fg-simple-kazhdan-group, weakly-sofic-not-sofic]
---

1. **The seed.** `weakly-sofic-not-sofic` supplies the Kun--Thom wreath `W`, which is countable,
   weakly sofic and not sofic.
2. **The envelope.** By `countable-group-embeds-in-fg-simple-kazhdan-group`, `W` embeds in a
   finitely generated infinite simple group `S` with property (T).
3. **`S` is not sofic.** Soficity passes to subgroups, and `W <= S` is not sofic.
4. **`S` is not weakly sofic.** If it were, `fg-simple-weakly-sofic-groups-are-sofic` would make `S`
   sofic, contradicting step 3.

So `S` witnesses `non-weakly-sofic-group-exists`.

Only the Kazhdan case of the prerequisite is used. The same argument with Schupp's
two-generator envelope (`countable-group-embeds-in-two-generator-simple-group`) needs the
prerequisite for two-generator simple groups instead. This route does not fire until the
prerequisite is established, and it is open.

---
rg: 2
id: sofic-non-lef-simple-kazhdan-from-universal-sofic-host
kind: route
title: A universal sofic simple Kazhdan host theorem gives a sofic non-LEF infinite simple Kazhdan group
target: sofic-non-lef-infinite-simple-kazhdan-group-exists
requires:
  - sofic-groups-embed-in-simple-kazhdan-sofic-groups
  - sofic-universal-envelope-forces-non-lef-simple-kazhdan
---

Assembly only. The second required claim is the implication from the first to the target:
- apply the host theorem to a finitely generated sofic group that is not LEF (the witness recorded there
  is `BS(2,3)`);
- the host contains it, and LEF passes to subgroups;
- so the host is an infinite simple Kazhdan sofic group that is not LEF.

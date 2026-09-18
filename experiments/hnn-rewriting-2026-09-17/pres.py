#!/usr/bin/env python3
"""Emit kb input: python3 pres.py <name> <order> <ordering> <max_rules> <max_len>"""
import sys
inv = lambda w: ''.join(c.swapcase() for c in reversed(w))
comm = lambda u, v: u + v + inv(u) + inv(v)
b = 'taT'  # b = t a t^-1; t^-1 x t = sigma(x) with sigma: b -> a, a -> b^2, so T^2 a t^2 = a^2
P = {
 'bs12': ['taTAA'],
 'thompsonF': [comm('xY', 'Xyx'), comm('xY', 'XXyxx')],
 # Basilica HNN: sigma(a)=b^2, sigma(b)=a (checked in basilica_sigma_check.py); relator [a, a^b]
 'basilicaHNN': ['TTattAA', comm('a', inv(b) + 'a' + b)],
 # Grigorchuk 1998: a^2=b^2=c^2=d^2=bcd=1, T x t = sigma(x), sigma: a->aca, b->d, c->b, d->c; (ad)^4, (adacac)^4
 'grigorchukHNN': ['aa', 'bb', 'cc', 'dd', 'bcd', 'Tat' + inv('aca'), 'TbtD', 'TctB', 'TdtC', 'ad' * 4, 'adacac' * 4],
}
name, order, ordering, mr, ml = sys.argv[1:6]
print(order); print(ordering); print(mr, ml)
for r in P[name]:
    print(r)

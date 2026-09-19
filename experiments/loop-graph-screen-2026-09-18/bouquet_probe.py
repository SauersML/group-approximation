"""Probe of the linear bouquet class: orders of the two loop letters l_s, l_t at the bouquet
vertex z and whether they commute (data toward the ray-loop subgroup H_{z^inf})."""
from same_point_screen import *
tally = {}
for name, R in family(True):
    ok, loops = check_L1(R)
    comps = classify_components(R, loops)
    if max([rk for _, rk, _, _ in comps] + [0]) < 2: continue
    ls = {s: A + ((s, 1),) + B for s, (x, A, B) in loops.items()}
    def o(w):
        c = infinite_order(R, w)
        return "inf" if c else (exact_order(R, w) or "?")
    try: comm = R.trivial(inv(ls["s"]) + inv(ls["t"]) + ls["s"] + ls["t"])
    except RuntimeError: comm = "?"
    key = (o(ls["s"]), o(ls["t"]), comm)
    tally.setdefault(key, []).append(name)
for k, v in sorted(tally.items(), key=lambda kv: -len(kv[1])):
    print(len(v), "ord(l_s), ord(l_t), commute =", k, "e.g.", v[0])

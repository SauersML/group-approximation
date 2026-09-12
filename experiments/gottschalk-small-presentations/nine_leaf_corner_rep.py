"""Separate x_h in the nine-leaf window eld-full-order2 (radius 1:1) by a linear image of
its table group in GL(6,2), and write a witness that window_table_screen.py --verify replays.

Only relators with h = E01(1) carry Steinberg content at radius 1:1. The others are
involutions, commutations of E_ij(a), E_kl(b) at non-adjacent positions, and the zero
products t_k s_m = 0 (k != m). The compressors cu, cv occur only with h, so they can be sent to 1.
Send E_ij(r) to the block matrix 1 + e_ij (x) rho_ij(r) in GL_3(M_2(F_2)), with rho chosen
per position. The Steinberg relations with h need
    P rho_12(r) = rho_02(r),  rho_20(r) P = rho_21(r),  rho_02(a) rho_21(b) = P  for ab = 1,
with P = rho_01(1) = e_00. A finite ring cannot satisfy t_k s_m = delta_km 1. Here the
products land in the rank-one corner P instead, so rho_02(t_k) = e_0k and rho_21(s_k) = e_k0.

MSI usage (GAP through sage, as in window_table_screen.py):
  python nine_leaf_corner_rep.py --out runs/wit/eld-full-order2-1-1.witness.json
  python window_table_screen.py --verify runs/res-c.json --gap-dir runs/wit
"""
import argparse, json, os, re, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import window_table_screen as W

L = W.L
NPTS = 63  # nonzero row vectors of F_2^6
RHO = {(0, 1): {"1": [(0, 0)]},
       (0, 2): {"1": [(0, 0)], "t0": [(0, 0)], "t1": [(0, 1)]},
       (2, 1): {"1": [(0, 0)], "s0": [(0, 0)], "s1": [(1, 0)]}}
RHO[(1, 2)] = RHO[(0, 2)]
RHO[(2, 0)] = RHO[(2, 1)]


def base_perm(name):
    rows = [1 << k for k in range(6)]
    m = re.match(r"E(\d)(\d)_(\w+)$", name)
    if m:
        i, j, r = int(m.group(1)), int(m.group(2)), m.group(3)
        for a, b in RHO.get((i, j), {}).get(r, []):
            rows[2 * i + a] ^= 1 << (2 * j + b)
    def act(v):
        out = 0
        for k in range(6):
            if (v >> k) & 1:
                out ^= rows[k]
        return out
    return [act(p) for p in range(1, NPTS + 1)]


def invert(perm):
    inv = [0] * len(perm)
    for i, x in enumerate(perm):
        inv[x - 1] = i + 1
    return inv


def table_words(units, gen_names, h, S, M):
    base = [units[n] for n in gen_names]
    hi = gen_names.index(W.FAMILIES["eld-full-order2"][1])
    letters = {L.IDENTITY.key: []}
    for i, g in enumerate(base):
        letters.setdefault(g.key, [(i, 1)])
        letters.setdefault(g.inverse().key, [(i, -1)])
    words = {k: letters.get(k) for k in set(S) | set(M)}
    for x_key, x in W.ball(base, 1).items():
        y = h * x
        if y.key in words and words[y.key] is None:
            words[y.key] = [(hi, 1)] + letters[x_key]
    missing = [k for k, w in words.items() if w is None]
    if missing:
        sys.exit("window elements without a word: %d" % len(missing))
    return words


def gap_check(n, rels, perms, h_idx, gap_cmd):
    def w(ix):
        return "*".join("F.%d" % (i + 1) for i in ix) if ix else "One(F)"
    fd, path = tempfile.mkstemp(suffix=".g", dir=".")
    with os.fdopen(fd, "w") as fh:
        fh.write("F := FreeGroup(%d);;\nrels := [%s];;\n" % (
            n, ",\n".join("%s/(%s)" % (w(l), w(r)) for l, r in rels)))
        fh.write("imgs := [%s];;\n" % ",\n".join("PermList(%s)" % p for p in perms))
        fh.write("ok := ForAll(rels, rr -> MappedWord(rr, GeneratorsOfGroup(F), imgs) = ());;\n"
                 "Print(\"GAP_RELATORS_OK \", ok, \" H_NONTRIVIAL \", imgs[%d] <> (),\n"
                 "  \" IMAGE_ORDER \", Size(Group(imgs)), \"\\n\");\nQUIT;\n" % (h_idx + 1))
    out = subprocess.run(gap_cmd.split() + [path], stdout=subprocess.PIPE,
                         universal_newlines=True).stdout
    os.remove(path)
    print(out.strip())
    return "GAP_RELATORS_OK true H_NONTRIVIAL true" in out, out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--gap-cmd", default="sage -gap -q")
    args = ap.parse_args()
    units = W.named_units()
    gen_names, h_name = W.FAMILIES["eld-full-order2"]
    h, order, powers, S, M = W.window(units, gen_names, h_name, 1, 1)
    index, rels, h_idx = W.relators(h, powers, S, M)
    print("|S|=%d |M|=%d generators=%d relators=%d" % (len(S), len(M), len(index), len(rels)))
    words = table_words(units, gen_names, h, S, M)
    base = [base_perm(n) for n in gen_names]
    base_inv = [invert(p) for p in base]
    ident = L.IDENTITY.key
    perms = [None] * len(index)
    for key, i in index.items():
        img = list(range(1, NPTS + 1))
        for c, e in words[key]:
            p = base[c] if e == 1 else base_inv[c]
            img = [p[x - 1] for x in img]
        perms[i] = img
    bad = [(l, r) for l, r in rels
           if W.perm_word(perms, l, NPTS) != W.perm_word(perms, r, NPTS)]
    ok = W.check_perm_witness(rels, perms, h_idx, NPTS)
    print("python replay:", "OK" if ok else "FAIL", "failing relators:", len(bad))
    if not ok:
        sys.exit(1)
    gap_ok, _ = gap_check(len(index), rels, perms, h_idx, args.gap_cmd)
    json.dump({"index": NPTS, "gap_relators_ok": gap_ok, "image": "GL(6,2) corner representation",
               "perms": perms}, open(args.out, "w"))
    print("wrote", args.out, "gap_relators_ok", gap_ok)
    sys.exit(0 if gap_ok else 1)


if __name__ == "__main__":
    main()

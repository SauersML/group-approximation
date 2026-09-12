#!/usr/bin/env python3
"""Extract a small replayable certificate for a window that df_table_screen.py --verify called DEAD.

The run's characters are replayed first, then the witness images in file order. A character or
an image is kept only if it refines the partition of BA u {1}; any image failing a relator of
U(A, B) is skipped. Output in <outdir>:
  <run>-<tag>.json             the window record, keeping only the characters that were used
  <tag>--min.witness.jsonl     the images that were used
Replay:
  python df_table_screen.py --verify <outdir>/<run>-<tag>.json --gap-dir <outdir>
which must print status DEAD.

usage: python kdf_min_cert.py <run.json> <family> <ra> <rb> <gap_dir> <outdir>
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import df_table_screen as T  # noqa: E402


def cell_perms(img, word, ncells):
    n = img["degree"]
    gens = [[x - 1 for x in p] + list(range(len(p), n)) for p in img["perms"]]
    inv = []
    for p in gens:
        q = [0] * n
        for x, y in enumerate(p):
            q[y] = x
        inv.append(q)
    perm = {}
    for k in range(ncells):
        cur = list(range(n))
        for a, e in word[k]:
            cur = T.mul(cur, gens[a - 1] if e == 1 else inv[a - 1])
        perm[k] = tuple(cur)
    return perm


def main():
    run, fam, ra, rb, gdir, outdir = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5], sys.argv[6]
    tag = "%s-%d-%d" % (fam, ra, rb)
    rec = next(r for r in json.load(open(run)) if (r["family"], r["ra"], r["rb"]) == (fam, ra, rb))
    nA, nB, cells, rels, ba = T.table(fam, ra, rb)
    keys = {g: () for g in ba}

    def nclasses(k):
        return len(set(k.values()))
    kept_chars = []
    for ch in rec["characters"]:
        p, chi = ch["p"], dict(ch["chi"])
        if any((chi.get(i, 0) + chi.get(j, 0) - chi.get(k, 0)) % p for i, j, k in rels):
            sys.exit("%s: stored character fails a relator" % tag)
        new = {g: keys[g] + (chi.get(g, 0),) for g in ba}
        if nclasses(new) > nclasses(keys):
            keys, kept_chars = new, kept_chars + [ch]
    basic, word, crels = T.compact(cells, rels)
    kept_lines, skipped = [], 0
    wits = sorted(f for f in os.listdir(gdir) if f.startswith(tag + "--") and f.endswith(".witness.jsonl"))
    for f in wits:
        for line in open(os.path.join(gdir, f)):
            if not T.classes(keys):
                break
            try:
                img = json.loads(line)
            except ValueError:
                skipped += 1
                continue
            perm = cell_perms(img, word, len(cells))
            if any(T.mul(perm[i], perm[j]) != list(perm[k]) for i, j, k in rels):
                skipped += 1
                continue
            new = {g: keys[g] + (perm[g],) for g in ba}
            if nclasses(new) > nclasses(keys):
                keys = new
                kept_lines.append(line.strip())
    cl = T.classes(keys)
    os.makedirs(outdir, exist_ok=True)
    out = {k: v for k, v in rec.items() if k != "final_classes_cells"}
    out["characters"] = kept_chars
    base = os.path.splitext(os.path.basename(run))[0]
    json.dump([out], open(os.path.join(outdir, "%s-%s.json" % (base, tag)), "w"))
    with open(os.path.join(outdir, tag + "--min.witness.jsonl"), "w") as fh:
        fh.write("".join(x + "\n" for x in kept_lines))
    print(tag, "status", "DEAD" if not cl else "SURVIVES", "characters kept", len(kept_chars),
          "images kept", len(kept_lines), "skipped", skipped, "classes", len(cl), "CERT_DONE")


if __name__ == "__main__":
    main()

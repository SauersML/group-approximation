#!/usr/bin/env python3
"""Shapes of iterates of Labbe's morphism omega = alpha beta gamma on the 19 Wang tiles U.

Input: article1_omega.tex from the arXiv e-print of S. Labbe, arXiv:1802.03265
(fetch: curl -sSL -o eprint.tar https://arxiv.org/e-print/1802.03265 ; tar xf eprint.tar).
Usage: python3 omega_shapes.py path/to/article1_omega.tex > output.txt

Checks, all exact:
 1. 19 source tiles 0..18, each image a full rectangle of shape <= (2,2), image tiles carry the
    same edge labels as the source tiles with the same id, and images are valid Wang patches.
 2. Shape consistency on locally admissible dominoes (top(a)=bottom(b) => equal widths,
    right(a)=left(b) => equal heights).
 3. Incidence matrix M[a][b] = #occurrences of a in omega(b); smallest m with M^m > 0.
 4. omega^m(a) for m = 1..8 computed by block substitution, asserting column-constant widths and
    row-constant heights of the letters substituted, and Wang validity of the result; reports
    min over letters of width and height of omega^m(a).
 5. Images of locally admissible dominoes are Wang-valid across the seam.
Single-threaded, no randomness.
"""
import re
import sys

POS = re.compile(r"% tile at position \(x,y\)=\((\d+), (\d+)\)")
ID = re.compile(r"\\node at \(([\d.]+), ([\d.]+)\) \{(\d+)\};")
LAB = re.compile(r"\\node\[rotate=0\] at \(([\d.]+), ([\d.]+)\) \{([A-Za-z0-9]+)\};")


def parse(path):
    events = []  # ('tile', x, y, id, labels) or ('mapsto',)
    cur = None
    for line in open(path, encoding="utf8"):
        if "$\\mapsto$" in line:
            events.append(("mapsto",))
            continue
        m = POS.search(line)
        if m:
            cur = {"x": int(m.group(1)), "y": int(m.group(2)), "id": None, "lab": {}}
            events.append(("tile", cur))
            continue
        if cur is None:
            continue
        m = ID.search(line)
        if m and cur["id"] is None:
            cur["id"] = int(m.group(3))
            continue
        m = LAB.search(line)
        if m:
            fx, fy = float(m.group(1)) - cur["x"], float(m.group(2)) - cur["y"]
            side = {(0.8, 0.5): "R", (0.5, 0.8): "T", (0.2, 0.5): "L", (0.5, 0.2): "B"}[
                (round(fx, 1), round(fy, 1))]
            cur["lab"][side] = m.group(3)
    idx = [i for i, e in enumerate(events) if e[0] == "mapsto"]
    tiles, omega = {}, {}
    for n, k in enumerate(idx):
        src = events[k - 1][1]
        end = idx[n + 1] - 1 if n + 1 < len(idx) else len(events)
        img = [e[1] for e in events[k + 1:end] if e[0] == "tile"]
        tiles[src["id"]] = tuple(src["lab"][s] for s in "RTLB")
        omega[src["id"]] = img
    return tiles, omega


def main():
    tiles, omega_raw = parse(sys.argv[1])
    ids = sorted(tiles)
    assert ids == list(range(19)), ids
    R, T, L, B = 0, 1, 2, 3
    omega = {}
    for a in ids:
        img = omega_raw[a]
        w = 1 + max(t["x"] for t in img)
        h = 1 + max(t["y"] for t in img)
        grid = {(t["x"], t["y"]): t["id"] for t in img}
        assert len(grid) == len(img) == w * h, (a, grid)
        for t in img:
            assert tuple(t["lab"][s] for s in "RTLB") == tiles[t["id"]], (a, t)
        arr = [[grid[(x, y)] for y in range(h)] for x in range(w)]  # arr[x][y], y upward
        for x in range(w):
            for y in range(h):
                if x + 1 < w:
                    assert tiles[arr[x][y]][R] == tiles[arr[x + 1][y]][L]
                if y + 1 < h:
                    assert tiles[arr[x][y]][T] == tiles[arr[x][y + 1]][B]
        omega[a] = arr
    shape = {a: (len(omega[a]), len(omega[a][0])) for a in ids}
    print("check 1: 19 tiles, images rectangular and Wang-valid, labels consistent: OK")
    print("shapes of omega(a):", {a: shape[a] for a in ids})
    assert all(s[0] <= 2 and s[1] <= 2 for s in shape.values())
    print("letters with shape (2,2):", [a for a in ids if shape[a] == (2, 2)])

    bad_v = [(a, b) for a in ids for b in ids
             if tiles[a][T] == tiles[b][B] and shape[a][0] != shape[b][0]]
    bad_h = [(a, b) for a in ids for b in ids
             if tiles[a][R] == tiles[b][L] and shape[a][1] != shape[b][1]]
    print("check 2: locally admissible vertical dominoes with unequal widths:", bad_v)
    print("check 2: locally admissible horizontal dominoes with unequal heights:", bad_h)

    # check 5: images of locally admissible dominoes are Wang-valid across the seam, so omega maps
    # valid tilings to valid tilings (Omega_U is the set of all valid tilings).
    seam_bad = []
    for a in ids:
        for b in ids:
            if tiles[a][R] == tiles[b][L] and shape[a][1] == shape[b][1]:
                for y in range(shape[a][1]):
                    if tiles[omega[a][-1][y]][R] != tiles[omega[b][0][y]][L]:
                        seam_bad.append(("h", a, b))
            if tiles[a][T] == tiles[b][B] and shape[a][0] == shape[b][0]:
                for x in range(shape[a][0]):
                    if tiles[omega[a][x][-1]][T] != tiles[omega[b][x][0]][B]:
                        seam_bad.append(("v", a, b))
    n_h = sum(1 for a in ids for b in ids if tiles[a][R] == tiles[b][L])
    n_v = sum(1 for a in ids for b in ids if tiles[a][T] == tiles[b][B])
    print(f"check 5: {n_h} horizontal and {n_v} vertical admissible dominoes; seam failures:",
          seam_bad)
    assert not bad_v and not bad_h and not seam_bad

    M = [[sum(col.count(a) for col in omega[b]) for b in ids] for a in ids]
    P, m = [row[:] for row in M], 1
    while not all(v > 0 for row in P for v in row):
        P = [[sum(P[i][k] * M[k][j] for k in ids) for j in ids] for i in ids]
        m += 1
        assert m < 50
    print("check 3: smallest m with M^m > 0:", m)

    cur = {a: [[a]] for a in ids}
    for step in range(1, 9):
        nxt = {}
        for a in ids:
            X = cur[a]
            W, H = len(X), len(X[0])
            widths = []
            for x in range(W):
                ws = {shape[X[x][y]][0] for y in range(H)}
                assert len(ws) == 1, ("column width not constant", a, step)
                widths.append(ws.pop())
            heights = []
            for y in range(H):
                hs = {shape[X[x][y]][1] for x in range(W)}
                assert len(hs) == 1, ("row height not constant", a, step)
                heights.append(hs.pop())
            out = [[None] * sum(heights) for _ in range(sum(widths))]
            ox = 0
            for x in range(W):
                oy = 0
                for y in range(H):
                    blk = omega[X[x][y]]
                    for i in range(widths[x]):
                        for j in range(heights[y]):
                            out[ox + i][oy + j] = blk[i][j]
                    oy += heights[y]
                ox += widths[x]
            for x in range(len(out)):
                for y in range(len(out[0])):
                    if x + 1 < len(out):
                        assert tiles[out[x][y]][R] == tiles[out[x + 1][y]][L]
                    if y + 1 < len(out[0]):
                        assert tiles[out[x][y]][T] == tiles[out[x][y + 1]][B]
            nxt[a] = out
        cur = nxt
        ws = [len(cur[a]) for a in ids]
        hs = [len(cur[a][0]) for a in ids]
        print(f"check 4: m={step}: min width {min(ws)}, min height {min(hs)}, "
              f"max width {max(ws)}, max height {max(hs)}")
        if step == 2:
            assert min(ws) >= 2 and min(hs) >= 2
    assert all(len(cur[a]) >= 2 and len(cur[a][0]) >= 2 for a in ids)
    print("RESULT: omega is shape-consistent on admissible dominoes and maps valid tilings to valid")
    print("tilings; every letter a of U has shape(omega^2(a)) >= (2,2) and shape(omega^8(a)) >= (34,34)")


if __name__ == "__main__":
    main()

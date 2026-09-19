#!/usr/bin/env python3
"""census_linemap.py   (census lane, 2026-09-13)

The lanes' LINE:<n> row keys and worklist.py's owner rules number the lines of the tex as it stood before 45483f699
(the tex at a8cc132c8, unchanged since 09-11; census_merge.sh exports it as cc-in/tex-rows.tex).  45483f699 moved
the tex (+10 lines at 249, +2 at 1107, +255 at 1336), so those numbers are carried to the current tex by a line diff,
and a manuscript edit moves no row and no owner.  A line the edit replaced keeps its offset from the last line kept
before it, capped before the next kept line; a line only the current tex has maps back to None.
"""
import difflib


class LineMap:
    def __init__(self, old_lines, new_lines):
        self.fwd, self.back = {}, {}
        sm = difflib.SequenceMatcher(None, old_lines, new_lines, autojunk=False)
        for a, b, size in sm.get_matching_blocks():
            for i in range(size):
                self.fwd[a + i + 1] = b + i + 1
                self.back[b + i + 1] = a + i + 1
        self.kept = sorted(self.fwd)
        self.moved = any(o != n for o, n in self.fwd.items()) or len(old_lines) != len(new_lines)

    def to_new(self, n: int) -> int:
        """The current tex line of line n of the rows' tex."""
        if n in self.fwd:
            return self.fwd[n]
        prev = max((o for o in self.kept if o < n), default=0)
        nxt = min((o for o in self.kept if o > n), default=None)
        at = self.fwd.get(prev, 0) + (n - prev)
        if nxt is not None:
            at = min(at, self.fwd[nxt] - 1)
        return max(at, 1)

    def to_old(self, n: int):
        """The rows' tex line of current line n, or None for a line only the current tex has."""
        return self.back.get(n)


def load(old_path: str, new_path: str) -> LineMap:
    with open(old_path, encoding="utf-8") as fh:
        old = fh.read().split("\n")
    with open(new_path, encoding="utf-8") as fh:
        new = fh.read().split("\n")
    if len(old) < 100:
        raise SystemExit("linemap: the rows' tex %s has %d lines; refusing to translate LINE keys" % (old_path, len(old)))
    return LineMap(old, new)

"""Undo GAP's line continuations: a backslash immediately before a newline joins the two lines.
Usage: joinlines.py IN OUT
"""
import sys

s = open(sys.argv[1]).read().replace("\\\n", "")
open(sys.argv[2], "w").write(s)

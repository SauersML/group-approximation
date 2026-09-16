#!/usr/bin/env python3
"""Extract the segments and atom labels of Labbe's partition P_U from the vector figure.

Input: article3_partitionU.pdf from the arXiv e-print of arXiv:1903.06137
(fetched 2026-09-16 from export.arxiv.org/e-print/1903.06137), and
article3_tile_set_U.tex from the same e-print.
Output (stdout): a plain-text data file (partitionU_data.txt) listing
  SEG x0 y0 x1 y1      frame coordinates, frame = [0, 85.04042]^2 = [0,1]^2
  LABEL n x y          text-box origin of the label u_n
  TILE n right top left bottom
Usage: extract_figure.py <article3_partitionU.pdf> <article3_tile_set_U.tex>
"""
import re
import sys
import zlib


def content_stream(pdf_path):
    s = open(pdf_path, 'rb').read()
    m = re.search(rb'stream\r?\n', s)
    st = m.end()
    en = s.find(b'endstream', st)
    return zlib.decompress(s[st:en]).decode('latin1')


def main():
    pdf, tex = sys.argv[1], sys.argv[2]
    c = content_stream(pdf)
    out = []
    for m in re.finditer(r'([\d.]+) ([\d.]+) m \n([\d.]+) ([\d.]+) l \nS', c):
        out.append('SEG ' + ' '.join(m.groups()))
    for m in re.finditer(
            r'1 0 0 1 ([\d.\-]+) ([\d.\-]+) cm\n1\.0 0\.0 0\.0 1\.0 0\.0 0\.0 cm \n.*?\[\((\d+)\)\]TJ',
            c, re.S):
        if float(m.group(2)) < 0:  # axis tick labels below the frame
            continue
        out.append('LABEL %s %s %s' % (m.group(3), m.group(1), m.group(2)))
    t = open(tex).read()
    for blk in re.split(r'% tile at position', t)[1:]:
        n = re.search(r'\\node\[\] at \([^)]*\) \{(\d+)\};', blk).group(1)
        cols = re.findall(r'\\node\[rotate=0,black\] at \(([\d.\-]+), ([\d.\-]+)\) \{(\w)\};', blk)
        # order in the source: right, top, left, bottom
        out.append('TILE %s %s' % (n, ' '.join(col[2] for col in cols)))
    print('\n'.join(out))


if __name__ == '__main__':
    main()

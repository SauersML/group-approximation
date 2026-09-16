import re, zlib, sys
data = open('refB/zop.pdf','rb').read()
out = []
for m in re.finditer(rb'stream\r?\n', data):
    start = m.end()
    end = data.find(b'endstream', start)
    if end < 0: continue
    chunk = data[start:end]
    try:
        dec = zlib.decompress(chunk)
    except Exception:
        try:
            dec = zlib.decompressobj().decompress(chunk)
        except Exception:
            continue
    out.append(dec)
blob = b'\n'.join(out)
# collect literal strings inside TJ/Tj operators
texts = re.findall(rb'\((?:[^()\\]|\\.)*\)', blob)
s = b''.join(t[1:-1] for t in texts).decode('latin-1')
for kw in ['raided', 'cyclic']:
    for mm in re.finditer(kw, s):
        print(repr(s[max(0,mm.start()-200):mm.end()+80]))
        print('---')
print(len(blob), len(s))

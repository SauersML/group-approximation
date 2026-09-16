# Minimal PDF text extractor (zlib + ToUnicode CMaps), for reading arXiv PDFs without poppler.
import re, zlib, sys
path = sys.argv[1]
data = open(path,'rb').read()
objs = {}
# uncompressed objects
for m in re.finditer(rb'(\d+)\s+0\s+obj(.*?)endobj', data, re.S):
    objs[int(m.group(1))] = m.group(2)
def stream_of(body):
    m = re.search(rb'stream\r?\n', body)
    if not m: return None
    raw = body[m.end():]
    try:
        return zlib.decompressobj().decompress(raw)
    except Exception:
        return raw
# object streams
for num, body in list(objs.items()):
    if b'/ObjStm' in body:
        s = stream_of(body)
        n = int(re.search(rb'/N\s+(\d+)', body).group(1))
        first = int(re.search(rb'/First\s+(\d+)', body).group(1))
        hdr = s[:first].split()
        for k in range(n):
            onum = int(hdr[2*k]); off = int(hdr[2*k+1])
            nxt = int(hdr[2*k+3]) if k+1 < n else len(s)-first
            objs[onum] = s[first+off:first+nxt]
def deref(x):
    m = re.match(rb'\s*(\d+)\s+0\s+R', x)
    return objs.get(int(m.group(1))) if m else x
def parse_cmap(s):
    mp = {}
    for blk in re.findall(rb'beginbfchar(.*?)endbfchar', s, re.S):
        for a,b in re.findall(rb'<([0-9A-Fa-f]+)>\s*<([0-9A-Fa-f]+)>', blk):
            mp[int(a,16)] = bytes.fromhex(b.decode()).decode('utf-16-be', 'replace')
    for blk in re.findall(rb'beginbfrange(.*?)endbfrange', s, re.S):
        for a,b,c in re.findall(rb'<([0-9A-Fa-f]+)>\s*<([0-9A-Fa-f]+)>\s*<([0-9A-Fa-f]+)>', blk):
            lo,hi,base = int(a,16),int(b,16),int(c,16)
            for k in range(lo,hi+1):
                mp[k] = chr(base + (k-lo))
    return mp
cmaps = {}
def font_cmap(fobj):
    m = re.search(rb'/ToUnicode\s+(\d+)\s+0\s+R', fobj)
    if not m: return None, 1
    nb = 2 if b'/Type0' in fobj else 1
    s = stream_of(objs[int(m.group(1))])
    return parse_cmap(s), nb
out = []
pages = [ (n,b) for n,b in objs.items() if re.search(rb'/Type\s*/Page[^s]', b)]
pages.sort()
for pn, pb in pages:
    res = re.search(rb'/Resources\s+(\d+\s+0\s+R|<<.*)', pb, re.S)
    resb = deref(res.group(1))
    fm = re.search(rb'/Font\s*(\d+\s+0\s+R|<<(.*?)>>)', resb, re.S)
    fdict = deref(fm.group(1)) if fm.group(2) is None else fm.group(2)
    fonts = {}
    for name, ref in re.findall(rb'/(F\d+)\s+(\d+)\s+0\s+R', fdict):
        fonts[name] = font_cmap(objs[int(ref)])
    cm = re.search(rb'/Contents\s*\[?\s*(\d+)\s+0\s+R', pb)
    content = stream_of(objs[int(cm.group(1))])
    cur = (None,1)
    line = []
    for tok in re.finditer(rb'/(F\d+)\s+[\d.]+\s+Tf|\[(.*?)\]\s*TJ|<([0-9A-Fa-f]*)>\s*Tj|\(((?:\\.|[^\\)])*)\)\s*Tj|(-?[\d.]+\s+-?[\d.]+\s+T[dD]|T\*)|(ET)', content, re.S):
        if tok.group(1):
            cur = fonts.get(tok.group(1), (None,1))
        elif tok.group(2) is not None or tok.group(3) is not None or tok.group(4) is not None:
            arr = tok.group(2) if tok.group(2) is not None else (b'<'+tok.group(3)+b'>' if tok.group(3) is not None else b'('+tok.group(4)+b')')
            for hx, lit, num in re.findall(rb'<([0-9A-Fa-f]*)>|\(((?:\\.|[^\\)])*)\)|(-?\d+\.?\d*)', arr):
                mp, nb = cur
                if hx:
                    codes = [int(hx[i:i+2*nb],16) for i in range(0,len(hx),2*nb)]
                elif lit:
                    lit2 = re.sub(rb'\\([0-7]{1,3})', lambda m: bytes([int(m.group(1),8)]), lit)
                    lit2 = re.sub(rb'\\(.)', lambda m: m.group(1), lit2)
                    codes = list(lit2)
                elif num:
                    if float(num) < -250: line.append(' ')
                    continue
                else:
                    continue
                for c in codes:
                    line.append(mp.get(c, '?') if mp else chr(c))
        elif tok.group(5):
            t = tok.group(5).split()
            if len(t) == 3 and abs(float(t[1])) > 1:
                line.append('\n')
            else:
                line.append(' ')
        elif tok.group(6):
            line.append(' ')
    out.append('\n\n===== PAGE obj %d =====\n' % pn + ''.join(line))
open(sys.argv[2],'w').write(''.join(out))
print('pages', len(pages))

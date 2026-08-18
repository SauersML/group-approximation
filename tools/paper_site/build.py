#!/usr/bin/env python3
"""Assemble the self-contained web edition of non_mf_groups_exist.tex.

The page embeds the raw TeX and the claims manifest verbatim; a client-side
renderer (parser.js + ui.js) typesets them with an inlined KaTeX, so the
manuscript stays the single source of truth and the site follows every tex
push with no separate content pipeline.  Stdlib only; no toolchain.

    python3 tools/paper_site/build.py --out .cairn/site/paper/index.html
"""
import argparse
import base64
import json
import os
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent


def read(p):
    return Path(p).read_text(encoding='utf-8')


DECL_HEAD = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+)?'
    r'(theorem|lemma|def|abbrev|instance|structure|inductive)\s+(\S+)', re.M)

# A line that starts a new top-level item ends the previous declaration.
NEXT_TOP = re.compile(
    r'^(?:@\[|/--|/-!|--|(?:noncomputable\s+|private\s+|protected\s+|partial\s+|unsafe\s+|scoped\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|example|open|end|namespace|'
    r'section|variable|universe|set_option|attribute|omit|include|mutual|deriving|alias|export|'
    r'notation|macro|syntax|elab|initialize|run_cmd|#)\b)', re.M)


def split_signature(code):
    """Index of the top-level `:=` (or a line starting with `| `, for
    structures given by anonymous-constructor syntax); -1 if none."""
    depth = 0
    i, n = 0, len(code)
    while i < n:
        c = code[i]
        if code.startswith('--', i):                 # line comment
            j = code.find('\n', i)
            i = n if j < 0 else j
            continue
        if code.startswith('/-', i):                 # block comment
            j = code.find('-/', i + 2)
            i = n if j < 0 else j + 2
            continue
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        elif depth == 0 and code.startswith(':=', i):
            return i
        i += 1
    return -1


def cap(text, max_lines, max_chars):
    lines = text.splitlines()
    trunc = len(lines) > max_lines or len(text) > max_chars
    if len(lines) > max_lines:
        text = '\n'.join(lines[:max_lines])
    return text[:max_chars], trunc


def extract_decl(module, decl):
    """Best-effort: the full declaration `decl` (statement and proof) from
    <module>.lean, as {'sig','proof','line','trunc'}."""
    path = REPO / 'GroupApproximation' / (module + '.lean')
    if not path.exists():
        path = REPO / (module + '.lean')
    if not path.exists():
        return None
    src = path.read_text(encoding='utf-8')
    name = decl.split('.')[-1]
    for m in DECL_HEAD.finditer(src):
        if m.group(2) != name:
            continue
        line = src.count('\n', 0, m.start(1)) + 1
        stop = NEXT_TOP.search(src, m.end())
        code = src[m.start(1):stop.start() if stop else len(src)].rstrip()
        at = split_signature(code)
        if at < 0:
            sig, proof = code, ''
        else:
            sig, proof = code[:at].rstrip(), code[at:].rstrip()
        sig, t1 = cap(sig, 60, 6000)
        proof, t2 = cap(proof, 400, 24000)
        return {'sig': sig, 'proof': proof, 'line': line, 'trunc': t1 or t2}
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default=str(HERE / 'index.html'))
    ap.add_argument('--build-id', default=os.environ.get('GITHUB_SHA', 'dev'))
    args = ap.parse_args()

    katex_css = read(HERE / 'katex' / 'katex.min.css')
    katex_js = read(HERE / 'katex' / 'katex.min.js')
    site_css = read(HERE / 'styles.css')
    polish_css = read(HERE / 'polish.css')
    parser_js = read(HERE / 'parser.js')
    ui_js = read(HERE / 'ui.js')
    enhance_js = read(HERE / 'enhance.js')
    freshness_js = read(HERE / 'freshness.js').replace(
        '/*__BUILD_ID_JSON__*/', json.dumps(args.build_id))
    template = read(HERE / 'template.html')
    tex = read(REPO / 'non_mf_groups_exist.tex')
    claims = read(REPO / 'docs' / 'NON_MF_NUMBERED_CLAIMS.json')

    # inline the woff2 fonts into the KaTeX css; drop the woff/ttf fallbacks
    def font_uri(m):
        data = (HERE / 'katex' / 'fonts' / f'{m.group(1)}.woff2').read_bytes()
        return 'url(data:font/woff2;base64,%s) format("woff2")' % base64.b64encode(data).decode('ascii')

    katex_css = re.sub(r'url\(fonts/([A-Za-z0-9_-]+)\.woff2\) format\("woff2"\)', font_uri, katex_css)
    katex_css = re.sub(r',url\(fonts/[A-Za-z0-9_-]+\.(?:woff|ttf)\) format\("(?:woff|truetype)"\)', '', katex_css)
    leftovers = re.findall(r'url\(fonts/[^)]*\)', katex_css)
    if leftovers:
        sys.exit(f'unresolved font urls remain: {leftovers[:4]}')

    wanted = []
    for c in json.loads(claims)['claims']:
        for l in c.get('lean', []):
            wanted.append((l['module'], l['declaration']))
    # declarations cited only by in-tex \leanverified markers
    for m in re.finditer(r'\\leanverified\{([^}]*)\}\{([^}]*)\}', tex):
        wanted.append((m.group(1).strip(), m.group(2).strip()))
    lean_src = {}
    for module, declaration in wanted:
        key = module + '|' + declaration
        if key not in lean_src:
            code = extract_decl(module, declaration)
            if code:
                lean_src[key] = code
    data_js = (
        'window.PAPER_TEX = ' + json.dumps(tex).replace('</', '<\\/') + ';\n'
        'window.CLAIMS = ' + json.dumps(json.loads(claims)).replace('</', '<\\/') + ';\n'
        'window.LEAN_SRC = ' + json.dumps(lean_src).replace('</', '<\\/') + ';\n'
    )

    for name, payload in [
        ('FRESHNESS_JS', freshness_js), ('KATEX_JS', katex_js),
        ('PARSER_JS', parser_js), ('UI_JS', ui_js), ('ENHANCE_JS', enhance_js),
        ('DATA_JS', data_js),
    ]:
        if '</script' in payload.replace('<\\/script', ''):
            sys.exit(f'{name} contains a literal </script sequence')

    out = template
    for name, payload in [
        ('FRESHNESS_JS', freshness_js), ('KATEX_CSS', katex_css),
        ('SITE_CSS', site_css), ('POLISH_CSS', polish_css),
        ('KATEX_JS', katex_js), ('DATA_JS', data_js),
        ('PARSER_JS', parser_js), ('UI_JS', ui_js), ('ENHANCE_JS', enhance_js),
    ]:
        marker = f'/*__{name}__*/'
        assert marker in out, marker
        out = out.replace(marker, payload)

    dest = Path(args.out)
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(out, encoding='utf-8')

    if re.fullmatch(r'[0-9a-fA-F]{7,64}', args.build_id):
        version = args.build_id.lower()
        (dest.parent / 'version.json').write_text(
            json.dumps({'version': version}, separators=(',', ':')) + '\n', encoding='utf-8')
        versioned = dest.parent / 'v' / version / 'index.html'
        versioned.parent.mkdir(parents=True, exist_ok=True)
        versioned.write_text(out, encoding='utf-8')

    print(f'wrote {dest} ({len(out)/1e6:.2f} MB)')


if __name__ == '__main__':
    main()

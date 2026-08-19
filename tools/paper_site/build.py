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
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:(?:noncomputable|private|protected|nonrec|partial|unsafe|scoped)\s+)*'
    r'(theorem|lemma|def|abbrev|instance|structure|inductive)\s+(\S+)', re.M)

# A line that starts a new top-level item ends the previous declaration.
NEXT_TOP = re.compile(
    r'^(?:@\[|/--|/-!|--|(?:noncomputable\s+|private\s+|protected\s+|partial\s+|unsafe\s+|scoped\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|example|open|end|namespace|'
    r'section|variable|universe|set_option|attribute|omit|include|mutual|deriving|alias|export|'
    r'notation|macro|syntax|elab|initialize|run_cmd|#)\b)', re.M)


def comment_spans(src):
    """(start, end) of every Lean comment in `src`: nesting block comments
    (`/- -/`, and so `/-- -/` and `/-! -/` too) and line comments.

    A module docstring is prose, and prose contains sentences that begin with
    the word `theorem`.  Scanning for declarations without this mask picks
    those up as declarations named after whatever word follows -- one such
    phantom carried a path from this repository onto the page."""
    spans = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c == '"':                                   # string literal
            i += 1
            while i < n and src[i] != '"':
                i += 2 if src[i] == '\\' else 1
            i += 1
            continue
        if src.startswith('/-', i):
            start, depth, i = i, 0, i
            while i < n:
                if src.startswith('/-', i):
                    depth += 1
                    i += 2
                elif src.startswith('-/', i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    i += 1
            spans.append((start, i))
            continue
        if src.startswith('--', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            spans.append((i, j))
            i = j
            continue
        i += 1
    return spans


def in_any(spans, pos):
    return any(a <= pos < b for a, b in spans)


def name_matches(source_name, wanted):
    """How well a name written at a declaration head matches a fully
    qualified name, in dot-segments; 0 for no match.

    `theorem NormModel.exists_hs_collapse` inside `namespace GroupApproximation`
    is cited as `GroupApproximation.NormModel.exists_hs_collapse`, so neither
    the whole name nor its last segment is what stands in the source.  What
    always holds is that the source name is a suffix of the cited one."""
    a = source_name.split('.')
    b = wanted.split('.')
    return len(a) if len(a) <= len(b) and b[-len(a):] == a else 0


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
    spans = comment_spans(src)
    # the head that names the most segments of `decl` wins, so a `Foo.bar` in
    # the file is preferred over a bare `bar` when both could answer
    best = None
    for m in DECL_HEAD.finditer(src):
        if in_any(spans, m.start()):
            continue
        score = name_matches(m.group(2), decl)
        if score and (best is None or score > best[0]):
            best = (score, m)
    if best is None:
        return None
    m = best[1]
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


def strip_tex_comments(tex):
    """Drop TeX comments, exactly as parser.js's stripComments does.

    The page carries the manuscript source so the renderer can typeset it,
    and a comment is a note between authors, not part of the manuscript --
    these ones name files in this repository.  The renderer strips comments
    anyway, so doing it here changes nothing it reads and keeps the words
    out of what is served."""
    out, carry = [], None
    for raw in tex.split('\n'):
        line = raw if carry is None else carry + raw.lstrip()
        carry = None
        cut = -1
        k = 0
        while k < len(line):
            if line[k] == '\\':
                k += 2
                continue
            if line[k] == '%':
                cut = k
                break
            k += 1
        if cut < 0:
            out.append(line)
            continue
        before = line[:cut]
        if before.strip() == '':
            continue                     # whole-line comment: no paragraph break
        carry = before                   # a comment eats the newline after it
    if carry is not None:
        out.append(carry)
    return '\n'.join(out)


def parse_steps():
    """Step rows of metadata/NON_MF_PROOF_LEDGER.md, grouped by anchor.

    Hand-authored, pin-enforced in CI; each row grades one printed step's
    statement and proof route against the Lean development."""
    path = REPO / 'metadata' / 'NON_MF_PROOF_LEDGER.md'
    if not path.exists():
        return {}
    txt = path.read_text(encoding='utf-8')
    m = re.search(r'<!-- LEDGER-STEPS -->(.*?)<!-- END-LEDGER-STEPS -->', txt, re.S)
    if not m:
        return {}
    by_anchor = {}
    for line in m.group(1).splitlines():
        line = line.strip()
        if not line.startswith('|'):
            continue
        cells = [c.strip() for c in line.strip('|').split('|')]
        if len(cells) < 6 or cells[0] in ('Step', '') or set(cells[0]) <= set('- '):
            continue
        decls = [d.strip().strip('`') for d in cells[3].split(';')]
        decls = [d for d in decls if d and d != '-']
        claim, tombstone = scrub_claim(cells[2])
        if tombstone:
            # A tombstoned row is not a step of any printed proof -- it is a
            # citation, a piece of terminology, or a note that some unrelated
            # strengthening is still open, kept in the ledger only so that
            # references to its ID still resolve.  The paper page grades
            # proofs, so such a row has nothing to say there: printing it
            # would show repository bookkeeping, and counting it would report
            # a proof as unformalized because of a footnote.
            continue
        row = {
            'step': cells[0],
            'decls': decls,
            'stmt': cells[4],
            'proof': cells[5],
        }
        if cells[5] != 'EXACT':
            # Only steps that fall short are printed, so only their claims
            # are carried.  Those cells are TeX, kept that way by
            # scripts/check_ledger_claims_typeset.py.
            row['claim'] = claim[:240]
            # the rare case, and the only one a reader needs explained: say
            # whether the step is quoted from the literature or posed as open,
            # and name what it rests on
            row['why'] = cells[7] if len(cells) > 7 else ''
            src = cells[8] if len(cells) > 8 else '-'
            if src and src != '-':
                row['source'] = [x.strip() for x in src.split(',') if x.strip()]
        by_anchor.setdefault(cells[1], []).append(row)
    return by_anchor


# The ledger is repo bookkeeping as well as audit data: a tombstoned row is
# marked by a "MOVED to <path>" prefix pointing at a file in this repository.
# The published page is the paper, not the repository, so no in-repo path is
# ever shipped to it -- the path is how a tombstone is recognized, never
# something the reader sees.
MOVED_RE = re.compile(r'^MOVED to\s+\S+\.md\s*[—-]\s*')
PATH_RE = re.compile(r'\b(?:notes|metadata|scripts|research|tools|bin)/\S+')


def scrub_claim(cell):
    tombstone = bool(MOVED_RE.match(cell))
    text = MOVED_RE.sub('', cell)
    if PATH_RE.search(text):
        print('warn: ledger claim names a repo path, dropped: ' + text[:80],
              file=sys.stderr)
        text = PATH_RE.sub('', text).strip(' —-')
    return text.strip(), tombstone


# What the page serves is the paper.  Anything that describes how the paper is
# produced -- the name of a file in this repository, the vocabulary of the
# grading process -- belongs to the workshop, not to a reader, and reaches the
# page only by accident: a TeX comment, a note inside a Lean proof the drawer
# displays, a table cell copied straight through.  These say where.
LEAK_RE = re.compile(
    r'\b(?:notes|metadata|scripts|research|tools|bin|docs|experiments)/[\w./-]+'
    r'|[\w./-]+\.md\b'
    r'|\bledgers?\b|\baudit(?:s|ed|ing|or)?\b', re.I)


def report_leaks(name, payload):
    seen = set()
    for m in LEAK_RE.finditer(payload):
        word = m.group(0)
        if word in seen:
            continue
        seen.add(word)
        ctx = re.sub(r'\s+', ' ', payload[max(0, m.start() - 60):m.end() + 40])
        print(f'warn: {name} carries "{word}" -> ...{ctx}...', file=sys.stderr)


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
    tex = strip_tex_comments(read(REPO / 'non_mf_groups_exist.tex'))
    claims = read(REPO / 'metadata' / 'NON_MF_NUMBERED_CLAIMS.json')

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

    # the statement of every declaration in a cited module, so the page can
    # resolve identifiers a proof mentions into an expandable statement
    lean_sigs = {}
    for module in sorted({m for m, _ in wanted}):
        path = REPO / 'GroupApproximation' / (module + '.lean')
        if not path.exists():
            path = REPO / (module + '.lean')
        if not path.exists():
            continue
        srcm = path.read_text(encoding='utf-8')
        spans_m = comment_spans(srcm)
        for m2 in DECL_HEAD.finditer(srcm):
            if in_any(spans_m, m2.start()):
                continue
            key = module + '|' + m2.group(2)
            if key in lean_sigs:
                continue
            line = srcm.count('\n', 0, m2.start(1)) + 1
            stop = NEXT_TOP.search(srcm, m2.end())
            codem = srcm[m2.start(1):stop.start() if stop else len(srcm)]
            at = split_signature(codem)
            sig, _ = cap((codem[:at] if at >= 0 else codem).rstrip(), 30, 2500)
            lean_sigs[key] = {'sig': sig, 'line': line}
    data_js = (
        'window.PAPER_TEX = ' + json.dumps(tex).replace('</', '<\\/') + ';\n'
        'window.CLAIMS = ' + json.dumps(json.loads(claims)).replace('</', '<\\/') + ';\n'
        'window.LEAN_SRC = ' + json.dumps(lean_src).replace('</', '<\\/') + ';\n'
        'window.LEAN_SIGS = ' + json.dumps(lean_sigs).replace('</', '<\\/') + ';\n'
        'window.STEPS = ' + json.dumps(parse_steps()).replace('</', '<\\/') + ';\n'
    )

    for name, payload in [
        ('FRESHNESS_JS', freshness_js), ('KATEX_JS', katex_js),
        ('PARSER_JS', parser_js), ('UI_JS', ui_js), ('ENHANCE_JS', enhance_js),
        ('DATA_JS', data_js),
    ]:
        if '</script' in payload.replace('<\\/script', ''):
            sys.exit(f'{name} contains a literal </script sequence')
        report_leaks(name, payload)


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

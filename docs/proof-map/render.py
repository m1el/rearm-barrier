#!/usr/bin/env python3
"""Render contracted.json + layout.json -> rearm-map.html (narrow vertical).

One pre-laid-out section per view; a <select> picks the root theorem."""
import json, html, math

C = json.load(open('contracted.json'))
L = json.load(open('layout.json'))
D = json.load(open('depgraph.json'))

P = 'RearmBarrier.'
GROUPS = [
    ('Protocol inv',   [P+'Protocol', P+'StepInvariant']),
    ('Tree inv',       [P+'TreeInvariant', P+'TreeInit']),
    ('Tree / defs',    [P+'TreeProofs', P+'TreeModel', P+'Tree', P+'Basics', P+'Model']),
    ('Happens-before', [P+'Hb']),
    ('Refinement',     [P+'Refinement', P+'Completion']),
    ('WalkInv',        [P+'WalkInv']),
    ('WeakMemory',     [P+'WeakMemory']),
    ('Spec / NoFault', [P+'SpecProofs', P+'TreeCheck', P+'NoFault']),
    ('ExecutionOrder', [P+'ExecutionOrder']),
]
MOD2G = {m: gi for gi, (_, mods) in enumerate(GROUPS) for m in mods}
def grp(module): return MOD2G.get(module, 2)

def short(n):
    return n[len(P):] if n.startswith(P) else n

def filetag(module):
    return module.replace(P, '') + '.lean'

TYPE_PRE = ('RearmBarrier.WeakMemory.', 'RearmBarrier.Completion.',
            'RearmBarrier.ExecutionOrder.', 'RearmBarrier.')
def shortT(t):
    """Statement for display: strip project prefixes, HTML-escape."""
    for pre in TYPE_PRE:
        t = t.replace(pre, '')
    return html.escape(t)

star_desc = {
    # the spine
    'reachable_no_race': 'Race freedom: with Strong orderings no reachable state has a step that is Outcome.race',
    'reachable_hbInv': 'HbInv (every clock fact) holds in every reachable state',
    'reachable_inv': 'The protocol invariant Inv holds in every reachable state; needs only 1 ≤ workers, 2 ≤ cluster',
    'step_consumer_inv': 'Every consumer step preserves InvAt (version, probe, tree, consumer phases, finisher)',
    'step_consumer_treeInv': 'Every consumer step preserves the path-indexed counting invariant TreeInv',
    'walk_preserves': 'One fetch_add walk preserves TreeInv, split into self / parent / other nodes',
    'nodeInv_self': 'NodeInv at the node the walker just updated',
    'walk_spec': 'Tree.walk = one fetch_add on the cursor node; updated version/counter stated explicitly',
    # other audited entrypoints
    'reachable_absInv': 'The model refines the Completion game: Completion.Inv of the abstract tree in every reachable state',
    'reachable_violations_nil': 'Spec.violations is empty in every reachable state',
    'reachable_finalViolations_nil': 'Spec.finalViolations is empty in every reachable final state',
    'reachable_no_fault': 'No thread has a step that is Outcome.fault from a reachable state',
    'WeakMemory.reachable_projection': 'Stuttering reduction: every history-machine state projects to a reachable model state',
    'WeakMemory.transition_projects': 'One history-machine transition projects to a model step or a stutter',
    'WeakMemory.lift_reachable': 'Converse: every original execution lifts to the history machine',
    'WeakMemory.pending_write_stable': 'A saved observation stays current until its fence',
    'WeakMemory.consumer_reads_publication': 'A consumer\'s successful stale-tolerant read is supplied by the actual publication RMW',
    'WeakMemory.producer_reads_completion': 'The producer\'s successful read is supplied by the actual completion RMW',
    'WeakMemory.reachable_attempt_no_race': 'Race freedom for every attempted access on the stale-read history machine',
    'WeakMemory.reachable_attempt_no_fault': 'Fault freedom for every attempted history-machine access',
    'WeakMemory.reachable_violations_nil': 'Spec.violations is empty on the history machine',
    'WeakMemory.reachable_finalViolations_nil': 'Spec.finalViolations is empty on the history machine',
    'ExecutionOrder.acyclic': 'HB ∪ one probe modification order ∪ write-write coherence is acyclic (no SC/race premises, no axioms)',
    'ExecutionOrder.key_before': 'Finite events get ordering keys that respect both orders',
    'ExecutionOrder.key_injective': 'Those ordering keys are distinct',
    # unaudited extra roots
    'Completion.run_completes': 'Abstract game only: a fresh run that can go no further is done, and the done clock dominates every consumer\'s',
    'Completion.Fresh.inv': 'A fresh tree satisfies the game invariant',
    'Completion.done_clock': 'A done node\'s clock dominates the clock of every consumer below it',
    'Completion.progress': 'If every consumer has contributed and the node is not done, a step is possible',
    # intermediates
    'WeakMemory.reachable_machineInv': 'MachineInv and original-model reachability, derived together',
    'WeakMemory.transition_inv': 'One history-machine transition preserves MachineInv',
    'WeakMemory.reachable_write_source': 'Every probe value in the history has a supplying reachable write',
    'step_consumer_hbInv': 'Every consumer step preserves HbInv',
    'step_producer_hbInv': 'Every producer step preserves HbInv',
    'treeHb_walk': 'The TreeHb clauses (filled / leaf / counted / walker) across one fetch_add',
    'consumer_no_race': 'No consumer step races, given HbInv + Strong',
    'producer_no_race': 'No producer step races, given HbInv + Strong',
    'init_hbInv': 'HbInv holds initially',
    'reachable_wInv': 'WalkInv (walkers carry the child they came through) in every reachable state',
    'walkInv_walk': 'WalkInv across one walk: filling a node and continuing',
    'refine_step': 'Every model step is Completion Steps or a reset to Fresh',
    'sim': 'Path-indexed simulation of one walk by the abstract game',
    'core_inner': 'Inner fetch_add = apply of the child the walker came through',
    'core_leaf': 'Leaf fetch_add = inner(finish) then apply of the consumer',
    'Completion.Step.inv': 'The abstract Completion game step preserves its invariant',
    'reachable_dataInv': 'Job and result slots match the producer/consumer phases in every reachable state',
    'violations_nil': 'Every clause of Spec.violations is ruled out by Inv + DataInv',
    'nodeViolations_nil': 'Each executable node check ↔ a NodeInv clause',
    'step_producer_inv': 'Every producer step preserves InvAt',
    'nodeInv_parent': 'NodeInv at the parent of the updated node',
    'nodeInv_other': 'NodeInv at every node the walk did not touch',
    'init_inv': 'Inv holds in the initial state',
    'init_treeInv': 'TreeInv holds for the freshly built tree',
    'consumer_no_fault': 'No consumer step faults (walk_ok: node exists, version matches, no overflow)',
    'step_consumer_move': 'Every consumer step = one ConsumerMove + setConsumer',
    'step_producer_move': 'Every producer step = one ProducerMove',
}

# every theorem's display data, shared by all views: [short, file, lines, statement]
THM = {}
for n in D['nodes']:
    l0, l1 = n['lines']
    THM[n['name']] = [short(n['name']), filetag(n['module']), max(1, l1 - l0 + 1),
                      shortT(n.get('type', ''))]
DESC = {n: star_desc[short(n)] for n in THM if short(n) in star_desc}

DOT_PITCH = 10.0
MARG = 30


def view_label(v):
    if len(v['roots']) == 1:
        return short(v['roots'][0]) + ('' if v['audited'] else ' (not audited)')
    return f"all {len(v['roots'])} audited entrypoints"


def render_view(v, lay):
    """One view -> (section HTML, per-view JS data)."""
    boxes = lay['boxes']; edges = lay['edges']
    majors = {m['name']: m for m in v['majors']}
    stats = v['stats']
    single = len(v['roots']) == 1

    minx = min(b['x'] - b['w']/2 for b in boxes.values())
    maxx = max(b['x'] + b['w']/2 for b in boxes.values())
    miny = min(b['y'] - b['h']/2 for b in boxes.values())
    maxy = max(b['y'] + b['h']/2 for b in boxes.values())
    def X(x): return x - minx + MARG
    def Y(y): return y - miny + MARG
    W = maxx - minx + 2*MARG
    H = maxy - miny + 2*MARG

    STARSET = {m['name'] for m in v['majors'] if m['star']}

    # ---------- edges ----------
    def path(e):
        (x0, y0), (x1, y1) = e['pts']
        y0 += boxes[e['a']]['h']/2 - 2
        y1 -= boxes[e['b']]['h']/2 - 2
        ym = (y0 + y1) / 2
        return (f"M{X(x0):.0f},{Y(y0):.0f}"
                f"C{X(x0):.0f},{Y(ym):.0f} {X(x1):.0f},{Y(ym):.0f} {X(x1):.0f},{Y(y1):.0f}")

    edge_svg = []
    for e in edges:
        spine = e['a'] in STARSET and e['b'] in STARSET
        cls = 'edge spine' if spine else 'edge mm'
        edge_svg.append(f'<path class="{cls}" data-a="{e["a"]}" data-b="{e["b"]}" d="{path(e)}"/>')

    # ---------- major boxes ----------
    def dot(attr, mm, cx, cy):
        r = min(2.2 + 0.5 * math.sqrt(mm['lines']), 4.6)
        did = html.escape(mm['name'], quote=True)
        return f'<circle class="dot dg{grp(mm["module"])}" {attr}="{did}" cx="{cx:.1f}" cy="{cy:.1f}" r="{r:.1f}"/>'

    node_svg = []
    for name, b in boxes.items():
        m = majors[name]
        g = grp(m['module'])
        x0, y0 = X(b['x'] - b['w']/2), Y(b['y'] - b['h']/2)
        nid = html.escape(name, quote=True)
        star = (' star' if m['star'] else '') + (' root' if m['root'] else '')
        parts = [f'<g class="major g{g}{star}" data-n="{nid}">']
        parts.append(f'<rect class="mbox" x="{x0:.0f}" y="{y0:.0f}" width="{b["w"]:.0f}" height="{b["h"]:.0f}" rx="9"/>')
        tx = x0 + 12
        if m['star']:
            parts.append(f'<circle class="mnum" cx="{tx+8:.0f}" cy="{y0+15:.0f}" r="8"/>'
                         f'<text class="mnumt" x="{tx+8:.0f}" y="{y0+18.5:.0f}">{m["num"]}</text>')
            tx += 22
        parts.append(f'<text class="mtitle" x="{tx:.0f}" y="{y0+19:.0f}">{html.escape(short(name))}</text>')
        parts.append(f'<text class="msub" x="{x0+12:.0f}" y="{y0+33:.0f}">{html.escape(filetag(m["module"]))} · {m["lines"]}L{" · audited" if m["root"] else ""}</text>')
        n = len(m['bag'])
        if n:
            cols = b['cols']
            gx = x0 + (b['w'] - cols * DOT_PITCH) / 2 + DOT_PITCH/2
            gy = y0 + 42 + DOT_PITCH/2
            for i, mm in enumerate(m['bag']):
                parts.append(dot('data-d', mm, gx + (i % cols) * DOT_PITCH, gy + (i // cols) * DOT_PITCH))
        if m['shared']:
            sy = y0 + 42 + (b['rows'] * DOT_PITCH + 6 if n else 0)
            ly = sy + 7
            parts.append(f'<line class="sep" x1="{x0+10:.0f}" y1="{ly:.1f}" x2="{x0+b["w"]-10:.0f}" y2="{ly:.1f}"/>')
            parts.append(f'<text class="sepl" x="{X(b["x"]):.0f}" y="{ly+3:.1f}">shared</text>')
            scols = b['scols']
            sgx = x0 + (b['w'] - scols * DOT_PITCH) / 2 + DOT_PITCH/2
            sgy = sy + 14 + DOT_PITCH/2
            for i, mm in enumerate(m['shared']):
                parts.append(dot('data-sd', mm, sgx + (i % scols) * DOT_PITCH, sgy + (i // scols) * DOT_PITCH))
        parts.append('</g>')
        node_svg.append(''.join(parts))

    # ---------- JS data ----------
    adj = {}
    for e in edges:
        adj.setdefault(e['a'], [[], []])[0].append(e['b'])
        adj.setdefault(e['b'], [[], []])[1].append(e['a'])
    box = {name: [len(m['bag']), len(m['shared'])] for name, m in majors.items()}
    sh = {}
    for m in v['majors']:
        for x in m['shared']:
            sh.setdefault(x['name'], sorted({short(c) for c in x['co']} | {short(m['name'])}))
    tb = {x['name']: x['owners'] for x in v['toolbox']}

    # ---------- legend / lists ----------
    gcount = {}
    def bump(mod):
        gcount[grp(mod)] = gcount.get(grp(mod), 0) + 1
    for m in v['majors']:
        bump(m['module'])
        for x in m['bag']:
            bump(x['module'])
    for c in v['clusters']:
        for x in c['members']:
            bump(x['module'])
    for x in v['toolbox']:
        bump(x['module'])

    legend = ''.join(
        f'<span class="lg"><i class="sw g{i}"></i>{html.escape(gn)}<em>{gcount.get(i,0)}</em></span>'
        for i, (gn, _) in enumerate(GROUPS) if gcount.get(i))

    story = sorted((m for m in v['majors'] if m['star']), key=lambda m: m['num'])
    spine_list = ''.join(
        f'<li><b class="num">{m["num"]}</b><div><code>{html.escape(short(m["name"]))}</code>'
        f'<span class="fl">{html.escape(filetag(m["module"]))} · {m["lines"]} lines'
        f'{" · holds " + str(len(m["bag"])) + " private lemmas" if m["bag"] else ""}</span>'
        f'<p>{html.escape(star_desc.get(short(m["name"]), ""))}</p></div></li>'
        for m in story)

    toolbox_html = ''.join(
        f'<span class="chip tb" data-tb="{html.escape(x["name"], quote=True)}">'
        f'<i class="sw g{grp(x["module"])}"></i><code>{html.escape(short(x["name"]))}</code><em>×{x["owners"]}</em></span>'
        for x in v['toolbox'])

    key_rows = sorted(v['majors'], key=lambda m: -m['lines'])
    tbl = ''.join(
        f'<tr><td><code>{html.escape(short(m["name"]))}</code></td><td>{html.escape(filetag(m["module"]))}</td>'
        f'<td class="r">{m["lines"]}</td><td class="r">{len(m["bag"])}</td><td class="r">{len(m["shared"])}</td><td class="r">{m["indeg"]}</td></tr>'
        for m in key_rows)

    nroots = sum(1 for m in v['majors'] if m['root'])
    tbmin = min((x['owners'] for x in v['toolbox']), default=0)
    tbmax = max((x['owners'] for x in v['toolbox']), default=0)
    beneath = (f'<code>{html.escape(short(v["roots"][0]))}</code>' if single else
               f'the {len(v["roots"])} audited entrypoints of <code>model/ProofAudit.lean</code>')
    toolbox_sect = (f'''<div class="sect">Shared toolbox</div>
<p class="note">Plumbing facts used beneath {tbmin}–{tbmax} of the boxes above (invariant field projections, <code>Wf</code>/<code>Tree.get</code> window facts, list update lemmas). Edges omitted to keep the graph readable — hover for counts.</p>
<div class="toolbox">{toolbox_html}</div>''' if v['toolbox'] else '')
    spine_sect = (f'''<div class="sect">The spine, in order</div>
<ol class="cols">{spine_list}</ol>''' if story else '')

    section = f'''<section class="view" data-view="{v['id']}" hidden>
<p class="intro">The {stats['majors']} load-bearing lemma{'s' if stats['majors'] != 1 else ''} beneath {beneath}, flowing top&nbsp;→&nbsp;down
   to the leaf facts. The <b>{stats['absorbed']} private support lemmas</b> — used beneath exactly one box — are the dots packed
   <i>inside</i> that box (dot area ≈ proof length, color = source file). Support a box <b>shares</b> with other boxes appears
   as dots too, below the dashed divider — hover one to see who else uses it.{f" The toolbox strip at the bottom holds the {stats['toolbox']} plumbing facts used all over." if v['toolbox'] else ''}</p>
<div class="chips">
  <span class="chip"><b>{stats['nodes']}</b> theorems</span>
  <span class="chip"><b>{nroots}</b> audited entrypoint{'s' if nroots != 1 else ''} inside</span>
  <span class="chip"><b>{stats['majors']}</b> major</span>
  <span class="chip"><b>{stats['absorbed']}</b> folded into boxes</span>
  <span class="chip"><b>{stats['sharedLemmas']}</b> shared, below the dividers</span>
  <span class="chip"><b>{stats['toolbox']}</b> in the toolbox</span>
</div>
<div class="legend">{legend}</div>
<div class="vizwrap"><svg class="g" viewBox="0 0 {W:.0f} {H:.0f}" style="max-width:{W:.0f}px" xmlns="http://www.w3.org/2000/svg">
<g>{''.join(edge_svg)}</g>
<g>{''.join(node_svg)}</g>
</svg></div>
{toolbox_sect}
{spine_sect}
<details><summary>Table view — the {stats['majors']} major lemma{'s' if stats['majors'] != 1 else ''}</summary>
<table><tr><th>lemma</th><th>file</th><th class="r">proof lines</th><th class="r">private support</th><th class="r">shared support</th><th class="r">used by</th></tr>{tbl}</table>
</details>
</section>'''
    return section, {'adj': adj, 'box': box, 'sh': sh, 'tb': tb}


sections, VIEWS = [], {}
for v in C['views']:
    sec, data = render_view(v, L[v['id']])
    sections.append(sec)
    VIEWS[v['id']] = dict(data, hash=('all' if len(v['roots']) != 1 else short(v['roots'][0])))

options = ''.join(
    f'<option value="{v["id"]}"{" selected" if v["id"] == C["default"] else ""}>'
    f'{html.escape(view_label(v))} — {v["stats"]["nodes"]} theorem{"s" if v["stats"]["nodes"] != 1 else ""}</option>'
    for v in C['views'])
ROOTDESC = {v['id']: (star_desc.get(short(v['roots'][0]), '') if len(v['roots']) == 1 else
                      'Every audited entrypoint together, so shared structure between the theorems is visible')
            for v in C['views']}

page = f'''<!doctype html>
<html lang="en"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Rearm Barrier Proof Map</title>
<style>
body {{ margin: 0 }}
.viz-root {{
  --page:#f9f9f7; --surface:#fcfcfb; --card:#ffffff; --ink:#0b0b0b; --ink2:#52514e; --muted:#898781;
  --grid:#e1e0d9; --border:rgba(11,11,11,.10); --edge:#8b8a84; --halo:#fcfcfb;
  --c0:#2a78d6; --c1:#1baf7a; --c2:#008300; --c3:#4a3aa7; --c4:#eb6834;
  --c5:#e87ba4; --c6:#e34948; --c7:#eda100; --c8:#0b0b0b;
}}
@media (prefers-color-scheme: dark) {{ :root:not([data-theme="light"]) .viz-root {{
  --page:#0d0d0d; --surface:#1a1a19; --card:#222221; --ink:#ffffff; --ink2:#c3c2b7; --muted:#898781;
  --grid:#2c2c2a; --border:rgba(255,255,255,.10); --edge:#84837d; --halo:#1a1a19;
  --c0:#3987e5; --c1:#199e70; --c2:#008300; --c3:#9085e9; --c4:#d95926;
  --c5:#d55181; --c6:#e66767; --c7:#c98500; --c8:#ffffff;
}} }}
:root[data-theme="dark"] .viz-root {{
  --page:#0d0d0d; --surface:#1a1a19; --card:#222221; --ink:#ffffff; --ink2:#c3c2b7; --muted:#898781;
  --grid:#2c2c2a; --border:rgba(255,255,255,.10); --edge:#84837d; --halo:#1a1a19;
  --c0:#3987e5; --c1:#199e70; --c2:#008300; --c3:#9085e9; --c4:#d95926;
  --c5:#d55181; --c6:#e66767; --c7:#c98500; --c8:#ffffff;
}}
.viz-root {{ background:var(--page); color:var(--ink);
  font:14px/1.45 system-ui,-apple-system,"Segoe UI",sans-serif;
  padding:28px 32px 40px; min-height:100vh; box-sizing:border-box; }}
.viz-root .inner {{ max-width:1280px; margin:0 auto; }}
.viz-root header h1 {{ font-size:22px; font-weight:700; margin:0 0 10px; letter-spacing:-.01em; }}
.picker {{ display:flex; flex-wrap:wrap; align-items:center; gap:8px 12px; }}
.picker label {{ font-size:13px; font-weight:650; color:var(--ink2); }}
.picker select {{ font:13px ui-monospace,Menlo,Consolas,monospace; color:var(--ink); background:var(--card);
  border:1px solid var(--border); border-radius:8px; padding:6px 10px; max-width:100%; }}
.picker .rootdesc {{ color:var(--ink2); font-size:13px; }}
.intro {{ margin:12px 0 0; color:var(--ink2); font-size:13.5px; max-width:78em; }}
.chips {{ display:flex; gap:8px; margin:14px 0 0; flex-wrap:wrap; }}
.chip {{ background:var(--surface); border:1px solid var(--border); border-radius:8px;
  padding:6px 12px; font-size:12.5px; color:var(--ink2); }}
.chip b {{ color:var(--ink); font-weight:650; }}
.legend {{ display:flex; gap:14px; flex-wrap:wrap; margin:16px 0 6px; font-size:12.5px; color:var(--ink2); align-items:center; }}
.lg {{ display:inline-flex; align-items:center; gap:6px; }}
.lg em {{ font-style:normal; color:var(--muted); }}
.sw {{ width:10px; height:10px; border-radius:3px; display:inline-block; flex:none; }}
.sw.g0{{background:var(--c0)}} .sw.g1{{background:var(--c1)}} .sw.g2{{background:var(--c2)}}
.sw.g3{{background:var(--c3)}} .sw.g4{{background:var(--c4)}} .sw.g5{{background:var(--c5)}}
.sw.g6{{background:var(--c6)}} .sw.g7{{background:var(--c7)}} .sw.g8{{background:var(--c8)}}
.howto {{ color:var(--muted); font-size:12.5px; margin:10px 0 0; }}
.vizwrap {{ overflow-x:auto; background:var(--surface); border:1px solid var(--border);
  border-radius:12px; margin-top:8px; }}
.vizwrap svg {{ display:block; width:100%; height:auto; margin:0 auto; }}
svg .edge {{ fill:none; }}
svg .edge.mm {{ stroke:var(--edge); stroke-opacity:.5; stroke-width:1.4; }}
svg .edge.spine {{ stroke:var(--ink); stroke-opacity:.72; stroke-width:2.8; }}
svg .mbox {{ fill:var(--card); stroke-width:1.4; }}
svg .major.g0 .mbox{{stroke:var(--c0)}} svg .major.g1 .mbox{{stroke:var(--c1)}}
svg .major.g2 .mbox{{stroke:var(--c2)}} svg .major.g3 .mbox{{stroke:var(--c3)}}
svg .major.g4 .mbox{{stroke:var(--c4)}} svg .major.g5 .mbox{{stroke:var(--c5)}}
svg .major.g6 .mbox{{stroke:var(--c6)}} svg .major.g7 .mbox{{stroke:var(--c7)}}
svg .major.g8 .mbox{{stroke:var(--c8); stroke-width:2;}}
svg .major.star .mbox {{ stroke-width:2.2; }}
svg .major.root .mbox {{ stroke-width:2.6; stroke-dasharray:7 3; }}
svg .mtitle {{ font:600 12.5px ui-monospace,Menlo,Consolas,monospace; fill:var(--ink); }}
svg .msub {{ font:10px system-ui,sans-serif; fill:var(--muted); }}
svg .mnum {{ fill:var(--ink); }}
svg .mnumt {{ font:700 10.5px system-ui,sans-serif; fill:var(--halo); text-anchor:middle; }}
svg .dot {{ stroke:var(--card); stroke-width:.8; }}
svg .dot.dg0{{fill:var(--c0)}} svg .dot.dg1{{fill:var(--c1)}} svg .dot.dg2{{fill:var(--c2)}}
svg .dot.dg3{{fill:var(--c3)}} svg .dot.dg4{{fill:var(--c4)}} svg .dot.dg5{{fill:var(--c5)}}
svg .dot.dg6{{fill:var(--c6)}} svg .dot.dg7{{fill:var(--c7)}} svg .dot.dg8{{fill:var(--c8)}}
svg .sep {{ stroke:var(--muted); stroke-width:1; stroke-dasharray:4 3.5; }}
svg .sepl {{ font:9px system-ui,sans-serif; fill:var(--muted); text-anchor:middle;
  paint-order:stroke; stroke:var(--card); stroke-width:5; }}
svg.dimmed .edge {{ stroke-opacity:.07; }}
svg.dimmed .major {{ opacity:.18; }}
svg.dimmed .edge.hi {{ stroke:var(--ink); stroke-opacity:.78; stroke-width:1.8; }}
svg.dimmed .major.hi {{ opacity:1; }}
.tip {{ position:fixed; z-index:9; pointer-events:none; background:var(--card);
  border:1px solid var(--border); border-radius:10px; padding:10px 12px; max-width:480px;
  box-shadow:0 6px 24px rgba(0,0,0,.18); display:none; font-size:12.5px; color:var(--ink2); }}
.tip code {{ color:var(--ink); font-weight:650; font-size:13px; font-family:ui-monospace,Menlo,Consolas,monospace; }}
.tip .m {{ color:var(--muted); margin:2px 0 4px; }}
.tip pre.sig {{ margin:8px 0 0; padding:7px 9px; background:var(--surface);
  border:1px solid var(--border); border-radius:8px; white-space:pre; overflow:hidden;
  font:10.5px/1.5 ui-monospace,Menlo,Consolas,monospace; color:var(--ink2); }}
.tip .co code {{ font-weight:500; font-size:12px; }}
.sect {{ font-size:15px; font-weight:700; margin:26px 0 2px; }}
.note {{ color:var(--muted); font-size:12.5px; margin:0 0 8px; }}
.toolbox {{ display:flex; flex-wrap:wrap; gap:6px; margin-top:10px; }}
.chip.tb {{ display:inline-flex; align-items:center; gap:7px; padding:4px 10px; }}
.chip.tb code {{ font-size:12px; font-family:ui-monospace,Menlo,Consolas,monospace; color:var(--ink); }}
.chip.tb em {{ font-style:normal; color:var(--muted); font-size:11px; }}
.cols {{ display:grid; grid-template-columns:repeat(auto-fit,minmax(min(340px,100%),1fr)); gap:4px 28px;
  margin:14px 0 0; padding:0; list-style:none; }}
.cols li {{ display:flex; gap:10px; padding:7px 0; border-bottom:1px solid var(--grid); }}
.cols .num {{ flex:0 0 22px; height:22px; border-radius:50%; background:var(--ink); color:var(--halo);
  font-size:11.5px; font-weight:700; display:flex; align-items:center; justify-content:center; margin-top:2px; }}
.cols code {{ font-size:13px; font-weight:650; color:var(--ink); font-family:ui-monospace,Menlo,Consolas,monospace; }}
.cols .fl {{ color:var(--muted); font-size:11.5px; margin-left:8px; }}
.cols p {{ margin:2px 0 0; color:var(--ink2); font-size:12.5px; }}
details {{ margin-top:22px; }}
details summary {{ cursor:pointer; color:var(--ink2); font-size:13px; }}
details table {{ border-collapse:collapse; margin-top:10px; font-size:12.5px; color:var(--ink); }}
details th, details td {{ text-align:left; padding:4px 14px 4px 0; border-bottom:1px solid var(--grid); }}
details th {{ color:var(--muted); font-weight:600; }}
details td.r, details th.r {{ text-align:right; font-variant-numeric:tabular-nums; }}
details code {{ font-family:ui-monospace,Menlo,Consolas,monospace; }}
@media (max-width: 640px) {{ .viz-root {{ padding:20px 16px 32px; }} }}
</style>
</head><body>
<div class="viz-root"><div class="inner">
<header>
  <h1>The rearm-barrier model proofs — the argument, with its support folded in</h1>
  <div class="picker">
    <label for="root">Root theorem</label>
    <select id="root">{options}</select>
    <span class="rootdesc" id="rootdesc"></span>
  </div>
  <p class="howto">An arrow means the upper lemma (or its private support) uses the lower one; the heavy dark path is the spine
     (race freedom down to one <code>fetch_add</code>); dashed boxes are audited entrypoints of <code>model/ProofAudit.lean</code>.
     Hover any box, dot or toolbox chip to see the full theorem statement. Axioms: <b>[propext, Classical.choice, Quot.sound]</b>.</p>
</header>
{''.join(sections)}
<div class="tip" id="tip"></div>
</div></div>
<script>
const THM = {json.dumps(THM, ensure_ascii=False)};
const DESC = {json.dumps(DESC, ensure_ascii=False)};
const VIEWS = {json.dumps(VIEWS, ensure_ascii=False)};
const ROOTDESC = {json.dumps(ROOTDESC, ensure_ascii=False)};
const SIG_MAX = 24;
function sig(t) {{
  if (!t) return '';
  const lines = t.split('\\n');
  return `<pre class="sig">${{lines.slice(0, SIG_MAX).join('\\n')}}</pre>` +
    (lines.length > SIG_MAX ? `<div class="m">… ${{lines.length - SIG_MAX}} more lines</div>` : '');
}}
const lines = n => `${{n}} proof line${{n>1?'s':''}}`;
const tip = document.getElementById('tip'), sel = document.getElementById('root');
const rootdesc = document.getElementById('rootdesc');
const sections = {{}};
for (const s of document.querySelectorAll('section.view')) sections[s.dataset.view] = s;
let V = null, svg = null;

function unfocus() {{
  if (!svg) return;
  svg.classList.remove('dimmed');
  svg.querySelectorAll('.hi').forEach(e => e.classList.remove('hi'));
  tip.style.display = 'none';
}}
function focus(name) {{
  svg.classList.add('dimmed');
  const nbr = new Set([name, ...(V.adj[name]?.[0]??[]), ...(V.adj[name]?.[1]??[])]);
  for (const el of svg.querySelectorAll('[data-n]'))
    if (nbr.has(el.dataset.n)) el.classList.add('hi');
  for (const e of svg.querySelectorAll('.edge'))
    if (e.dataset.a === name || e.dataset.b === name) e.classList.add('hi');
}}
function show(id, push) {{
  if (!sections[id]) id = sel.options[0].value;
  unfocus();
  for (const [k, s] of Object.entries(sections)) s.hidden = k !== id;
  sel.value = id;
  V = VIEWS[id];
  svg = sections[id].querySelector('svg');
  rootdesc.textContent = ROOTDESC[id];
  if (push) history.replaceState(null, '', '#' + V.hash);
}}
function fromHash() {{
  const h = decodeURIComponent(location.hash.slice(1));
  const hit = Object.keys(VIEWS).find(k => VIEWS[k].hash === h);
  show(hit ?? sel.querySelector('option[selected]')?.value ?? sel.options[0].value, false);
}}
sel.addEventListener('change', () => show(sel.value, true));
addEventListener('hashchange', fromHash);
fromHash();

document.addEventListener('mouseover', ev => {{
  const box = ev.target.closest?.('svg.g [data-n]');
  if (!box) return;
  unfocus();
  const name = box.dataset.n, m = THM[name], [bag, nsh] = V.box[name];
  focus(name);
  const dot = ev.target.closest('[data-d]');
  const sd = ev.target.closest('[data-sd]');
  if (dot) {{
    const d = THM[dot.dataset.d];
    tip.innerHTML = `<code>${{d[0]}}</code><div class="m">${{d[1]}} · ${{lines(d[2])}}</div>` +
      `private support of <code>${{m[0]}}</code>` + sig(d[3]);
  }} else if (sd) {{
    const d = THM[sd.dataset.sd];
    tip.innerHTML = `<code>${{d[0]}}</code><div class="m">${{d[1]}} · ${{lines(d[2])}}</div>` +
      `<span class="co">shared support of ${{V.sh[sd.dataset.sd].map(x => `<code>${{x}}</code>`).join(', ')}}</span>` + sig(d[3]);
  }} else {{
    tip.innerHTML = `<code>${{m[0]}}</code><div class="m">${{m[1]}} · ${{m[2]}} proof lines</div>` +
      (bag ? `holds ${{bag}} private support lemma${{bag>1?'s':''}}` : 'no private support — leans on shared facts') +
      (nsh ? ` · shares ${{nsh}}` : '') +
      (DESC[name] ? `<div style="margin-top:6px">${{DESC[name]}}</div>` : '') + sig(m[3]);
  }}
  tip.style.display = 'block';
}});
document.addEventListener('mouseout', ev => {{ if (ev.target.closest?.('svg.g [data-n]')) unfocus(); }});
document.addEventListener('mousemove', ev => {{
  const pad = 14;
  let x = ev.clientX + pad, y = ev.clientY + pad;
  const r = tip.getBoundingClientRect();
  if (x + r.width > innerWidth - 8) x = ev.clientX - r.width - pad;
  if (y + r.height > innerHeight - 8) y = Math.max(8, ev.clientY - r.height - pad);
  tip.style.left = x + 'px'; tip.style.top = y + 'px';
}});
for (const el of document.querySelectorAll('[data-tb]')) {{
  el.addEventListener('mouseenter', () => {{
    const d = THM[el.dataset.tb];
    tip.innerHTML = `<code>${{d[0]}}</code><div class="m">${{d[1]}} · ${{lines(d[2])}} · used under ${{V.tb[el.dataset.tb]}} boxes</div>` + sig(d[3]);
    tip.style.display = 'block';
  }});
  el.addEventListener('mouseleave', () => {{ tip.style.display = 'none'; }});
}}
</script>
</body></html>
'''
open('rearm-map.html', 'w').write(page)
print(f'wrote rearm-map.html  {len(C["views"])} views  {len(page.encode()) / 1e6:.2f} MB')

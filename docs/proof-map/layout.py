#!/usr/bin/env python3
"""Narrow vertical Sugiyama layout for the contracted graph -> layout.json.

One layout per view in contracted.json. Majors only. Ranks from grandalf; ranks wider than MAXW wrap into stacked
sub-rows (safe: layered DAGs have no same-rank edges, so sub-rows keep every
edge flowing strictly downward).
"""
import json, math
from collections import defaultdict
from grandalf.graphs import Vertex, Edge, Graph
from grandalf.layouts import SugiyamaLayout

MAXW = 1210          # target drawable width for the graph body
XGAP = 20            # min horizontal gap between boxes
SUBROW_GAP = 26      # vertical gap between wrapped sub-rows
LAYER_GAP = 64       # vertical gap between ranks



def short(n):
    return n[len('RearmBarrier.'):] if n.startswith('RearmBarrier.') else n

# ---- box geometry ----
DOT_PITCH = 10.0
def bag_grid(n):
    if n == 0:
        return 0, 0
    cols = max(4, math.ceil(math.sqrt(n * 2.6)))
    rows = math.ceil(n / cols)
    return cols, rows

SEP_H = 14           # divider zone between private and shared dot grids

def layout(C):
    boxes = {}
    for m in C['majors']:
        name = m['name']
        t = short(name)
        title_w = len(t) * 7.6 + (26 if m['star'] else 0)
        cols, rows = bag_grid(len(m['bag']))
        grid_w = cols * DOT_PITCH
        grid_h = rows * DOT_PITCH
        nsh = len(m['shared'])
        scols, srows = bag_grid(nsh)
        sgrid_w = scols * DOT_PITCH
        sgrid_h = srows * DOT_PITCH
        w = max(title_w, 7 * 5.6 + 60, grid_w, sgrid_w) + 24
        h = (44 + (grid_h + 8 if rows else 0)
             + (SEP_H + sgrid_h + 8 if nsh else 0))
        boxes[name] = {'w': w, 'h': h, 'cols': cols, 'rows': rows,
                       'scols': scols, 'srows': srows}

    # ---- grandalf for ranks + initial order ----
    class VView:
        def __init__(self, w, h):
            self.w, self.h = w, h
            self.xy = (0, 0)

    V = {}
    for name, b in boxes.items():
        v = Vertex(name)
        v.view = VView(b['w'] + XGAP, b['h'])
        V[name] = v
    E = [Edge(V[e['a']], V[e['b']]) for e in C['edges']]
    g = Graph(list(V.values()), E)
    # one Sugiyama run per connected component; rank k of every component shares a row
    hasPred = {e['b'] for e in C['edges']}
    merged = defaultdict(list)     # rank index -> [(component, x, name)]
    for ci, comp in enumerate(sorted(g.C, key=lambda c: -len(c.sV))):
        byrank = defaultdict(list)
        if len(comp.sV) == 1:          # grandalf cannot lay out an edgeless vertex
            v = comp.sV[0]
            v.view.xy = (0, 0)
            byrank[0].append(v)
        else:
            sug = SugiyamaLayout(comp)
            sug.xspace = XGAP
            sug.yspace = LAYER_GAP
            roots = [v for v in comp.sV if v.data not in hasPred]
            sug.init_all(roots=roots, optimize=True)
            sug.draw(14)
            for v in comp.sV:
                byrank[round(v.view.xy[1])].append(v)
        for k, y in enumerate(sorted(byrank)):
            merged[k] += [(ci, v.view.xy[0], v.data) for v in byrank[y]]
    ranks = [[n for _, _, n in sorted(merged[k])] for k in sorted(merged)]

    # ---- wrap wide ranks into sub-rows, assign final coords ----
    succ = defaultdict(list); pred = defaultdict(list)
    for e in C['edges']:
        succ[e['a']].append(e['b']); pred[e['b']].append(e['a'])

    pos = {}          # name -> (x, y) center
    ycur = 0.0
    for rank in ranks:
        # split into sub-rows not exceeding MAXW
        rows_, cur, curw = [], [], 0.0
        for n in rank:
            w = boxes[n]['w'] + XGAP
            if cur and curw + w > MAXW:
                rows_.append(cur); cur, curw = [], 0.0
            cur.append(n); curw += w
        rows_.append(cur)
        for row in rows_:
            rowh = max(boxes[n]['h'] for n in row)
            total = sum(boxes[n]['w'] for n in row) + XGAP * (len(row) - 1)
            # center the row near the mean x of the members' already-placed parents
            px = [pos[p][0] for n in row for p in pred[n] if p in pos]
            cx = sum(px) / len(px) if px else 0.0
            cx = max(-MAXW/2 + total/2, min(MAXW/2 - total/2, cx))
            x = cx - total / 2
            for n in row:
                pos[n] = (x + boxes[n]['w'] / 2, ycur + rowh / 2)
                x += boxes[n]['w'] + XGAP
            ycur += rowh + SUBROW_GAP
        ycur += LAYER_GAP - SUBROW_GAP

    out_nodes = {}
    for name, b in boxes.items():
        out_nodes[name] = dict(b, x=pos[name][0], y=pos[name][1])

    out_edges = [dict(e, pts=[list(pos[e['a']]), list(pos[e['b']])]) for e in C['edges']]

    xs = [(b['x'] - b['w']/2, b['x'] + b['w']/2) for b in out_nodes.values()]
    ys = [(b['y'] - b['h']/2, b['y'] + b['h']/2) for b in out_nodes.values()]
    print(f"{C['id']:4s} extent x {min(a for a,_ in xs):.0f}..{max(b for _,b in xs):.0f}  "
          f"y {min(a for a,_ in ys):.0f}..{max(b for _,b in ys):.0f}  ranks={len(ranks)}")
    return {'boxes': out_nodes, 'edges': out_edges}


CC = json.load(open('contracted.json'))
json.dump({v['id']: layout(v) for v in CC['views']}, open('layout.json', 'w'))

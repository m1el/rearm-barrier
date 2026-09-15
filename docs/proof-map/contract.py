#!/usr/bin/env python3
"""Contract depgraph.json around major lemmas -> contracted.json

One view per audited entrypoint and per DepGraph.lean extraRoots theorem (plus one
for all audited entrypoints together); each view contracts only the theorems
reachable from its root(s).

Majors: big boxes. Minors owned by exactly one major: absorbed into its bag.
Minors owned by 2+ majors: grouped per owner-set into shared cluster nodes,
except ubiquitous ones (>= TOOLBOX_MIN owners) which go to the toolbox strip.
"""
import json
from collections import defaultdict, Counter

TOOLBOX_MIN = 6

d = json.load(open('depgraph.json'))
nodes = {n['name']: n for n in d['nodes']}
succ = defaultdict(set)
for a, b in d['edges']:
    succ[a].add(b)
indeg = Counter(b for a, b in d['edges'])

P = 'RearmBarrier.'
# the view shown first: race freedom on the stale-read history machine
DEFAULT_ROOT = P + 'WeakMemory.reachable_attempt_no_race'
# the numbered spine: race freedom down to the one fetch_add step
STORY = [P+x for x in ['WeakMemory.reachable_attempt_no_race',
                       'reachable_no_race', 'reachable_hbInv', 'reachable_inv',
                       'step_consumer_inv', 'step_consumer_treeInv', 'walk_preserves',
                       'nodeInv_self', 'walk_spec']]
ROOTS = [n['name'] for n in d['nodes'] if n.get('root')]   # ProofAudit.lean entrypoints
EXTRA = [n['name'] for n in d['nodes'] if n.get('extra')]  # DepGraph.lean extraRoots
MAJORS = STORY + [r for r in ROOTS + EXTRA if r not in STORY] + [P+x for x in [
    'Completion.Fresh.inv', 'Completion.done_clock', 'Completion.progress',
    'WeakMemory.reachable_machineInv', 'WeakMemory.transition_inv',
    'WeakMemory.reachable_write_source',
    'step_consumer_hbInv', 'step_producer_hbInv', 'treeHb_walk',
    'consumer_no_race', 'producer_no_race', 'init_hbInv',
    'reachable_wInv', 'walkInv_walk',
    'refine_step', 'sim', 'core_inner', 'core_leaf', 'Completion.Step.inv',
    'reachable_dataInv', 'violations_nil', 'nodeViolations_nil',
    'step_producer_inv', 'nodeInv_parent', 'nodeInv_other',
    'init_inv', 'init_treeInv', 'consumer_no_fault',
    'step_consumer_move', 'step_producer_move']]
MAJORS = [m for m in MAJORS if m in nodes]


def reachable(roots):
    seen = set(roots)
    stack = list(roots)
    while stack:
        for y in succ[stack.pop()]:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return seen


def contract(roots):
    vnodes = reachable(roots)
    majors = [m for m in MAJORS if m in vnodes]
    MSET = set(majors)

    # ownership: minor m owned by major j iff m reachable from j through minors only
    own = defaultdict(set)
    reach_minors = {}   # major -> set of minors reachable through minors
    for j in majors:
        seen = set()
        stack = list(succ[j])
        while stack:
            n = stack.pop()
            if n in seen or n in MSET:
                continue
            seen.add(n)
            stack += list(succ[n])
        reach_minors[j] = seen
        for m in seen:
            own[m].add(j)

    minors = [n for n in vnodes if n not in MSET]
    absorbed = {m: next(iter(own[m])) for m in minors if len(own[m]) == 1}
    toolbox = [m for m in minors if len(own[m]) >= TOOLBOX_MIN]
    shared = {m: tuple(sorted(own[m])) for m in minors
              if 2 <= len(own[m]) < TOOLBOX_MIN}

    clusters = defaultdict(list)   # owner-set -> [minor]
    for m, s in shared.items():
        clusters[s].append(m)
    cluster_id = {s: f'C{i}' for i, s in enumerate(sorted(clusters, key=lambda s: (-len(clusters[s]), s)))}

    # ---- contracted edges ----
    # major -> major: k in succ(j) or succ(m) for m in reach_minors[j]
    mm = set()
    for j in majors:
        hits = set()
        for src in [j] + list(reach_minors[j]):
            hits |= succ[src] & MSET
        hits.discard(j)
        for k in hits:
            mm.add((j, k))

    # ---- transitive reduction over the contracted DAG ----
    sc = defaultdict(set)
    for a, b in mm:
        sc[a].add(b)
    reach = {}
    def rset(n):
        if n in reach:
            return reach[n]
        r = set()
        for s2 in sc[n]:
            r.add(s2)
            r |= rset(s2)
        reach[n] = r
        return r
    for n in majors:
        rset(n)
    Ered = sorted((a, b) for a, b in mm
                  if not any(b in reach[s2] for s2 in sc[a] if s2 != b))

    def info(m):
        l0, l1 = nodes[m]['lines']
        return {'name': m, 'module': nodes[m]['module'],
                'lines': max(1, l1 - l0 + 1), 'indeg': indeg[m],
                'type': nodes[m].get('type', ''), 'root': bool(nodes[m].get('root'))}

    shared_of = defaultdict(list)   # major -> [(info, co-owners)]
    for m, s2 in shared.items():
        for j in s2:
            shared_of[j].append(dict(info(m), co=[x for x in s2 if x != j]))
    for j in shared_of:
        shared_of[j].sort(key=lambda x: -x['lines'])

    story = [j for j in STORY if j in MSET]
    out = {
        'roots': list(roots),
        'audited': all(r in ROOTS for r in roots),
        'majors': [dict(info(j),
                        bag=sorted((info(m) for m, o in absorbed.items() if o == j),
                                   key=lambda x: -x['lines']),
                        shared=shared_of.get(j, []),
                        star=(j in story), num=(story.index(j) + 1 if j in story else 0))
                   for j in majors],
        'clusters': [{'id': cid, 'owners': list(s),
                      'members': sorted((info(m) for m in clusters[s]), key=lambda x: -x['lines'])}
                     for s, cid in cluster_id.items()],
        'toolbox': sorted((dict(info(m), owners=len(own[m])) for m in toolbox),
                          key=lambda x: -x['owners']),
        'edges': [{'a': a, 'b': b, 'kind': 'mm'} for a, b in Ered],
        'stats': {'nodes': len(vnodes),
                  'deps': sum(len(succ[n]) for n in vnodes),
                  'majors': len(majors), 'absorbed': len(absorbed),
                  'sharedClusters': len(clusters), 'sharedLemmas': len(shared),
                  'toolbox': len(toolbox)},
    }
    print(f"{roots[0] if len(roots) == 1 else 'ALL':50s} nodes={len(vnodes)} majors={len(majors)} "
          f"absorbed={len(absorbed)} shared={len(shared)} toolbox={len(toolbox)} edges={len(Ered)}")
    return out


# views: single roots, largest subtree first (default root pinned first), then all audited together
order = sorted(ROOTS + EXTRA, key=lambda r: (r != DEFAULT_ROOT, -len(reachable([r])), r))
views = [dict(contract([r]), id=f'v{i}') for i, r in enumerate(order)]
views.append(dict(contract(ROOTS), id='all'))
json.dump({'default': 'v0', 'views': views}, open('contracted.json', 'w'))

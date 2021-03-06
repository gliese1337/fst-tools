export const EPSILON = Symbol('e');

type Token = string | Symbol;

class Edge {
  constructor(
    public input: Token,
    public output: Token,
    public source: number,
    public target: number,
  ) {}
}

class State {
  constructor(
    public n: number,
    public accepts: boolean,
    public edges: Edge[],
  ) {}
}

// Get all of the states that can be reached through
// epsilon transitions, with their associated outputs.
function * epsilon_closure(s: State, fst: FST, prefix: Token[], outprop: "input" | "output") {
  const pair: [State, Token[]] = [s, prefix];
  const stack = [pair];
  const seen = new Set<State>([s]);

  yield pair;

  while (stack.length > 0) {
    const [s, out] = stack.pop() as [State, string[]];
    for (const e of s.edges) {
      if (e.input !== EPSILON) continue;
      if (e.source === e.target) continue; // don't follow self-loops
      const edge_output = e[outprop];
      const nout = edge_output === EPSILON ? out : [...out, edge_output]; 
      const next = fst.states[e.target];
      if (!seen.has(next)) { // break longer cycles
        const pair = [next, nout] as [State, string[]];
        yield pair;
        stack.push(pair);
        seen.add(next);
      }
    }
  }
}

function * double_epsilon_closure(s: State, fst: FST) {
  const stack = [s];
  const seen = new Set<State>([s]);

  yield s;

  while (stack.length > 0) {
    const s = stack.pop() as State;
    for (const e of s.edges) {
      if (e.input !== EPSILON || e.output !== EPSILON) continue;
      if (e.source === e.target) continue; // don't follow self-loops 
      const next = fst.states[e.target];
      if (!seen.has(next)) { // break longer cycles
        yield next;
        stack.push(next);
        seen.add(next);
      }
    }
  }
}

function extend_outputs(
  fst: FST, target: number, prefix: Token[], outprop: "input" | "output",
  outputs: Token[][],
  states: [State, Token[]][],
) {
  const closure = epsilon_closure(fst.states[target], fst, prefix, outprop);
  for (const pair of closure) {
    const [tstate, nout] = pair;
    if (tstate.accepts) outputs.push(nout);
  
    // If the target state has no outgoing edges,
    // then it won't accept any further input,
    // so it's more efficient to just drop it here.
    // Thus, we only push states that have edges.
    if (tstate.edges.length) states.push(pair);
  }
}

export interface Executor {
  outputs: string[][];
  next(i: Token): null | Executor;
}

class _Executor implements Executor {
  
  constructor(
    private inprop: "input" | "output",
    private outprop: "input" | "output",
    private fst: FST,
    private states: [State, string[]][],
    public outputs: string[][],
  ) {}

  next(i: Token) {
    const { fst, states, inprop, outprop } = this;
    const nstates: [State, string[]][] = [];
    const outputs: string[][] = [];
    for (const [state, out] of states) {
      for (const e of state.edges) {
        const input = e[inprop];
        if (input !== i) continue;
        const output = e[outprop];
        const nout = output === EPSILON ? out : [...out, output];
        extend_outputs(fst, e.target, nout, outprop, outputs, nstates);
      }
    }
    if (nstates.length === 0) return null;
    return new _Executor(inprop, outprop, fst, nstates, outputs);
  }
}

export interface Recognizer {
  next(i: Token, o: Token): Recognizer | null;
}

class _Recognizer implements Recognizer {
  constructor(
    private fst: FST,
    private states: State[],
    public accepts: boolean,
  ) {}

  next(i: Token, o = i) {
    const { fst, states } = this;
    const nstates: State[] = [];
    let accepts = false;
    for (const state of states) {
      for (const { input, output, target } of state.edges) {
        if (input !== i || output !== o) continue;
        const state = fst.states[target];
        accepts = accepts || state.accepts;
        nstates.push(state);
      }
    }
    if (nstates.length === 0) return null;
    return new _Recognizer(fst, nstates, accepts);
  }
}

function t2s(t: Token) {
  return typeof t === 'symbol' ? '`' + t.description : "'" + t;
}

function mutate_total(f: FST) {
  const { states } = f;

  // Calculate the implicit alphabet
  const labels = states.flatMap(({ edges }) =>
    edges.map(({ input, output }) => [input, output])
         .filter(([i, o]) => i !== EPSILON && o !== EPSILON)
  ).sort(([a, b], [c, d]) => {
    const cmp = t2s(a).localeCompare(t2s(c));
    return cmp === 0 ? t2s(b).localeCompare(t2s(d)) : cmp;
  });
  const l = labels.length;
  let last = labels[0];
  let j = 1;
  for (let i = 1; i < l; i++) {
    const pair = labels[i];
    if (pair[0] !== last[0] || pair[1] !== last[1]) {
      labels[j++] = pair;
    }
    last = pair;
  }
  labels.length = j;

  // Ensure all states have transitions for all possible labels.
  const newn = states.length;
  let need_new = false;
  for (const s of states) {
    const { n, edges } = s;
    edges.sort(({ input: a, output: b }, { input: c, output: d }) => {
      const cmp = t2s(a).localeCompare(t2s(c));
      return cmp === 0 ? t2s(b).localeCompare(t2s(d)) : cmp;
    });
    
    const nedges = [];
    for (let i = 0, k = 0; i < j; i++) {
      const pair = labels[i];
      const edge = edges[k];
      if (edge && pair[0] == edge.input && pair[1] == edge.output) {
        nedges.push(edge);
        k++;
      } else {
        nedges.push(new Edge(pair[0], pair[1], n, newn));
        need_new = true;
      }
    }
  }

  // If we had to add new transitions,
  // add the new state that accepts them.
  if (need_new) {
    states.push(new State(newn, false,
      labels.map(([i, o]) => new Edge(i, o, newn, newn))
    ));
  }
}

function mutate_union(f: FST, ...gs: FST[]) {
  const fstates = f.states;
  for (const g of gs) {
    const l = fstates.length;
    const l1 = l - 1;
    for (const s of g.states) {
      if (s.n === g.start) {
        // Combine starting states
        const { edges } = f.states[f.start];
        for (const e of s.edges) {
          const target = e.target;
          const ntarget = target == g.start ? f.start :
                          target + (target < g.start ? l : l1);
          edges.push(new Edge(e.input, e.output, f.start, ntarget));
        }
      } else {
        // Append non-starting states, and fix up state indices
        const n = f.states.length;
        const edges = s.edges.map(e => {
          const target = e.target;
          const ntarget = target == g.start ? f.start :
                          target + (target < g.start ? l : l1);
          return new Edge(e.input, e.output, n, ntarget);
        });
        fstates.push(new State(n, s.accepts, edges));
      }
    }
  }
}

function trace(f: FST) {
  // Trace from the start state to find all
  // accessible states, and keep track of the
  // ones that accept, and of backlinks.
  const back = new Map<number, Set<number>>();
  const useful = new Map<number, number>();
  const stack = [f.start];
  let nid = 0;
  while (stack.length > 0) {
    const id = stack.pop() as number;
    const { edges, accepts } = f.states[id];
    if (accepts) useful.set(id, nid++);
    for (const { target } of edges) {
      const parents = back.get(target);
      if (parents) parents.add(id);
      else {
        back.set(target, new Set([id]));
        stack.push(target);
      }
    }
  }

  // Trace backwards to identify all useful states.
  stack.push(...useful.keys());
  while (stack.length > 0) {
    const id = stack.pop() as number;
    for (const parent of back.get(id) as Set<number>) {
      if (useful.has(parent)) continue;
      useful.set(parent, nid++);
      stack.push(parent);
    }
  }

  return useful;
}

export class FST {
  // https://www.aclweb.org/anthology/C88-2113.pdf

  private is_plus = false;
  private is_determined = false;
  private is_total = false;
  private is_minimal = false;
  private is_pruned = false;
  constructor(public states: State[], public start = 0) {}
  
  clone() {
    const nstates = this.states.map(s => new State(
      s.n, s.accepts, s.edges.map(e => new Edge(e.input, e.output, e.source, e.target)),
    ));
    return new FST(nstates, this.start) as FST;
  }
  
  union(...gs: FST[]) {
    if (gs.length === 0) return this;
    const f = this.clone();
    mutate_union(f, ...gs);
    return f;
  }

  intersect(...gs: FST[]) {
    if (gs.length === 0) return this;
    const cs = gs.map(g => g.complement());
    let f = this.complement();
    
    mutate_union(f, ...cs);
    f = f.determinize();
    mutate_total(f);
    f.is_total = true;

    for (const s of f.states) {
      s.accepts = !s.accepts;
    }

    return f;
  }

  // Get all edges in the transducer, augmented with
  // epsilon self-loops on all states to simplify
  // matching in the composition algorithm
  private all_edges_with_loops(){
    const edges: Edge[] = [];
    for (const state of this.states) {
      let has_self_epsilon = false;
      for (const e of state.edges) {
        has_self_epsilon = has_self_epsilon ||
          (e.source === e.target && e.input === EPSILON && e.output === EPSILON);
        edges.push(e);
      }
      if (!has_self_epsilon) {
        edges.push(new Edge(EPSILON, EPSILON, state.n, state.n));
      }
    }

    return edges;
  }

  compose(...gs: FST[]) {
    if (gs.length === 0) return this;

    // https://storage.googleapis.com/pub-tools-public-publication-data/pdf/35539.pdf
    let f: FST = this;
    for (const g of gs) {
      const A = f.states.length;
      const B = g.states.length;

      // Get all initial edges, augmented
      // with epsilon self-loops at every node
      const fes = f.all_edges_with_loops();
      const ges = g.all_edges_with_loops();

      // Generate all possible matched transitions
      // Source and target states are pairs of f's
      // states and g's states.
      const edges: Edge[] = [];
      for (const fe of fes) {
        for (const ge of ges) {
          if (fe.output !== ge.input) continue;
          const source = fe.source * (B + 1) + ge.source;
          const target = fe.target * (B + 1) + ge.target;
          edges.push(
            new Edge(fe.input, ge.output, source, target)
          );
        }
      }

      // Create states that are accessible
      // via the combined transitions, starting with
      // the combined start state, and assign
      // transitions to them.
      // State numbers are compactified as we go,
      // and we build a map from intermediate combined
      // state numbers to compact state numbers.
      const initial = f.start * (B + 1) + g.start;
      const stateMap = new Map([[initial, 0]]);
      const stack = [initial];
      const visited = new Set([initial]);
      const states: State[] = [];
      while (stack.length > 0) {
        // get the id of the state we need to create
        const n = stack.pop() as number;
        
        // find all edges that exit that state
        const arcs = edges.filter(e => e.source === n);
        
        // determine the new compactified state id,
        // and store the relation for later re-writing.
        const nn = states.length;
        stateMap.set(n, nn);
        
        // create the new state
        states.push(new State(nn, false, arcs));

        // determine which states are reachable from this one
        for (const { target } of arcs) {
          // If we already created the target
          // state, or plan to do so,
          // don't do anything.
          if (visited.has(target)) continue;

          // Otherwise, plan to create the target state.
          visited.add(target);
          stack.push(target);
        }
      }

      // Fix up used edges to have the correct
      // compactified state numbers.
      // We don't iterate over all generated edges
      // because some of them may not be used.
      for (const { n, edges } of states) {
        for (const e of edges) {
          e.source = n;
          e.target = stateMap.get(e.target) as number;
        }
      }

      // Calculate which new states should be accepting states
      for (let i = 0, j = 0; j < A; j++) {
        if (!f.states[j].accepts) i += B;
        else for (let k = 0; k < B; k++, i++) {
          if (g.states[k].accepts) {
            const id = stateMap.get(j * (B + 1) + k);
            if (id) states[id].accepts = true;
          }
        }
      }

      f = new FST(states, 0);
    }

    return f;
  }

  concat(...gs: FST[]) {
    if (gs.length === 0) return this;

    const f = this.clone();
    const { states } = f;
    
    // Cache f's accepting states, because these
    // will be used to link to g's copied states.
    const accepting = f.states.filter(s => s.accepts);

    for (const g of gs) {
      const gstart = g.start;

      // g's start state may end up stranded, if
      // it is not recursively accessible in g.
      // So, before copying it, check if we need to.
      let stranded = false;
      find_gstart: {
        const { states } = g;
        const stack = [gstart];
        const seen = new Set();
        while (stack.length > 0) {
          const { edges } = states[stack.pop() as number];
          for (const { target } of edges) {
            if (target === gstart) break find_gstart;
            if (seen.has(target)) continue;
            seen.add(target);
            stack.push(target);
          }
        }
        stranded = true;
      }

      const offset = states.length;

      // Add the starting transitions of g to the old
      // accepting states of f. We preserve the start
      // state of f and the accepting states of g.
      const transitions = g.states[gstart].edges;
      for (const state of accepting) {
        state.accepts = false;
        const { n, edges } = state;
        for (const { input, output, target } of transitions) {
          edges.push(new Edge(
            input, output, n,
            target + offset - (stranded && target > gstart ? 1 : 0),
          ));
        }
      }

      // Copy g's states into the new FST state list,
      // and kee track of which are accepting, in case
      // we need to concatenate another FST.
      accepting.length = 0;
      for (const { n, accepts, edges } of g.states) {
        if (stranded && n === gstart) continue;
        const idx = n + offset - (stranded && n > gstart ? 1 : 0);
        const s = new State(
          idx, accepts,
          edges.map(e =>
            new Edge(
              e.input, e.output, idx,
              e.target + offset - (stranded && e.target > gstart ? 1 : 0),
            )
          ),
        );
        states.push(s);
        if (accepts) accepting.push(s);
      }
    }

    return f;
  }

  // Produce a simplified FST whose input and output are equal.
  project(side: "input" | "output") {
    const nstates = this.states.map(s => {
      const edges: Edge[] = [];
      const { n } = s;
      for (const e of s.edges) {
        const exists = edges.find(f => f.target === e.target && f.input === e.input);
        if (exists) continue;
        const symbol = e[side];
        edges.push(new Edge(symbol, symbol, n, e.target));
      }
      return new State(s.n, s.accepts, edges);
    });

    return new FST(nstates, this.start);  
  }

  // Output projection
  lower() { return this.project("output"); }
  
  // Input projection
  upper() { return this.project("input"); }

  // Kleene Plus iteration
  // For every non-starting accepting state,
  // add an epsilon transition back to the start.
  // This is equivalent to copying the start
  // state's transitions onto all accepting states.
  plus() {
    if (this.is_plus) return this;
    const fst = this.clone();
    const start_n = fst.start;
    const start_s = fst.states[start_n];
    const start_edges = start_s.edges;
    for (const { n, accepts, edges} of fst.states) {
      if (!accepts || n === start_n) continue;
      // if there is an existing epsilon transition
      // to the start, remove it as redundant.
      const back = edges.findIndex(e =>
        e.target === start_n &&
        e.input === EPSILON &&
        e.output === EPSILON
      );
      if (back > -1) edges.splice(back, 1);

      // Copy edges without duplication
      for (const { input, output, target } of start_edges) {
        if (edges.findIndex(e =>
          e.target === target &&
          e.input === input &&
          e.output === output
        ) > -1) continue;
        edges.push(new Edge(input, output, n, target));
      }
    }

    fst.is_plus = true;
    return fst;
  }

  // Kleene Star iteration
  // For every non-starting accepting state,
  // add an epsilon transition back to the start,
  // and make the start state an accepting state.
  star() {
    if (this.is_plus) {
      if (this.states[this.start].accepts) return this;
      const fst = this.clone();
      fst.is_plus = true;
      fst.states[fst.start].accepts = true;
      return fst;
    }

    const fst = this.plus();
    fst.states[fst.start].accepts = true;

    return fst;
  }

  determinize() {
    if (this.is_determined) return this;

    // Use the powerset construction, treating the FST
    // as an NFA in which i/o pairs are treated as single
    // symbols, and only FST double-epsilons are mapped
    // to NFA epsilons.

    // The other, more common, source of non-determinism
    // is having multiple transitions to different states
    // with the same transition symbols.

    const hash = (s: Set<State>) => [...s]
      .map(({ n }) => n)
      .sort((a, b) => a - b)
      .join(' ');

    const states: State[] = [];
    const init_set = new Set(
      double_epsilon_closure(this.states[this.start], this)
    );

    const seen_sets = new Map([[hash(init_set), 0]]);
    const stack: [Set<State>, number][] = [[init_set, 0]];
    
    let i = 0;
    while (stack.length > 0) {
      // Get a set of states from the stack, find all of its
      // outgoing edges, create new sets from the targets of
      // edges with common labels, and then create a new state
      // with the collected edges of this set.
      const [substates, n] = stack.pop() as [Set<State>, number];

      // Our new state will accept if any of its component states accepted.
      let any_accept = false;

      // This map-of-maps lets us accumulate states that are
      // reached by edges with common input->output labels.
      const paths = new Map<Token,Map<Token,Set<State>>>();

      for (const { edges, accepts } of substates) {
        any_accept = any_accept || accepts;
        for (const { input, output, target } of edges) {
          // Double epsilons are taken care of when calculating closures.
          // These aren't outgoing edges, but rather make their target
          // states already part of the current set.
          if (input === EPSILON && output === EPSILON) continue;

          const m = paths.get(input) ?? new Map<Token,Set<State>>();
          const s = m.get(output) ?? new Set<State>();
          const targets = double_epsilon_closure(this.states[target], this);
          for (const state of targets) s.add(state);
          m.set(output, s);
          paths.set(input, m);
        }
      }

      // Now we look at each of the sets of states that
      // are reachable from the current set, assign them
      // new state numbers if they haven't been seen
      // before, and create edges pointing to them for
      // our new combined state.
      const edges: Edge[] = [];
      for (const [input, m] of paths.entries()) {
        for (const [output, s] of m.entries()) {
          const h = hash(s);
          const t = seen_sets.get(h);
          if (typeof t === 'number') {
            edges.push(new Edge(input, output, n, t));
          } else {
            stack.push([s, i]);
            edges.push(new Edge(input, output, n, i));
            seen_sets.set(h, i);
            i++;
          }
        }
      }

      // Can't use "push" because states may be constructed out-of-order.
      states[n] = new State(n, any_accept, edges);
    }

    const fst = new FST(states, 0);
    fst.is_plus = this.is_plus;
    fst.is_determined = true;
    return fst;
  }

  totalize() {
    if (this.is_total) return this;
    const f = this.clone();
    mutate_total(f);
    f.is_total = true;
    f.is_plus = this.is_plus;

    return f;
  }

  complement() {
    let f: FST = this.is_determined ?
      this.clone() : this.determinize();
    f.is_determined = true;
    
    mutate_total(f);
    f.is_total = true;
    
    for (const s of f.states) {
      s.accepts = !s.accepts;
    }

    return f;
  }
  
  prune() {
    if (this.is_pruned) return this;

    const useful = trace(this);

    if (useful.size === 0) {
      this.states.length = 1;
      this.start = 0;
      const s = this.states[0];
      s.accepts = false;
      s.edges.length = 0;
      return this;
    }
    
    if (useful.size === this.states.length) {
      this.is_pruned = true;
      return this;
    }

    // Preserve only useful states.
    const states: State[] = [];
    for (const s of this.states) {
      const id = useful.get(s.n);
      if (id === void 0) continue;
      s.n = id;
      for (const e of s.edges) {
        e.source = id;
        e.target = useful.get(e.target) as number;
      }
      states[id] = s;
    }
    
    this.states = states;
    this.start = useful.get(this.start) as number;
    this.is_pruned = true;
    return this;
  }

  pruned() {
    if (this.is_pruned) return this;

    const useful = trace(this);

    if (useful.size === 0)
      return new FST([new State(0, false, [])], 0);

    if (useful.size === this.states.length) {
      this.is_pruned = true;
      return this;
    }

    // Preserve only useful states.
    const states: State[] = [];
    for (const { n, edges, accepts } of this.states) {
      const id = useful.get(n);
      if (id === void 0) continue;
      states[id] = new State(id, accepts, edges.map(e => 
        new Edge(e.input, e.output, id, useful.get(e.target) as number)
      ));
    }
    
    const f = new FST(states, useful.get(this.start) as number);
    f.is_pruned = true;
    f.is_plus = this.is_plus;
    f.is_determined = this.is_determined;
    return f;
  }

  minimize() {
    if (this.is_minimal) return this;

    // http://www.cs.um.edu.mt/gordon.pace/Research/Software/Relic/Transformations/FSA/minimise.html

    // The automaton must first be deterministic, total, and
    // have unreachable and useless states removed (except
    // for at most one useless state needed for totality.)
    const f = this.is_determined ?
      this.pruned() : this.determinize().prune();
    mutate_total(f);

    // Construct an nxn matrix D(0) such that the
    // entry D(0)i,j is i_accepts XOR j_accepts.
    const { states } = f;
    const l = states.length;
    const D: boolean[][] = [];
    for (let i = 0; i < l; i++) {
      const row: boolean[] = [];
      D.push(row);
      const sia = states[i].accepts;
      for (let j = 0; j < l; j++) {
        row.push(sia !== states[j].accepts);
      }
    }

    // Given matrix D(k) we can construct matrix D(k+1) as follows:
    //  D(k+1)i,j is TRUE if
    //    1. D(k)i,j was TRUE or
    //    2. there is an input a such that starting from
    //        states i and j with input a takes us to states i', j`
    //        such that D(k)i',j' is TRUE.
    let changed: boolean;
    let count = 0;
    do {
      changed = false;
      for (let i = 0; i < l; i++) {
        const row = D[i];
        const i_edges = states[i].edges;
        row: for (let j = 0; j < l; j++) {
          if (row[j]) continue;
        
          const j_edges = states[j].edges;
          for (const { input: ii, output: io, target: it } of i_edges) {
            for (const { input: ji, output: jo, target: jt } of j_edges) {
              if (ii !== ji || io !== jo) continue;
              if (D[it][jt]) {
                changed = true;
                row[j] = true;
                continue row;
              }
            }
          }
        }
      }
      count++;
    } while (changed);

    if (count === 1) {
      // Nothing changed on the first, and only, iteration.
      f.is_minimal = true;
      return f;
    }

    // We now know that state i is indistinguishable from state j
    // iff Di,j is FALSE; give each state a number corresponding
    // to its equivalence class so we can construct the new states.
    const state_classes = new Array<number|undefined>(l);
    let n = 0;
    for (let i = 0; i < l; i++) {
      const set = state_classes[i] ?? n++;
      state_classes[i] = set;
      const row = D[i];
      for (let j = 0; j < l; j++) {
        if (row[j]) continue;
        state_classes[j] = set;
      }
    }

    if (n === l) {
      // Every state is already distinguishable
      f.is_minimal = true;
      return f;
    }

    // Construct the new combined states, merging
    // transitions and re-indexing as we go.
    const nstates: State[] = Array.from({ length: n },
      (_, i) => new State(i, false, [])
    );
    for (let i = 0; i < l; i++) {
      const id = state_classes[i] as number;
      const ostate = states[i];
      const nstate = nstates[id];
      
      if (ostate.accepts) nstate.accepts = true;

      const { edges } = nstate;
      for (const { input, output, target } of ostate.edges) {
        const ntarget = state_classes[target] as number;
        if (edges.findIndex(e =>
          e.target === ntarget &&
          e.input === input &&
          e.output === output
        )) continue;
        edges.push(new Edge(input, output, id, ntarget));
      }
    }
    
    const fst = new FST(nstates, state_classes[f.start]);
    fst.is_determined = true;
    fst.is_minimal = true;
    fst.is_plus = f.is_plus;
    return fst.prune();
  }

  private execute(
    inprop: "input" | "output",
    outprop: "input" | "output",
  ): Executor {
    const states: [State, string[]][] = [];
    const outputs: string[][] = [];
    extend_outputs(this, this.start, [], outprop, outputs, states);
    return new _Executor(
      inprop, outprop, this, states, outputs,
    );
  }

  generate() { return this.execute("input", "output"); }
  analyze() { return this.execute("output", "input"); }

  recognize(): Recognizer {
    const start = this.states[this.start];
    return new _Recognizer(this, [start], start.accepts);
  }

  toString() {
    return this.start.toString(10) + '\n' + this.states.flatMap(({ edges }) =>
      edges.map(e => `${ e.source } ${ e.target } ${
        typeof e.input === 'string' ? JSON.stringify(e.input) : '`'+e.input.description+'`'
      } ${
        typeof e.output === 'string' ? JSON.stringify(e.output) : '`'+e.output.description+'`'
      }`)
    ).join('\n');
  }

  static union(f: FST, g: FST, ...gs: FST[]) { return f.union(g, ...gs); }
  static intersect(f: FST, g: FST, ...gs: FST[]) { return f.intersect(g, ...gs); }
  static compose(f: FST, g: FST, ...gs: FST[]){ return f.compose(g, ...gs); }
  static concat(f: FST, g: FST, ...gs: FST[]){ return f.concat(g, ...gs); }

  static from_pairs(pairs: Iterable<[Token, Token]>) {
    const states = [];
    let n = 0;
    for (const [i, o] of pairs) {
      if (i === EPSILON && o === EPSILON) continue;
      states.push(new State(n, false, [new Edge(i, o, n, n + 1)]));
      n++;
    }
    states.push(new State(n, true, []));
    const fst = new FST(states, 0);
    fst.is_determined = true;
    return fst;
  }
}
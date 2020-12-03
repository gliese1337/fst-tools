export const EPSILON = Symbol('e');

class Edge {
  constructor(
    public input: string | Symbol,
    public output: string | Symbol,
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
function * epsilon_closure(s: State, fst: _FST, prefix: (string|Symbol)[], outprop: "input" | "output") {
  const pair: [State, (string|Symbol)[]] = [s, prefix];
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

function * double_epsilon_closure(s: State, fst: _FST) {
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
  fst: _FST, target: number, prefix: (string|Symbol)[], outprop: "input" | "output",
  outputs: (string|Symbol)[][],
  states: [State, (string|Symbol)[]][],
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
  next(i: string|Symbol): null | Executor;
}

class Recognizer implements Executor {
  
  constructor(
    private inprop: "input" | "output",
    private outprop: "input" | "output",
    private fst: _FST,
    private states: [State, string[]][],
    public outputs: string[][],
  ) {}

  next(i: string|Symbol) {
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
    return new Recognizer(inprop, outprop, fst, nstates, outputs);
  }
}

export class Acceptor {
  constructor(
    private fst: _FST,
    private states: State[],
  ) {}

  next(i: string|Symbol, o: string|Symbol) {
    const { fst, states } = this;
    const nstates: State[] = [];
    for (const state of states) {
      for (const { input, output, target } of state.edges) {
        if (input !== i || output !== o) continue;
        nstates.push(fst.states[target]);
      }
    }
    if (nstates.length === 0) return null;
    return new Acceptor(fst, nstates);
  }
}

export interface FST {
  clone(): FST;
  union(g: FST): FST;
  compose(g: FST): FST;
  concat(g: FST): FST;
  project(dir: "input" | "output"): FST;
  upper(): FST;
  lower(): FST;
  plus(): FST;
  star(): FST;
  determinize(): FST;
  generate(): Executor;
  analyze(): Executor;
}

class _FST implements FST {
  // https://www.aclweb.org/anthology/C88-2113.pdf
  constructor(public states: State[], public start = 0) {}
  
  clone() {
    const nstates = this.states.map(s => new State(
      s.n, s.accepts, s.edges.map(e => new Edge(e.input, e.output, e.source, e.target)),
    ));
    return new _FST(nstates, this.start);
  }
  
  union(g: _FST) {
    const f = this.clone();
    const l = f.states.length;
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
        f.states.push(new State(n, s.accepts, edges));
      }
    }

    return f;
  }

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

  compose(g: _FST) {
    // https://storage.googleapis.com/pub-tools-public-publication-data/pdf/35539.pdf
    const f = this;
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

    // TODO: Minimize 
    return new _FST(states, 0);
  }

  concat(g: _FST) {
    const fst = this.clone();

    // Step 1: the states from each input FST
    const { states } = fst;
    const accepting = states.filter(s => s.accepts);
    const offset = states.length;
    for (const state of g.states) {
      const idx = state.n + offset
      states.push(new State(
        idx,
        state.accepts,
        state.edges.map(e =>
          new Edge(e.input, e.output, idx, e.target + offset)
        ),
      ));
    }

    // Step 2: add epsilon transitions from the old
    // accepting states of the first FST to the old
    // start state of the second FST. We preserve the
    // start state of the first FST and the accepting
    // states of the second FST.
    // TODO: Collapse states instead of adding epsilons
    const target = g.start + offset;
    for (const state of accepting) {
      state.accepts = false;
      state.edges.push(new Edge(EPSILON, EPSILON, state.n, target));
    }

    // TODO: minimize
    return fst;
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

    // TODO: Minimize
    return new _FST(nstates, this.start);
  
  }

  // Output projection
  lower() { return this.project("output"); }
  
  // Input projection
  upper() { return this.project("input"); }

  // Kleene Plus iteration
  // For every non-starting accepting state,
  // add an epsilon transition back to the start.
  plus() {
    const fst = this.clone();
    const start_n = fst.start;
    const start_s = fst.states[start_n];
    for (const s of fst.states) {
      if (!s.accepts || s === start_s) continue;
      const back = s.edges.find(e =>
        e.target === start_n &&
        e.input === EPSILON &&
        e.output === EPSILON
      );
      // TODO: Collapse states instead of adding epsilons.
      if (!back) s.edges.push(new Edge(EPSILON, EPSILON, s.n, start_n));
    }
    
    // TODO: Minimize
    return fst;
  }

  // Kleene Star iteration
  // For every non-starting accepting state,
  // add an epsilon transition back to the start,
  // and make the start state an accepting state.
  star() {
    const fst = this.plus();
    fst.states[fst.start].accepts = true;

    // TODO: Minimize
    return fst;
  }

  determinize() {
    const states: State[] = [];
    const stack: [Set<State>, number][] = [
      [new Set(double_epsilon_closure(this.states[this.start], this)), 0]
    ];
    let i = 0;
    while (stack.length > 0) {
      const [substates, n] = stack.pop() as [Set<State>, number];
      const paths = new Map<string|Symbol,Map<string|Symbol,Set<State>>>();
      let any = false;
      for (const { edges, accepts } of substates) {
        any = any || accepts;
        for (const { input, output, target } of edges) {
          // double epsilons are taken care of when calculating closures.
          if (input === EPSILON && output === EPSILON) continue;

          const m = paths.get(input) ?? new Map<string|Symbol,Set<State>>();
          const s = m.get(output) ?? new Set<State>();
          const targets = double_epsilon_closure(this.states[target], this);
          for (const state of targets) s.add(state);
          m.set(output, s);
          paths.set(input, m);
        }
      }

      const edges: Edge[] = [];
      for (const [input, m] of paths.entries()) {
        for (const [output, s] of m.entries()) {
          stack.push([s, i]);
          edges.push(new Edge(input, output, n, i));
          i++;
        }
      }

      states[n] = new State(n, any, edges);
    }

    return new _FST(states, 0);
  }

  generate(): Executor {
    const states: [State, string[]][] = [];
    const outputs: string[][] = [];
    extend_outputs(this, this.start, [], "output", outputs, states);
    return new Recognizer(
      "input", "output", this, states, outputs,
    );
  }

  analyze(): Executor {
    const states: [State, string[]][] = [];
    const outputs: string[][] = [];
    extend_outputs(this, this.start, [], "input", outputs, states);
    return new Recognizer(
      "output", "input", this, states, outputs,
    );
  }

  accept(): Acceptor {
    return new Acceptor(this, [this.states[this.start]]);
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
}

export const FST = {
  union(f: FST, g: FST) { return f.union(g); },
  compose(f: FST, g: FST){ return f.compose(g); },
  concat(f: FST, g: FST){ return f.concat(g); },
  from_pairs(pairs: [string | Symbol, string | Symbol][]) {
    const states = pairs.map(([i,o], n) =>
      new State(n, false, [new Edge(i, o, n, n + 1)]));
    states.push(new State(states.length, true, []));
    return new _FST(states, 0);
  }
}
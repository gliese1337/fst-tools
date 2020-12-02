class Edge {
  constructor(
    public input: string,
    public output: string,
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

const EPSILON = "";

// Get all of the states that can be reached through
// epsilon transitions, with their associated outputs.
function * epsilon_closure(s: State, fst: _FST, prefix: string[], outprop: "input" | "output") {
  const pair: [State, string[]] = [s, prefix];
  const stack = [pair];

  yield pair;

  while (stack.length > 0) {
    const [s, out] = stack.pop() as [State, string[]];
    for (const e of s.edges) {
      if (e.input !== EPSILON) continue;
      const edge_output = e[outprop];
      const nout = edge_output === EPSILON ? out : [...out, edge_output]; 
      const next = fst.states[e.target];
      const pair = [next, nout] as [State, string[]];
      yield pair;
      stack.push(pair);
    }
  }
}

function extend_outputs(
  fst: _FST, target: number, prefix: string[], outprop: "input" | "output",
  outputs: string[][],
  states: [State, string[]][],
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
  next(i: string): null | Executor;
}

class Recognizer implements Executor {
  
  constructor(
    private inprop: "input" | "output",
    private outprop: "input" | "output",
    private fst: _FST,
    private states: [State, string[]][],
    public outputs: string[][],
  ) {}

  next(i: string) {
    if (i === EPSILON) return this;

    const { fst, states, inprop, outprop } = this;
    // We cast fst to any in order to access
    // its private fields.
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
  generate(): Executor;
  analyze(): Executor;
}

class _FST implements FST {
  constructor(public states: State[], public start = 0) {}
  
  clone() {
    const nstates = this.states.map(s => new State(
      s.n, s.accepts, s.edges.map(e => new Edge(e.input, e.output, e.source, e.target)),
    ));
    return new _FST(nstates, this.start);
  }

  // cross(g: FST)
  // intersect(g: FST)
  
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

  compose(g: _FST) {
    //https://stackoverflow.com/questions/2649474/how-to-perform-fst-finite-state-transducer-composition
    
    const f = this;
    const A = f.states.length;
    const B = g.states.length;

    // Step 1: Find combined accepting states
    const accepting = new Set<number>();
    
    let i = 0;
    for (let j = 0; j < A; j++) {
      const final = f.states[j].accepts;
      for (let k = 0; k < B; k++, i++) {
        if (final && g.states[k].accepts) accepting.add(i);
      }
    }

    // Step 2: Combine transitions
    const fes = f.states.flatMap(s => s.edges);
    const ges = g.states.flatMap(s => s.edges);
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

    // Step 3: Create states that are accessible
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
      const n = stack.pop() as number;
      const arcs = edges.filter(e => e.source === n);
      const nn = states.length;
      stateMap.set(n, nn);
      states.push(new State(nn, accepting.has(n), arcs));
      for (const { target } of arcs) {
        if (visited.has(target)) continue;
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

    // TODO: Handle Epsilons
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
}

export const FST = {
  union(f: FST, g: FST) { return f.union(g); },
  compose(f: FST, g: FST){ return f.compose(g); },
  concat(f: FST, g: FST){ return f.concat(g); },
  from_pairs(pairs: [string, string][]) {
    const states = pairs.map(([i,o], n) =>
      new State(n, false, [new Edge(i, o, n, n + 1)]));
    states.push(new State(states.length, true, []));
    return new _FST(states, 0);
  }
}
module AI {
  type state = int

  theory EnumerableType {
     type U
     enum: [U]
     complete: |- forall x:U. x in enum
  }
  
  theory TransitionSystem {
    action: EnumerableType
    transitions: (state,action.U) -> [state]
    applicable = (s,a) -> exists x. x in transitions(s,a)
    reachable:_
    reachable = (f:state, path: [action.U], t:state) -> path match {
      [] -> f == t
      a -: as -> exists x. x in transitions(f,a) & reachable(x,as,t)
    }
  }
  theory Deterministic {
    include TransitionSystem
    transition: (state,action.U) -> state?
    transitions = (s,a) -> transition(s,a)
  }

  theory SearchProblem {
    include TransitionSystem
    initials: [state]
    goals:    state -> bool
    solution: [action.U] -> bool = as -> exists i,g. i in initials & reachable(i,as,g) & goals(g)
  }
  theory FullyObservable {
    include SearchProblem
    initial: state
    initials = [initial]
  }
  theory Cost {
    include TransitionSystem
    cost: action.U -> rat
  }
  theory DefaultCost {
    include Cost
    cost = a -> 1
  }

  theory Node {
    label: state
    parent: Node?
  }
  makeNode = (l,p) -> Node {label = l, parent = p}

  theory SearchStrategy {
      type Fringe
      init: [state] -> Fringe
      empty: Fringe -> bool
      insert: Fringe -> (Node,state) -> Fringe
      takeNext: Fringe -> (Fringe,Node)
  }

  DFS = SearchStrategy {
    type Fringe = [Node]
    init = ss -> ss match {
      [] -> []
      h-:t -> makeNode(h,[]) -: init(t)
    }
    empty = l -> l == []
    insert = l -> (p,s) -> makeNode(s, [p]) -: l
    takeNext = l -> l match {
      h -: t -> (t,h)
    }
  }

  treeSearch: (SearchProblem, SearchStrategy) -> Node? = (prob,strat) -> {
    var fringe: strat.Fringe = strat.init(prob.initials)
    while (!strat.empty(fringe)) {
        (fringe, val node) = strat.takeNext(fringe)
        if (prob.goals(node.label)) return [node]
        else
          for (a in prob.action.enum)
            for (s in prob.transitions(node.label, a))
              fringe = strat.insert(fringe)(node, s)
    }
    []
  }
  test = true
}
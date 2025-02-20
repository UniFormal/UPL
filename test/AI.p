module AI {
  type state = int

  theory EnumeratedType {
     type univ
     enum: [univ]
     complete: |- forall x:univ. x in enum
  }
  
  theory TransitionSystem {
    action: EnumeratedType
    transitions: (state,action) -> [state]
    applicable = (s,a) -> exists x. x in transitions(s,a)
    reachable:_
    reachable = (f:state, path: [action], t:state) -> path match {
      [] -> f == t
      a -: as -> exists x. x in transitions(f,a) & reachable(x,as,t)
    }
  }
  theory Deterministic {
    include TransitionSystem
    transition: (state,action) -> state?
    transitions = (s,a) -> transition(s,a)
  }

  theory Cost {
    include TransitionSystem
    cost: action -> rat
  }

  theory DefaultCost {
    include Cost
    cost = a -> 1
  }

  theory SearchProblem {
    include TransitionSystem
    include Cost
    initials: [state]
    goals:    state -> bool
    solution: [action] -> bool = as -> exists i,g. i in initials & reachable(i,as,g) & goals(g)
  }

  theory SimpleSearchProblem {
    include SearchProblem
    include DefaultCost
    include Deterministic
  }

SEARCH = SimpleSearchProblem {
  action = EnumeratedType {type univ = int, enum = [0,1,2], make: int -> univ = x -> x }
  initials = [0]
  goals = x -> x > 5
  transition = (s,a) -> s + (action.enum)
}
  theory FullyObservable {
    include SearchProblem
    initial: state
    initials = [initial]
  }
  
  theory Node {
    label: state
    parent: Node?
    cost: rat
  }

  makeNode = (l,p,c) -> Node {label = l, parent = p, cost = c}

  theory SearchStrategy {
    type Fringe = [Node]
    empty: Fringe -> bool = l -> l == []
    init: [state] -> Fringe
    init = ss -> ss match {
      [] -> []
      h-:t -> makeNode(h,[],0) -: init(t)
    }
    insert: (Fringe,Node) -> Fringe
    takeNext: Fringe -> (Fringe,Node)
  }

  theory TakeFromFrontStrategy {
    include SearchStrategy
    takeNext = l -> l match {
      h -: t -> (t,h)
    }
  }

  DFS = TakeFromFrontStrategy {
    insert = (l,n) -> l :- n
  }

  BFS = TakeFromFrontStrategy {
    insert = (l,n) -> n -: l
  }

  theory TakeByMinimumStrategy {
    include SearchStrategy
    insert = (l,n) -> n -: l
    criterion: Node -> rat
    takeNext = l -> takeNext(l)
  }
  
  UCS = TakeByMinimumStrategy {
    criterion = n -> n.cost
  }

  AStar = (h: state -> rat) -> TakeByMinimumStrategy {
    criterion = n -> n.cost + h(n.label)
  }

  Greedy = (h: state -> rat) -> TakeByMinimumStrategy {
    criterion = n -> h(n.label)
  }

  treeSearch: (SearchProblem, SearchStrategy) -> Node? = (prob,strat) -> {
    var fringe: strat.Fringe = strat.init(prob.initials)
    while (!strat.empty(fringe)) {
        (fringe, val node) = strat.takeNext(fringe)
        if (prob.goals(node.label)) return [node]
        else
          for (a in prob.action.enum)
            for (s in prob.transitions(node.label, a)) {
              val n = makeNode(s, [node], node.cost+prob.cost(a)) 
              fringe = strat.insert(fringe,n)
            }
    }
    []
  }
  test = treeSearch (DFS, SEARCH) == []
}
module AI {
    type state = int
    class TransitionSystem {
      type action
      enumAllActions: [action]
      transitions: (state,action) -> [state]
      applicable = (s,a) -> exists x. x in transitions(s,a)
      reachable:_
      reachable = (f:state, path: [action], t:state) -> path match {
        [] -> f == t
        a -: as -> exists x. x in transitions(f,a) & reachable(x,as,t)
      }
    }
    class Deterministic {
      include TransitionSystem
      transition: (state,action) -> state?
      transitions = (s,a) -> transition(s,a)
    }
    class SearchProblem {
      include TransitionSystem
      initials: [state]
      goals:    state -> bool
      solution: [action] -> bool = as -> exists i,g. i in initials & reachable(i,as,g) & goals(g)
    }
    class FullyObservable {
      include SearchProblem
      initial: state
      initials = [initial]
    }
    class Cost {
      include TransitionSystem
      cost: action -> rat
    }
    class DefaultCost {
      include Cost
      cost = a -> 1
    }

    class Node {
      label: state
      parent: Node?
    }
    makeNode = (l,p) -> Node {label = l, parent = p}

    class SearchStrategy {
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
           for (a in prob.enumAllActions)
             for (s in prob.transitions(node.label, a))
               fringe = strat.insert(fringe)(node, s)
      }
      []
    }
    test = true
}
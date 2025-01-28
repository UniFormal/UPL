module UPL {
  // the language of UPL as a set of inductive types
  theory Syntax {
    // qualified identifiers
    type Path = [string]
    // theories are lists of declarations
    type Decl
    type Theory = [Decl]
    // contexts are lists of variable declarations
    type VarDecl
    type Context = [VarDecl]
    // relative to theory/context, there are types and typed expressions
    type Type
    type Expr

    globalExpr: Path -> Expr
    globalType: Path -> Type
    
    regionalExpr: string -> Expr
    regionalType: string -> Type

    localExpr: string -> Expr
    // localType: string -> Type

    // declarations
    moduleDecl: (string, bool, [Decl]) -> Decl
    exprDecl: (string, Type, Expr?) -> Decl
    typeDecl: (string, Type, Type?) -> Decl
    includeDecl: (Path, Expr?) -> Decl

    vardecl: (string, Type, Expr?) -> VarDecl

    // booleans
    Bool: Type
    boolVal: bool -> Expr

    // numbers
    Int: Type
    intVal: int -> Expr
    Interval: (Expr,Expr) -> Type

    Rat: Type
    ratVal: (int,int) -> Expr

    // strings
    String: Type
    stringVal: string -> Expr

    // other base types    
    Any: Type
    Exn: Type
    Void: Type
    Unit: Type
    unit: Expr

    // dependent products
    Product: Context -> Type
    product: [Expr] -> Expr
    projection: (Expr,int) -> Expr
    
    // dependent functions
    Function: Context -> Type -> Type 
    function: (Context,Expr) -> Expr
    apply: (Expr,[Expr]) -> Expr

    // collections
    type CollKind
    List: CollKind
    Bag: CollKind
    Set: CollKind
    Option: CollKind
    Collection: (Type,CollKind) -> Type
    collectionVal: [Expr] -> Expr

    // expressions over a theory
    ExprOver: (Theory,Type) -> Type
    exprOver: (Theory,Expr) -> Expr
    eval: Expr -> Expr

    // models of a theory
    ModelOf: Theory -> Type
    modelOf: Theory -> Expr
    fieldAccess: (instance: Expr, field: Expr) -> Expr

    // control flow
    declare: VarDecl -> Expr
    assign: (Expr,Expr) -> Expr
    doif: (cond: Expr, then: Expr, elseO: Expr?) -> Expr
    dowhile: (cond: Expr, body: Expr) -> Expr
    dofor: (VarDecl,Expr,Expr) -> Expr
    matchOrCatch: (bool,Expr,[(Expr,Expr)]) -> Expr
    returnOrThrow: (bool,Expr) -> Expr

  }
  
  // (beginnings of) a declarative type system for UPL
  theory Typing {
    include Syntax
    type Region = (Theory,Context)
    type Globe = (Theory,[Region])

    tp: (Globe, Type) -> bool
    expr: (Globe,Expr,Type) -> bool
    
    Int_tp: (g:_) -> |- tp(g,Int)
    intVal_expr: (g:_,i:_) -> |- expr(g, intVal(i), Int)

  }
  
  theory Process {
    type G = Typing{Globe}
    parseTheory: string -> Syntax{Theory}
    parseDecl: string -> Syntax{Decl}
    parseExpr: string -> Syntax{Expr}
    parseType: string -> Syntax{Type}

    checkTheory: (G,Syntax{Theory}) -> Syntax{Theory}
    checkDecl: (G,Syntax{Decl}) -> Syntax{Decl}
    checkExpr: (G,Syntax{Expr}) -> Syntax{Expr}
    checkType: (G,Syntax{Type}) -> Syntax{Type}
  }

  // an API for a hypothetical built-in and unsafe reflection operator
  theory Reflection {
    reflect: any -> Syntax{Expr}
    evaluate: Syntax{Expr} -> any
  }
}
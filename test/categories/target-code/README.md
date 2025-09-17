## target-code directory contains the target code specifying the UPL language extension for monads.
### This README should specify the UPL implementation of monads

### There will be built-in monadic types as well as a mechanism for user-defined monadic types
Built-in: list, set, option

User-defined (examples): state[A,B], writer[A,B]

Built-in monad methods: `fmap`, `return`, `bind` + `do` notation

The mechanism will work with magic methods that substitute behind the hood.

### UPL calls to monadic types/methods are replaced (=>) with other expressions: (?)

```
fmap(mx, f) => monad.type_name.fmap.(mx,f)
return(x)   => monad.type_name.return(x)
bind(mx,f) => mx.bind(f)? => monad.type_name.bind(f)
```

```bind([x,y],f) => [x,y].bind(f)? => monad.list.bind([x,y],f)```

```
do {
x <- mx
y <- my
f <- mz
mw
return(f(x,y))}
=> 
mx.bind(x -> my.bind(y -> mz.bind(f -> mw.bind(_ -> return(f(x,y))
```

### Mechanism for user-defined types: (?)
1. define a new type (only types of kind `* -> *`)
2. make it a monad by defining the methods fmap, return, bind

After defining the three methods the parser automatically knows of a new monad type.
Need to check if type is of kind `* -> *` and the methods have the correct type.
If so, the parser knows the new user-defined monad.
If not, error messages like:

> "defined methods fmap, return, bind on type state[A,B], but state[A,B] not of kind `*->*`."\
"defined method fmap for type counter[B], but monad definitions require three methods: fmap, return, bind"\
"bind definition for type counter[B] has wrong return type"

Example (state monad):

```
type state[A,B] = A -> (A,B)
type counter[B] = state[int,B]
counter[B].fmap: (B -> C) -> counter[B] -> counter[C] = ...
counter[B].return: B -> counter[B] = (x:B -> (s:int -> (s,x)))
counter[B].bind: counter[B] -> (B -> counter[C]) -> counter[C] = ...
```

### Some Questions (?)

How does the mechanism work?\
By a special keyword or defining required methods?\
What about namespaces and scoping?\
What is the order of namespace/scopes the compiler looks for defined values, variables, and methods?\
When does it recognize monadic types and calls to monadic methods?\
If it detects monad method calls it first looks for built-in type definitions and then user-defined definitions,
though user-defined definitions of monadic methods on built-in types should overwrite predefined?
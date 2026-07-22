Author of these ideas and notes: Navid Roux (inspired by Florian Rabe and Annika Schmidt)

# Abstract

There are a number of different foundations used throughout math and formalizations thereof.
We can roughly distinguish between the following three base languages:
hard-typed languages provide a type theory where each term carries its type;
soft-typed languages provide a type theory where terms and types exist independently and a meta-level predicate relating terms and types exists;
untyped languages provide terms only and extensions (e.g., set theories) provide meta-level predicates relating terms with other terms (e.g., the set membership predicate).

Many standard constructions can be carried out in either language:
finite collections, tuples, tuple collections, ...

Formalizing each construction for every base language is a daunting task, resulting in many redundancies in formalizations.
We investigate whether we can formalize the constructions once and for all in one language (namely, over a hard-typed language) and mechanically obtain formalizations for the other base languages.

# Examples

Consider the theories

- `HardTyped = {tp: type, tm: tp -> type, =: {A: tp} tm A -> tm A -> prop}`,
- `SoftTyped = {tp: type, term: type, of: term -> tp -> prop, =: {A: tp} term -> term -> prop}`
- `SetTheory = {include FOL, ∈: set -> set -> prop, =: set -> set -> prop}`

   (where `set` is an alias for the type of individuals from FOL).

## Unit types (one-element sets)

```
// prefixes: H(ardtyped), S(ofttyped), U(ntyped)

theory HUnit : HardTyped = {
    Unit: tp
    unit: tm Unit
    unit_ax: {x: tm Unit} |- x = unit
}
theory SUnit : SoftTyped = {
    Unit: tp
    
    unit: term
    unit_typing: |- unit :: Unit

    unit_ax: {x: term, x*: |- x :: Unit} |- x =_{Unit} unit
}
theory UUnit : SetTheory = {
    Unit: set

    unit: set
    unit_typing: |- unit :: Unit

    unit_ax: {x: set, x*: |- x ∈ Unit} |- x = unit
    unit_ax: unit ∈ Unit
}
```

## Pairs & Products (using inductive types)

Formalizing inductive types the manual way (as was done for the Unit type above) is quite daunting:
type formation, term formation, natural deduction rules, and induction schemes all need to be written manually.
Formal systems like Coq (which is based on CIC) extensively inductive types to get rid of all those boilerplate declarations.

I am not sure how inductive types work for soft-typed or even untyped languages.
But *if* we can get them to work, could we formalize inductively-flavored features (e.g., pairs & products) using an inductive type over a hard-typed language and then apply our translation to the soft- and untyped languages?
That is, do our translations (that we have in mind) carry over to inductive types, too?

```
theory HProd : HardTyped = {
    inductive prod (A: tp, B: tp): tp = {
        pair: tm A -> tm B -> tm (prod A B)
    }
}
theory SProd : SoftTyped = {
    inductive prod (A: tp, B: tp): tp = {
        pair: term -> term -> term
    }
}
theory UProd : SetTheory = {
    inductive prod (A: set, B: set): set = {
        pair: set -> set -> set
    }
}
```

**What is the semantics of the soft-/untyped inductive declarations?**

I guess their semantics is precisely "take the hardtyped inductive declaration, elaborate/flatten it to a list of constants (getting rid of the inductive language feature), apply the [softening translation](https://kwarc.info/people/frabe/Research/RR_soften_21.pdf)".

For example, the semantics of the untyped inductive should be something like

```
prod: {A: set, B: set} set
pair: set -> set -> set
pair*: {x: set, x*: |- x in A} {y: set, y*: |- y in B}   (pair x y) in (prod A B)
pair_injectivity: {x,y,x',y'}   |- pair x y = pair x' y'  -> |- x = x' /\ y  = y'
pair_induction: {A,B: set. P: set -> prop}  ({x,x*,y,y*} |- P (pair x y))  ->  {p: set, p*: |- p in prod A B} |- P p
```

## Representing the Translations from Hard- to Soft- & Untyped Languages (Morphisms & Logical Relations)

We could have these translations:

1. a view `v1: HardTyped -> SoftTyped`: mapping `tp := term`, `tm := [x] term`
2. a view `v2: SoftTyped -> SetTheory`: mapping `tp := set`, `term := set`, `of := [x: set, T: set] x ∈ T`
3. a view `v3: HardTyped -> SetTheory = v1; v2` (defined as the composition of `v1`, `v2`), thus mapping `tp := set`, `tm := [x] set`

These represent the following meta theorems, respectively (obtained by the fact that views preserve typing judgements):

1. `|-_{HardTyped}  t: tm A  ==> |-_{SoftTyped}  v1(t): term`
2. `|-_{SoftTyped}  t: term, A: tp, pf: |~ of t A ==> |-_{SetTheory}  v2(s): set, v2(pf): |~ v2(t) ∈ v2(A)`
3. `|-_{HardTyped}  t: tm A ==> |-_{SetTheory}  v2(t): set`

Observe how the first and third meta theorems are rather unsatisfying: the type annotations `A` are lost!
In contrast, the second meta theorem looks nice: the assertion `|~ of t A` is preserved as `|~ v2(t) ∈ v2(A)`.

To overcome the unsatisfactory nature of the first and third views, we can *complement* them with the following logical relations:

- a logical relation `P: v1: HardTyped -> SoftTyped` partial on `tp`, mapping `tm := [T,x] |~ of x T`
- a logical relation `Q: v1 ; v2: HardTyped -> SetTheory := P ; v2`, i.e. the logical relation `P` post-composed by `v2`

These represent the meta theorems below (obtained by the respective Basic Lemmas):

- `|-_{HardTyped}  t: tm A  ==> |-_{SoftTyped}  P(t): |~ of v1(t) v1(A)`
- `|-_{HardTyped}  t: tm A ==> |-_{SetTheory}  v2(P(t)): |~ v2(v1(t)) ∈ v2(A)`

We can interpret these theorems, respectively, as **type preservation (from hard- to soft-typed)** and **"membership" preservation (when translating types to sets)**.


Unrelated idea: can we state a view `v4: SetTheory -> SoftTyped`?

If so, how about proving a soft-typing judgement `of t A` over `SoftTyped` by

1. translating to `SetTheory` to get `v2(t) ∈ v2(A)`,
2. proving the judgement there, i.e. providing a witness `wit: |~ v2(t) ∈ v2(A)`,
3. and transporting back to `SoftTyped` via `v4` to get`v4(wit): |~ v4(v2(t)) ∈ v4(v2(A))`.

And hopefully, by simplification `v4(v2(X)) = X` for any MMT term `X`.

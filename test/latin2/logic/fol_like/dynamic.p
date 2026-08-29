module dynamic {
    // Dynamic Logic is a Multi-Modal Logic originally introduced by
    // Vaugham Pratt in 1996 for reasoning about imperative programs
    // and later extended to more general uses in linguistics and philosophy.
    // See https://en.wikipedia.org/wiki/Dynamic_logic_(modal_logic) for details.
    
    // Dynamic Logic comes with a very simple non-deterministic programming
    // language Π that only features composition, distribution, iteration, test, and assignment.
    
    // The main idea is to have a modality for every program α and proposition A:prop
    // - ⟬α⟭A means that "if α terminates, then $A$ holds afterwards"
    // - ⦉α⦊A means that "α terminates and $A$ holds afterwards".
    // The possible worlds are "states", i.e. variable assignments for program
    // variables, and a state w:world is accessible from state v:state for program α,
    // if a run of program α in v yields state w.
    
    // Dynamic logic comes in three levels of modeling: 
    // - Proposititional Dynamic Logic: programs are built up from program opaque variables,
    //     states are unspecified, and tests are over propositional formulae.
    // - First-Order Dynamic Logics: program contain (program) variables and assignment,
    //     possible worlds are states, accessibility is state change.
    
    theory Programs {
        type prog
    }

    // Dynamic Logic is just the multimodal logic where the modality is given by Π programs.
    theory DynamicLogic {
        include .multimodal.MML
        realize Programs
        type prog = modality
    }

    // A simple non-deterministic programming language
    theory NonDetProg {
        include .pl.PL
        include Programs

        // the programming language primitives of a non-deterministic programming 
        // language Π whose semantics is easy to specify.
        comp: (prog, prog) -> prog # infix ~
        distrib: (prog, prog) -> prog # infix ∪
        iteration: prog -> prog # prefix *
        test: prop -> prog # postfix ?

        // in Π, we can define the usual program combinators we know and love
        skip: prog = truth ?
        ifte: prop -> prog -> prog -> prog = F -> P -> Q -> ((F ?) ~ P) ∪ (((¬F)?) ~ Q)
        whileDo: prop -> prog -> prog = ???
        until: prop -> prog -> prog = ??? 
    }

    theory PropDynamicLogic {
        include DynamicLogic
        include NonDetProg
    }

    // A theory of (first-order) program variables and for Π; we also extend the language of tests ot sorted first-order logic
    theory TypedDynamicLogic {
        include PropDynamicLogic
        include .sfol.SFOLEQ

        type varDL(s: tp)
        retrieve: (S) -> varDL S -> tm S
        assign: (S) -> varDL S -> tm S -> prog
        random_assign: (S) -> varDL S -> prog
    }

    // A simple example to test what we have done above
    theory Example {
        include TypedDynamicLogic
        include .booleans.TrueFalse
        intDL: tp
        one: tm intDL
        five: tm intDL
        plus: (tm intDL, tm intDL) -> tm intDL # infix +
        test: ???  
    }
}
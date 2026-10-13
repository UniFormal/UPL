# Set theory

Formalizations of typical set_theoretic features as well as set theories like ZFC.

## File Overview

| File | Contents |
|------------|-------------------|
| setfol.mmt | extensionality, subset and other definitions and features that are needed for set_theory. This file is the basis of all formalizations in set theory| 
| finite_sets.mmt | EmptySet, Singleton and UnorderedPair. Every set that consists of exactly x known members |
| lattice_operations.mmt | (Big)Union, (Big)Intersection, Difference and Complement |
| powersets.mmt | Powersets |
| operations.mmt | Filter, Replace, Image, SymmetricDifference, Adjoin and Remove |
| cartesian_product.mmt |  OrderedPairs, CartesianProducts, Sigma and SigmaMod |
| relations.mmt | Relation, Relations, (Partial)Functions and LambdaFunction |
| views_features | views for the features above (except setfol.mmt of cours. |
| pair_definitions | definitions for OrderedPairs. |
| axioms.mmt | Axioms (excluding extensionality and existence). |
| typebase.mmt | Class, Elem and Eq definitions. |
| zfc.mmt | building up zfc from axioms, features and views. Also contains a theory typed_zfc. |
| nats.mmt | natural numbers and Peano axioms. |
| typed_features.mmt| Some LATIN expressions in MMT. This can be ignored. |
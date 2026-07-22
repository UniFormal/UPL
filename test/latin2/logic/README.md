# Logic

Formalizations of propositional logic (PL), first-order logic (FOL), sorted first-order logic, modal logic and many others.

## Naming conventions

### Theory Names

**Prefixes:**

- I: intuitionistic

**Suffixes:**

- NDI: _n_atural _d_eduction rules, _i_ntroduction rules only
- NDE: _n_atural _d_eduction rules, _e_limination rules only
- ND: _n_atural _d_eduction rules (both introduction and elimination rules)
- NDS: _n_atural _d_eduction rules with proof _s_implification rules simplifying proofs employing introduction forms followed directly by elimination forms (e.g., *and introduction* (via proofs `pf1` and `pf2`) followed by *and elimination left* is declared to simplify to just `pf1`.)
- EQ: denotes a logic with equality, e.g. there are theories FOL and FOLEQ, and only in the latter is equality a thing
- EQND: combination of EQ and ND
- EQNDS: combination of EQ and NDS

### Constant Names

**Suffixes:**

- `Il`, `Ir`: introduction rule (possibly left or right variant, e.g., as for *or*)
- `E`,`El`,`Er`: elimination rule (possibly left or right variant, e.g., as for *and*)
- `S`,`Sl`,`Sr`: proof simplification rule (possibly left or right variant, e.g., as for *and*)

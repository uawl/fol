# FOL, a many-sorted first-order logic proof assistant
## Commands
### add_func
Usage: add_func *name* (*arg_sort*, ...) : *result_sort*

Adds a function to the environment.

Example: `add_func add_nat (nat, nat) : nat`
### add_binder
Usage: add_binder *name* *variable_sort* *body_sort* *result_sort*

Adds a binder to the environment.

Example: `add_binder forall set wff wff`
### add_rule
Usage: add_rule *name* \[*meta_function_types*, ...\] *rule_type*

Adds a rule to the environment.

Example: `add_rule imp_intro [phi:wff, psi:wff] ((%phi |- %psi) |- imp(%phi, %psi)`
### prove
Usage: prove *name* \[*meta_function_types*, ...\] *rule_type*

Starts a proof mode, adds a rule when proof is done.

Example: `prove add_comm [x:nat, y:nat] eq(add(x, y), add(y, x))`
## Tactics
### introduce
Usage: introduce

Introduces premises from all goals.
### trivial
Usage: trivial

Closes all goals that is in their premises.
### apply (premise)
Usage: apply *premise_index*

Apply a premise to the first goal.
### apply (rule)
Usage: apply *rule_name* \[*meta_function_name* <- *term*\]

Apply a rule to the first goal, after substituting all meta functions.

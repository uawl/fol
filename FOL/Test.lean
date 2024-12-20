import FOL.Meta

fol_func eq(set, set) : wff

fol_binder \all set, wff : wff

fol_rule ax_eq [x:set] ⊢ eq(?x, ?x)

fol_rule all_intro [φ:set→wff] ([y:set] ⊢ ?φ(?y)) ⊢ (⊢ \all x, ?φ(x))

fol_rule all_elim [φ:set→wff, y:set] (⊢ \all x, ?φ(x)) ⊢ (⊢ ?φ(?y))

fol_prove all_eq ⊢ \all x, eq(x, x) =>
  have all_intro
  specialize 0 [x => eq(x, x)]
  · have ax_eq
    intro
    specialize 1 [?y]
    triv
  · triv

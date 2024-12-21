import FOL.Meta

fol_func true : wff
fol_func false : wff
fol_func imp(wff, wff) : wff
fol_func not(wff) : wff

fol_rule true.intro true

fol_rule false.elim [φ:wff] false ⊢ φ

fol_rule imp.intro [φ:wff, ψ:wff] (φ ⊢ ψ) ⊢ imp(φ, ψ)
fol_rule imp.elim [φ:wff, ψ:wff] imp(φ, ψ) ⊢ φ ⊢ ψ

fol_rule not.intro [φ:wff] imp(φ, false) ⊢ not(φ)
fol_rule not.elim [φ:wff] not(φ) ⊢ φ ⊢ false

fol_prove mt [φ:wff, ψ:wff] imp(ψ, φ) ⊢ imp(not(φ), not(ψ)) =>
  intro
  apply imp.intro [not(φ), not(ψ)]
  intro
  apply not.intro [ψ]
  apply imp.intro [ψ, false]
  intro
  apply not.elim [φ]
  · triv
  · apply imp.elim [ψ, φ]
    · triv
    · triv

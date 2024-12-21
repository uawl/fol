import FOL.Meta

fol_func true : wff
fol_func false : wff
fol_func imp(wff, wff) : wff
fol_func not(wff) : wff
fol_func iff(wff, wff) : wff
fol_func and(wff, wff) : wff
fol_func or(wff, wff) : wff

fol_binder \all set, wff : wff
fol_binder \ex set, wff : wff

fol_rule true.intro true

fol_rule false.elim [φ:wff] false ⊢ φ

fol_rule imp.intro [φ:wff, ψ:wff] (φ ⊢ ψ) ⊢ imp(φ, ψ)
fol_rule imp.elim [φ:wff, ψ:wff] imp(φ, ψ) ⊢ φ ⊢ ψ

fol_rule not.intro [φ:wff] imp(φ, false) ⊢ not(φ)
fol_rule not.elim [φ:wff] not(φ) ⊢ φ ⊢ false

fol_rule iff.intro [φ:wff, ψ:wff] imp(φ, ψ) ⊢ imp(ψ, φ) ⊢ iff(φ, ψ)
fol_rule iff.mp [φ:wff, ψ:wff] iff(φ, ψ) ⊢ imp(φ, ψ)
fol_rule iff.mpr [φ:wff, ψ:wff] iff(φ, ψ) ⊢ imp(ψ, φ)

fol_rule and.intro [φ:wff, ψ:wff] φ ⊢ ψ ⊢ and(φ, ψ)
fol_rule and.left [φ:wff, ψ:wff] and(φ, ψ) ⊢ φ
fol_rule and.right [φ:wff, ψ:wff] and(φ, ψ) ⊢ ψ

fol_rule or.inl [φ:wff, ψ:wff] φ ⊢ or(φ, ψ)
fol_rule or.inr [φ:wff, ψ:wff] ψ ⊢ or(φ, ψ)
fol_rule or.elim [φ:wff, ψ:wff, χ:wff] imp(φ, χ) ⊢ imp(ψ, χ) ⊢ or(φ, ψ) ⊢ χ

fol_rule all.intro [φ:set→wff] ([x:set] ⊢ φ(x)) ⊢ \all y, φ(y)
fol_rule all.elim [φ:set→wff, x:set] \all y, φ(y) ⊢ φ(x)

fol_rule ex.intro [φ:set→wff, x:set] φ(x) ⊢ \ex y, φ(y)
fol_rule ex.elim [φ:set→wff, ψ:wff] \ex y, φ(y) ⊢ \all x, imp(φ(x), ψ) ⊢ ψ

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

fol_prove alim [φ:set→wff, ψ:set→wff] ⊢ imp(\all x, imp(φ(x), ψ(x)), imp(\all x, φ(x), \all x, ψ(x))) =>
  intro
  apply imp.intro [\all x, imp(φ(x), ψ(x)), imp(\all x, φ(x), \all x, ψ(x))]
  intro
  apply imp.intro [\all x, φ(x), \all x, ψ(x)]
  intro
  apply all.intro [λ y => ψ(y)]
  intro
  apply imp.elim [φ(x), ψ(x)]
  · apply all.elim [λ y => imp(φ(y), ψ(y)), x]
    triv
  · apply all.elim [λ y => φ(y), x]
    triv

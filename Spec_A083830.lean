import A083829

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spec_A083830 : énoncé pur auditable (protocole N0, Option B)

Conjecture sur la suite image A083830 (« palindromes de la forme
`3n+1` où `n` est aussi palindrome », compagnon d'A083829) : les
chiffres de `q = 3p+1` n'appartiennent jamais à `{0, 6, 9}`
(alphabet `{1,2,3,4,5,7,8}` - les sept valeurs réalisées dans
les données affichées de la fiche).

Surface minimale : `IsPal`/`dgt` sont réutilisés du module
`A083829` (namespace `A083829`, ouvert ci-dessous) ; zéro
redéfinition, zéro `sorry`, zéro tactique, zéro notation locale.
La fermeture `theorem proven_A083830 : SpecA083830 := ...` vit dans
`Check_Spec_A083830.lean`. L'énoncé recopie la signature du
théorème `A083830_digits`, prouvé dans `A083829.lean`.
-/

open A083829

/-- Énoncé record : les chiffres de `q = 3p+1` sont hors de
`{0,6,9}` (théorème `A083830_digits` du module `A083829`). -/
abbrev SpecA083830 : Prop :=
  ∀ {p m m' : ℕ}, IsPal p m → IsPal (3 * p + 1) m' →
    1 ≤ m → ∀ j < m', dgt (3 * p + 1) j ≠ 0 ∧ dgt (3 * p + 1) j ≠ 6 ∧
      dgt (3 * p + 1) j ≠ 9

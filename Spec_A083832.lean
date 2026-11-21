import A083831

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spec_A083832 : énoncé pur auditable (protocole N0, Option B)

Suite image A083832 (compagnon d'A083831) : pour `p` palindrome tel
que `q = 4p+1` est aussi palindrome, les chiffres de `q`
appartiennent à l'alphabet `{1,2,3,5,6,9}`.

Surface minimale : `IsPal`/`dgt` sont réutilisés du module
`A083831` (namespace `A083831`, ouvert ci-dessous) ; zéro
redéfinition, zéro `sorry`, zéro tactique, zéro notation locale.
La fermeture `theorem proven_A083832 : SpecA083832 := ...` vit dans
`Check_Spec_A083832.lean`. L'énoncé recopie la signature du
théorème `A083832_alphabet` du module `A083832`.
-/

open A083831

/-- Énoncé record : les chiffres de `q = 4p+1` sont dans
`{1,2,3,5,6,9}` (théorème `A083832_alphabet` du module `A083832`). -/
abbrev SpecA083832 : Prop :=
  ∀ {p m m' : ℕ}, IsPal p m → IsPal (4 * p + 1) m' →
    1 ≤ m → ∀ j < m', dgt (4 * p + 1) j = 1 ∨ dgt (4 * p + 1) j = 2 ∨
      dgt (4 * p + 1) j = 3 ∨ dgt (4 * p + 1) j = 5 ∨
      dgt (4 * p + 1) j = 6 ∨ dgt (4 * p + 1) j = 9

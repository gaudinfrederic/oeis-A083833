import A083831

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spec_A083831 : énoncés purs auditables (protocole N0, Option B)

Conjecture de Robert Israel (fiche OEIS A083831, Apr 2018,
« It appears ») sur les palindromes `p` tels que `4p+1` est
aussi palindrome, plus le bonus alphabet prouvé dans le module :

* (E) longueur `m` paire ⟹ tous les chiffres de `p` sont `8`
  (`p = 88...8`, sens unicité de la conjecture Israel : les
  seuls termes de longueur paire sont les repdigits `8...8`) ;
* (D) chaque chiffre de `p` est `≤ 4` ou `= 8` (alphabet
  `{0,1,2,3,4} ∪ {8}`).

Surface minimale : `IsPal`/`dgt` sont réutilisés du module
`A083831` (namespace `A083831`, ouvert ci-dessous) ; zéro
redéfinition, zéro `sorry`, zéro tactique, zéro notation locale.
La fermeture `theorem proven_A083831 : SpecA083831 := ...` vit dans
`Check_Spec_A083831.lean`. Chaque conjoint recopie la signature
du théorème du module (E `A083831_even`, D `A083831_digits`).
Le compagnon `A083832_digits` (suite image) relève du package
A083832, hors périmètre de cette spec.
-/

open A083831

/-- Énoncés record E-D (Israel), en conjonction. -/
abbrev SpecA083831 : Prop :=
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (4 * p + 1) m' →
      1 ≤ m → m % 2 = 0 → ∀ j < m, dgt p j = 8) ∧
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (4 * p + 1) m' →
      1 ≤ m → ∀ j < m, dgt p j ≤ 4 ∨ dgt p j = 8)

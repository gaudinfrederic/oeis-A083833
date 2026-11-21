import A083829

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spec_A083829 : énoncés purs auditables (protocole N0, Option B)

Quatre conjectures de Robert Israel (fiche OEIS A083829, Feb 2023,
« It appears ») sur les palindromes `p` tels que `3p+1` est aussi
palindrome :

* (P1) longueur `m` paire ⟹ tous les chiffres de `p` sont `7`
  (`p = 77...7`, repdigits A002281) ;
* (P2) `m ≥ 2` et `p` non tout-`7` ⟹ le préfixe
  `10·a_{m-1} + a_{m-2}` ∈ `{14,15,16,24,25,26}` ;
* (P3) aucun chiffre de `p` n'est `3`, `8` ou `9` ;
* (P4) un chiffre de `p` égal à `7` ⟹ `p = 77...7`.

Surface minimale : `IsPal`/`dgt` sont réutilisés du module
`A083829` (namespace `A083829`, ouvert ci-dessous) ; zéro
redéfinition, zéro `sorry`, zéro tactique, zéro notation locale.
La fermeture `theorem proven_A083829 : SpecA083829 := ...` vit dans
`Check_Spec_A083829.lean`. Chaque conjoint recopie la signature du
théorème du module (P1 `A083829_even`, P2 `A083829_prefix`,
P3 `A083829_digits`, P4 `A083829_seven`).
-/

open A083829

/-- Énoncés record P1-P4 (Israel), en conjonction. -/
abbrev SpecA083829 : Prop :=
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (3 * p + 1) m' →
      1 ≤ m → m % 2 = 0 → ∀ j < m, dgt p j = 7) ∧
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (3 * p + 1) m' →
      2 ≤ m → (∃ j, j < m ∧ dgt p j ≠ 7) →
      10 * dgt p (m - 1) + dgt p (m - 2) = 14 ∨
      10 * dgt p (m - 1) + dgt p (m - 2) = 15 ∨
      10 * dgt p (m - 1) + dgt p (m - 2) = 16 ∨
      10 * dgt p (m - 1) + dgt p (m - 2) = 24 ∨
      10 * dgt p (m - 1) + dgt p (m - 2) = 25 ∨
      10 * dgt p (m - 1) + dgt p (m - 2) = 26) ∧
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (3 * p + 1) m' →
      1 ≤ m → ∀ j < m, dgt p j ≠ 3 ∧ dgt p j ≠ 8 ∧ dgt p j ≠ 9) ∧
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (3 * p + 1) m' →
      1 ≤ m → (∃ j, j < m ∧ dgt p j = 7) → ∀ j < m, dgt p j = 7)

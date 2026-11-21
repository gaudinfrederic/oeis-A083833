import A069881

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spec_A069881 : énoncés purs auditables (protocole N0, Option B)

Classification Tangente (problème 8154) des palindromes `p` tels
que `2p+1` est aussi palindrome (OEIS A069881) :

* (i) `A069881_even` : longueur `m` paire ⟹ tous les chiffres de
  `p` sont `5` (`p = 55...5`, repdigits `R_d(5)`) : la conjecture
  Tangente ;
* (ii) `A069881_overflow` : dichotomie complète des membres :
  soit `p = 55...5` (cas `m' = m+1`), soit `m` impair, le chiffre
  de tête `a_0 ∈ {1,2,3,4}` et les classes alternées `a_j ≤ 4`
  (`j` pair) / `a_j ≥ 5` (`j` impair) ;
* (iii) `A069881_image_odd` (bonus) : les chiffres de `q = 2p+1`
  aux positions paires sont tous impairs.

Portée : `IsPal p m` classe les palindromes de longueur exacte
`m ≥ 1` (pas de zéro de tête) ; le membre dégénéré `p = 0` est
hors classification (documenté dans le module).

Surface minimale : `IsPal`/`dgt` sont réutilisés du module
`A069881` (namespace `A069881`, ouvert ci-dessous) ; zéro
redéfinition, zéro `sorry`, zéro tactique, zéro notation locale.
La fermeture `theorem proven_A069881 : SpecA069881 := ...` vit dans
`Check_Spec_A069881.lean`.
-/

open A069881

/-- Énoncés record de la classification, en conjonction. -/
abbrev SpecA069881 : Prop :=
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (2 * p + 1) m' →
      1 ≤ m → m % 2 = 0 → ∀ j < m, dgt p j = 5) ∧
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (2 * p + 1) m' →
      1 ≤ m →
      (∀ j < m, dgt p j = 5) ∨
        (Odd m ∧ 1 ≤ dgt p 0 ∧ dgt p 0 ≤ 4 ∧
          (∀ j, j < m → j % 2 = 0 → dgt p j ≤ 4) ∧
          (∀ j, j < m → j % 2 = 1 → 5 ≤ dgt p j))) ∧
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (2 * p + 1) m' →
      1 ≤ m → ∀ j < m', j % 2 = 0 → dgt (2 * p + 1) j % 2 = 1)

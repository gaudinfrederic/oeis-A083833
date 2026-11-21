import A083835

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spec_A083836 : énoncé pur auditable (protocole N0, Option B)

Suite image A083836 (compagnon d'A083835) : les palindromes
`q = 6p+1` avec `p` palindrome. Pas de conjecture sur la fiche ;
l'énoncé record recopie les deux théorèmes compagnons prouvés
dans `A083835.lean` :

* (alphabet) chaque chiffre de `q` est hors de `{0,3,4,6}`
  (i.e. dans `{1,2,5,7,8,9}`) ;
* (forme paire) longueur `m'` paire ⟹ `q = 5 9^{m'-2} 5` :
  chiffres `5` aux deux bords, `9` partout ailleurs.

Surface minimale : `IsPal`/`dgt` sont réutilisés du module
`A083835` (namespace `A083835`, ouvert ci-dessous) ; zéro
redéfinition, zéro `sorry`, zéro tactique, zéro notation locale.
La fermeture `theorem proven_A083836 : SpecA083836 := ...` vit dans
`Check_Spec_A083836.lean`. Chaque conjoint recopie la signature
du théorème du module (alphabet `A083836_digits`, forme paire
`A083836_form`).
-/

open A083835

/-- Énoncé record (suite image), en conjonction. -/
abbrev SpecA083836 : Prop :=
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (6 * p + 1) m' →
      1 ≤ m → ∀ j < m', dgt (6 * p + 1) j ≠ 0 ∧ dgt (6 * p + 1) j ≠ 3 ∧
        dgt (6 * p + 1) j ≠ 4 ∧ dgt (6 * p + 1) j ≠ 6) ∧
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (6 * p + 1) m' →
      1 ≤ m → m' % 2 = 0 →
        (dgt (6 * p + 1) 0 = 5 ∧ dgt (6 * p + 1) (m' - 1) = 5) ∧
          ∀ j, 1 ≤ j → j ≤ m' - 2 → dgt (6 * p + 1) j = 9)

import A083833

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spec_A083833 : énoncés purs auditables (protocole N0, Option B)

Deux conjectures « (Conjectures) » de Michael S. Branicky (fiche
OEIS A083833, Jun 2021) sur les palindromes `p` tels que `5p+1`
est aussi palindrome :

* (C1) chaque chiffre de `p` est `≤ 3` (alphabet `{0,1,2,3}`) ;
* (C2) longueur `m` paire ⟹ tous les chiffres de `p` sont `2`
  (`p = 22...2 = 2^d`, i.e. tout terme commençant par `1` a une
  longueur impaire).

Surface minimale : `IsPal`/`dgt` sont réutilisés du module
`A083833` (namespace `A083833`, ouvert ci-dessous) ; zéro
redéfinition, zéro `sorry`, zéro tactique, zéro notation locale.
La fermeture `theorem proven_A083833 : SpecA083833 := ...` vit dans
`Check_Spec_A083833.lean`. Chaque conjoint recopie la signature du
théorème du module (C1 `A083833_C1`, C2 `A083833_C2`). Les
compagnons `A083834_C1`/`A083834_C2` (suite image) relèvent du
package A083834, hors périmètre de cette spec.
-/

open A083833

/-- Énoncés record C1-C2 (Branicky), en conjonction. -/
abbrev SpecA083833 : Prop :=
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (5 * p + 1) m' →
      1 ≤ m → ∀ j < m, dgt p j ≤ 3) ∧
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (5 * p + 1) m' →
      1 ≤ m → m % 2 = 0 → ∀ j < m, dgt p j = 2)

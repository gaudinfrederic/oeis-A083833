import A083833

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spec_A083834 : énoncés purs auditables (protocole N0, Option B)

Conjectures « (Conjectures) » de Michael S. Branicky (fiche OEIS
A083834, Jun 2021) sur la suite image : les palindromes
`q = 5p+1` avec `p` palindrome (A083833) :

* (C1) chaque chiffre de `q` appartient à `{0,1,5,6}` ;
* (C2) longueur `m'` paire ⟹ tous les chiffres de `q` sont `1`
  (`q = 11...1`, repunit `R_{m'}` : équivalent de « les termes
  commençant par `6` ont tous une longueur impaire »).

Surface minimale : `IsPal`/`dgt` sont réutilisés du module
`A083833` (namespace `A083833`, ouvert ci-dessous) ; zéro
redéfinition, zéro `sorry`, zéro tactique, zéro notation locale.
La fermeture `theorem proven_A083834 : SpecA083834 := ...` vit dans
`Check_Spec_A083834.lean`. Chaque conjoint recopie la signature
du théorème du module (C1 `A083834_C1`, C2 `A083834_C2`), tous
deux prouvés dans `A083833.lean`. Les conjectures C1/C2 sur `p`
lui-même relèvent du package A083833, hors périmètre de cette
spec.
-/

open A083833

/-- Énoncés record C1-C2 (Branicky, suite image), en conjonction. -/
abbrev SpecA083834 : Prop :=
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (5 * p + 1) m' →
      1 ≤ m → ∀ j < m', dgt (5 * p + 1) j = 0 ∨ dgt (5 * p + 1) j = 1 ∨
        dgt (5 * p + 1) j = 5 ∨ dgt (5 * p + 1) j = 6) ∧
  (∀ {p m m' : ℕ}, IsPal p m → IsPal (5 * p + 1) m' →
      1 ≤ m → m' % 2 = 0 → ∀ j < m', dgt (5 * p + 1) j = 1)

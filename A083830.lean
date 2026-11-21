import A083829

import Mathlib

open A083829

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A083830 - palindromes `3p+1` (compagnon d'A083829)

Les resultats sont prouves dans `A083829.lean` (structure `IsPal`,
machinerie `dgt`/`crry`, theoreme `A083830_digits`).
Ce module re-exporte l'enonce dedie : les chiffres de `q = 3p+1`
(palindrome image) sont hors de `{0, 6, 9}`.
-/

theorem A083830_alphabet {p m m' : ℕ} (hp : IsPal p m)
    (hq : IsPal (3 * p + 1) m') (hm : 1 ≤ m) :
    ∀ j < m', dgt (3 * p + 1) j ≠ 0 ∧ dgt (3 * p + 1) j ≠ 6 ∧
      dgt (3 * p + 1) j ≠ 9 :=
  A083830_digits hp hq hm

#print axioms A083830_alphabet

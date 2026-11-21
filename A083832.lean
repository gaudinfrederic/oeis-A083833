import A083831

import Mathlib

open A083831

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A083832 - palindromes `4p+1` (compagnon d'A083831)

Resultats prouves dans `A083831.lean` (theoreme `A083832_digits`).
Re-export : les chiffres de `q = 4p+1` sont dans `{1,2,3,5,6,9}`.
-/

theorem A083832_alphabet {p m m' : ℕ} (hp : IsPal p m)
    (hq : IsPal (4 * p + 1) m') (hm : 1 ≤ m) :
    ∀ j < m', dgt (4 * p + 1) j = 1 ∨ dgt (4 * p + 1) j = 2 ∨
      dgt (4 * p + 1) j = 3 ∨ dgt (4 * p + 1) j = 5 ∨
      dgt (4 * p + 1) j = 6 ∨ dgt (4 * p + 1) j = 9 :=
  A083832_digits hp hq hm

#print axioms A083832_alphabet

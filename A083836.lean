import A083835

import Mathlib

open A083835

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A083836 - palindromes `6p+1` (compagnon d'A083835)

Resultats prouves dans `A083835.lean` (theoremes `A083836_digits`,
`A083836_even`, `A083836_form`). Re-export : les chiffres de
`q = 6p+1` sont hors de `{0,3,4,6}` ; a longueur `m'` paire,
`q = 5 9^{m'-2} 5` (chiffres `5` aux bords, `9` a l'interieur).
-/

theorem A083836_alphabet {p m m' : ℕ} (hp : IsPal p m)
    (hq : IsPal (6 * p + 1) m') (hm : 1 ≤ m) :
    ∀ j < m', dgt (6 * p + 1) j ≠ 0 ∧ dgt (6 * p + 1) j ≠ 3 ∧
      dgt (6 * p + 1) j ≠ 4 ∧ dgt (6 * p + 1) j ≠ 6 :=
  A083836_digits hp hq hm

theorem A083836_evenlen {p m m' : ℕ} (hp : IsPal p m)
    (hq : IsPal (6 * p + 1) m') (hm : 1 ≤ m) (hm'e : m' % 2 = 0) :
    ∀ j < m', dgt (6 * p + 1) j = 5 ∨ dgt (6 * p + 1) j = 9 :=
  A083836_even hp hq hm hm'e

theorem A083836_shape {p m m' : ℕ} (hp : IsPal p m)
    (hq : IsPal (6 * p + 1) m') (hm : 1 ≤ m) (hm'e : m' % 2 = 0) :
    (dgt (6 * p + 1) 0 = 5 ∧ dgt (6 * p + 1) (m' - 1) = 5) ∧
      ∀ j, 1 ≤ j → j ≤ m' - 2 → dgt (6 * p + 1) j = 9 :=
  A083836_form hp hq hm hm'e

#print axioms A083836_alphabet
#print axioms A083836_evenlen
#print axioms A083836_shape

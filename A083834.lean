import A083833

import Mathlib

open A083833

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A083834 - palindromes `5p+1` (compagnon d'A083833)

Resultats prouves dans `A083833.lean` (theoremes `A083834_C1/C2`).
Re-export : chiffres de `q = 5p+1` dans `{0,1,5,6}` ; a longueur
paire, `q` est le repunit `1^{m'}`.
-/

theorem A083834_alphabet {p m m' : ℕ} (hp : IsPal p m)
    (hq : IsPal (5 * p + 1) m') (hm : 1 ≤ m) :
    ∀ j < m', dgt (5 * p + 1) j = 0 ∨ dgt (5 * p + 1) j = 1 ∨
      dgt (5 * p + 1) j = 5 ∨ dgt (5 * p + 1) j = 6 :=
  A083834_C1 hp hq hm

theorem A083834_repunit {p m m' : ℕ} (hp : IsPal p m)
    (hq : IsPal (5 * p + 1) m') (hm : 1 ≤ m) (hm'e : m' % 2 = 0) :
    ∀ j < m', dgt (5 * p + 1) j = 1 :=
  A083834_C2 hp hq hm hm'e

#print axioms A083834_alphabet

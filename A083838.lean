import A083833
import A083837
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A083838 - les zéros affichés de la suite image

`A083838(k) = k·A083837(k)+1` : l'image palindromique associée au plus
petit témoin, `0` là où il n'en existe pas (commentaire Chandler 2003 :
« no palindrome < 10^15 »). Le zéro de l'image est exactement le zéro de
A083837 : `A083838(k) = 0` s'il n'existe aucun couple `(p, q)` de
palindromes avec `q = k·p+1`.

La b-file publiée (66 termes) n'affiche que les 12 premiers zéros
`k = 12, 17, 23, 31, 37, 41, 42, 48, 51, 53, 61, 64` ; le module certifie
les 21 indices de la mission (ceux de A083837), extension incluse.

Chaque `A083838_<k>_zero` est un corollaire direct de
`A083837.no_wit_<k>`.
-/

open A083833

namespace A083838

/-- A083838(12) = 0 : aucun couple `(p, q)` palindromique avec `q = 12p+1`. -/
theorem A083838_12_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 12 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_12 hp hq

/-- A083838(17) = 0 : inexistence universelle. -/
theorem A083838_17_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 17 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_17 hp hq

/-- A083838(23) = 0 : inexistence universelle. -/
theorem A083838_23_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 23 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_23 hp hq

/-- A083838(31) = 0 : inexistence universelle. -/
theorem A083838_31_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 31 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_31 hp hq

/-- A083838(37) = 0 : inexistence universelle. -/
theorem A083838_37_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 37 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_37 hp hq

/-- A083838(41) = 0 : inexistence universelle. -/
theorem A083838_41_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 41 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_41 hp hq

/-- A083838(42) = 0 : inexistence universelle. -/
theorem A083838_42_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 42 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_42 hp hq

/-- A083838(48) = 0 : inexistence universelle. -/
theorem A083838_48_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 48 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_48 hp hq

/-- A083838(51) = 0 : inexistence universelle. -/
theorem A083838_51_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 51 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_51 hp hq

/-- A083838(53) = 0 : inexistence universelle. -/
theorem A083838_53_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 53 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_53 hp hq

/-- A083838(61) = 0 : inexistence universelle. -/
theorem A083838_61_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 61 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_61 hp hq

/-- A083838(64) = 0 : inexistence universelle. -/
theorem A083838_64_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 64 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_64 hp hq

/-- A083838(71) = 0 : inexistence universelle (au-delà de la b-file). -/
theorem A083838_71_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 71 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_71 hp hq

/-- A083838(74) = 0 : inexistence universelle (au-delà de la b-file). -/
theorem A083838_74_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 74 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_74 hp hq

/-- A083838(79) = 0 : inexistence universelle (au-delà de la b-file). -/
theorem A083838_79_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 79 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_79 hp hq

/-- A083838(81) = 0 : inexistence universelle (au-delà de la b-file). -/
theorem A083838_81_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 81 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_81 hp hq

/-- A083838(86) = 0 : inexistence universelle (au-delà de la b-file). -/
theorem A083838_86_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 86 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_86 hp hq

/-- A083838(91) = 0 : inexistence universelle (au-delà de la b-file). -/
theorem A083838_91_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 91 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_91 hp hq

/-- A083838(96) = 0 : inexistence universelle (au-delà de la b-file). -/
theorem A083838_96_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 96 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_96 hp hq

/-- A083838(101) = 0 : inexistence universelle (au-delà de la b-file). -/
theorem A083838_101_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 101 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_101 hp hq

/-- A083838(103) = 0 : inexistence universelle (au-delà de la b-file). -/
theorem A083838_103_zero :
    ¬ ∃ q p m m', IsPal p m ∧ IsPal q m' ∧ q = 103 * p + 1 := by
  rintro ⟨q, p, m, m', hp, hq, rfl⟩
  exact A083837.no_wit_103 hp hq

end A083838

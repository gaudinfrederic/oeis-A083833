import A083835

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_AntiVacuite_A083835 : protocole N3 pour A083835

Trois exigences, toutes kernel-pures (`decide`/`rfl`/`norm_num`) :

1. satisfiabilité des deux branches de la classification par des
   membres réels de la suite : `99` (`6·99+1 = 595`, longueur paire,
   branche `m' = m+1` repdigit `9`) et `121` (`6·121+1 = 727`,
   longueur impaire, branche `m' = m` classes alternées) figurent
   dans les données affichées de la fiche OEIS ;
2. ancrage `rfl`/`decide` sur de petits cas (verrouille les
   conventions `dgt`/`crry`/`IsPal`) ;
3. ablation : les deux bornes de classe sont serrées (`dgt 131 1 = 3`
   réalise le `3`), le chiffre `9` est indispensable à l'énoncé
   complet (`dgt 99 0 = 9`, membre réel hors classes alternées), et
   la classe `{2,3}` est fonctionnelle : `141` (chiffre `4` en
   position impaire) donne `847`, non palindrome.
-/

open A083835

namespace CheckAntiVacA083835

-- N3.1 - Satisfiabilité des deux branches.

/-- Branche `m' = m+1`, `m` pair : `p = 99`, `q = 595` (membre OEIS). -/
theorem sat_even_branch :
    ∃ p m m', IsPal p m ∧ IsPal (6 * p + 1) m' ∧ 1 ≤ m ∧ m % 2 = 0 :=
  ⟨99, 2, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

/-- Branche `m' = m`, `m` impair : `p = 121`, `q = 727` (membre OEIS). -/
theorem sat_odd_branch :
    ∃ p m m', IsPal p m ∧ IsPal (6 * p + 1) m' ∧ 1 ≤ m ∧ m % 2 = 1 :=
  ⟨121, 3, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

-- N3.2 - Ancrage `rfl`/`decide` (conventions du module).

example : dgt 99 0 = 9 := rfl
example : dgt 99 1 = 9 := rfl
example : dgt 121 0 = 1 := by decide
example : dgt 121 1 = 2 := by decide
example : dgt 121 2 = 1 := by decide
example : crry 99 0 = 1 := crry_zero 99
example : crry 99 1 = 5 := by decide
example : crry 99 2 = 5 := by decide
example : crry 121 1 = 0 := by decide
example : crry 121 2 = 1 := by decide
example : dgt (6 * 99 + 1) 0 = 5 := by decide
example : dgt (6 * 99 + 1) 1 = 9 := by decide
example : dgt (6 * 99 + 1) 2 = 5 := by decide
example : dgt (6 * 121 + 1) 0 = 7 := by decide
example : dgt (6 * 121 + 1) 1 = 2 := by decide
example : dgt (6 * 121 + 1) 2 = 7 := by decide

-- N3.3 - Ablation : chaque clause est indispensable / serrée.

/-- Ablation (classe impaire) : la borne `3` est serrée - `p = 131`
(membre OEIS) atteint `dgt 131 1 = 3` en position impaire. -/
theorem ablation_odd_tight : dgt 131 1 = 3 := by decide

/-- Ablation (classe paire) : la borne `1` est serrée - `p = 121`
(membre OEIS) atteint `dgt 121 0 = 1` en position paire. -/
theorem ablation_even_tight : dgt 121 0 = 1 := by decide

/-- Ablation (chiffre `9`) : `p = 99` (membre réel) a `dgt 99 0 = 9` -
hors classes alternées, la branche débordement est indispensable. -/
theorem ablation_nine_needed : dgt 99 0 = 9 := by decide

/-- Ablation (parité de `m`) : `p = 99` (`m = 2` pair) est un terme -
la clause `m % 2 = 1` de la branche `m' = m` est indispensable. -/
theorem ablation_parity_needed : ∃ j < 2, dgt 99 j = 9 :=
  ⟨0, by decide, by decide⟩

/-- Ablation (classe `{2,3}` fonctionnelle) : `p = 141` a `a_1 = 4`
(violation de la classe impaire) et `6·141+1 = 847` n'est pas
palindrome (`q_0 = 7 ≠ 8 = q_2`). -/
theorem ablation_class_load_bearing :
    dgt 141 1 = 4 ∧ dgt (6 * 141 + 1) 0 ≠ dgt (6 * 141 + 1) 2 :=
  ⟨by decide, by decide⟩

end CheckAntiVacA083835

#print axioms CheckAntiVacA083835.sat_even_branch
#print axioms CheckAntiVacA083835.sat_odd_branch
#print axioms CheckAntiVacA083835.ablation_odd_tight
#print axioms CheckAntiVacA083835.ablation_nine_needed
#print axioms CheckAntiVacA083835.ablation_class_load_bearing

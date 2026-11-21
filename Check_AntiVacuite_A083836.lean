import A083835

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_AntiVacuite_A083836 : protocole N3 pour A083836

Trois exigences, toutes kernel-pures (`decide`/`rfl`/`norm_num`) :

1. satisfiabilité des hypothèses conjointes des théorèmes image par
   des membres réels de la suite : `55` (`p = 9`, `m' = 2` paire) et
   `727` (`p = 121`, `m' = 3` impaire) figurent dans les données
   affichées de la fiche OEIS ;
2. ancrage `rfl`/`decide` sur de petits cas ;
3. ablation : l'alphabet `{1,2,5,7,8,9}` est serré (`9` et `5`
   réalisés dans `595`, `2` dans `727`) et la forme paire
   `5 9...9 5` est exacte sur `595`.
-/

open A083835

namespace CheckAntiVacA083836

-- N3.1 - Satisfiabilité des hypothèses conjointes.

/-- Branche `m'` paire : `p = 9`, `q = 55` (membre OEIS). -/
theorem sat_even_branch :
    ∃ p m m', IsPal p m ∧ IsPal (6 * p + 1) m' ∧ 1 ≤ m ∧ m' % 2 = 0 :=
  ⟨9, 1, 2, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

/-- Branche `m'` impaire : `p = 121`, `q = 727` (membre OEIS). -/
theorem sat_odd_branch :
    ∃ p m m', IsPal p m ∧ IsPal (6 * p + 1) m' ∧ 1 ≤ m ∧ m' % 2 = 1 :=
  ⟨121, 3, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

-- N3.2 - Ancrage `rfl`/`decide`.

example : dgt 55 0 = 5 := by decide
example : dgt 55 1 = 5 := by decide
example : dgt 595 1 = 9 := by decide
example : dgt 727 1 = 2 := by decide
example : dgt 787 1 = 8 := by decide

-- N3.3 - Ablation : les clauses sont serrées.

/-- Ablation (alphabet) : le chiffre `9` est réalisé - `q = 595`
(membre OEIS) a `dgt 595 1 = 9`. -/
theorem ablation_alphabet_nine : dgt 595 1 = 9 := by decide

/-- Ablation (alphabet) : le chiffre `5` est réalisé - `q = 595`
a `dgt 595 0 = 5`. -/
theorem ablation_alphabet_five : dgt 595 0 = 5 := by decide

/-- Ablation (alphabet) : le chiffre `2` est réalisé - `q = 727`
a `dgt 727 1 = 2`. -/
theorem ablation_alphabet_two : dgt 727 1 = 2 := by decide

/-- Ablation (forme paire) : `q = 5995` (membre OEIS, `p = 999`,
`m' = 4` paire) vérifie la forme exacte `5 9...9 5` : bords `5`,
intérieur `9`. -/
theorem ablation_shape_exact :
    dgt 5995 0 = 5 ∧ dgt 5995 1 = 9 ∧ dgt 5995 2 = 9 ∧ dgt 5995 3 = 5 :=
  ⟨by decide, by decide, by decide, by decide⟩

end CheckAntiVacA083836

#print axioms CheckAntiVacA083836.sat_even_branch
#print axioms CheckAntiVacA083836.sat_odd_branch
#print axioms CheckAntiVacA083836.ablation_alphabet_nine
#print axioms CheckAntiVacA083836.ablation_shape_exact

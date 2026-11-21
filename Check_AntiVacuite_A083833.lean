import A083833

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_AntiVacuite_A083833 : protocole N3 pour A083833

Trois exigences, toutes kernel-pures (`decide`/`rfl`/`norm_num`) :

1. satisfiabilité des hypothèses conjointes des théorèmes C1-C2
   par des membres réels de la suite : `22` (`5·22+1 = 111`,
   longueur paire, branche `m' = m+1`) et `121` (`5·121+1 = 606`,
   longueur impaire, branche `m' = m`) figurent dans les données
   affichées de la fiche OEIS ;
2. ancrage `rfl`/`decide` sur de petits cas (verrouille les
   conventions `dgt`/`crry`/`IsPal`) ;
3. ablation : la parité de `m` est indispensable à C2
   (`ablation_C2_needs_even`) et la borne `3` de C1 est atteinte
   (`ablation_C1_tight`). Les hypothèses seules ne prouvent pas
   `False` : la satisfiabilité du point 1 est le certificat
   machine de consistance ; la variante tactique (sous
   `intro hp hq hm`, `first | omega | simp_all | aesop`
   n'aboutit pas) est vérifiée à la revue, jamais automatisée.
-/

open A083833

namespace CheckAntiVacA083833

-- N3.1 - Satisfiabilité des hypothèses conjointes.

/-- Branche `m' = m+1`, `m` pair (cas C2) : `p = 22`, `q = 111`
(membre OEIS : `22` est un terme affiché). -/
theorem sat_even_branch :
    ∃ p m m', IsPal p m ∧ IsPal (5 * p + 1) m' ∧ 1 ≤ m ∧ m % 2 = 0 :=
  ⟨22, 2, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

/-- Branche `m' = m`, `m` impair : `p = 121`, `q = 606`
(membre OEIS : `121` est un terme affiché). -/
theorem sat_odd_branch :
    ∃ p m m', IsPal p m ∧ IsPal (5 * p + 1) m' ∧ 1 ≤ m ∧ m % 2 = 1 :=
  ⟨121, 3, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

-- N3.2 - Ancrage `rfl`/`decide` (conventions du module).

example : dgt 22 0 = 2 := rfl
example : dgt 22 1 = 2 := rfl
example : dgt 121 0 = 1 := by decide
example : dgt 121 1 = 2 := by decide
example : dgt 121 2 = 1 := by decide
example : crry 22 0 = 1 := crry_zero 22
example : crry 22 1 = 1 := by decide
example : crry 121 2 = 1 := by decide
example : dgt (5 * 22 + 1) 0 = 1 := by decide
example : dgt (5 * 22 + 1) 2 = 1 := by decide
example : dgt (5 * 121 + 1) 0 = 6 := by decide
example : dgt (5 * 121 + 1) 2 = 6 := by decide

-- N3.3 - Ablation : chaque clause est indispensable / serrée.

/-- Ablation (C2) : la parité de `m` est indispensable - `p = 121`
(`m = 3` impair, `q = 606` palindrome) a un chiffre `≠ 2` ; sans
`m % 2 = 0` l'énoncé C2 serait réfuté par ce membre. -/
theorem ablation_C2_needs_even : ∃ j < 3, dgt 121 j ≠ 2 :=
  ⟨0, by decide, by decide⟩

/-- Ablation (C1) : la borne `3` est serrée - `p = 131` (membre
OEIS) atteint `dgt 131 1 = 3` : l'alphabet `{0,1,2,3}` ne peut
pas être réduit à `{0,1,2}`. -/
theorem ablation_C1_tight : dgt 131 1 = 3 := by decide

end CheckAntiVacA083833

#print axioms CheckAntiVacA083833.sat_even_branch
#print axioms CheckAntiVacA083833.sat_odd_branch
#print axioms CheckAntiVacA083833.ablation_C2_needs_even
#print axioms CheckAntiVacA083833.ablation_C1_tight

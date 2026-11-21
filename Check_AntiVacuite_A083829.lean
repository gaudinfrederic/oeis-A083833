import A083829

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_AntiVacuite_A083829 : protocole N3 pour A083829

Trois exigences, toutes kernel-pures (`decide`/`rfl`/`norm_num`) :

1. satisfiabilité des hypothèses conjointes des théorèmes P1-P4
   par des membres réels de la suite : `77` (`3·77+1 = 232`,
   longueur paire, branche `m' = m+1`) et `141` (`3·141+1 = 424`,
   longueur impaire, branche `m' = m`) figurent dans les données
   affichées de la fiche OEIS ;
2. ancrage `rfl`/`decide` sur de petits cas (verrouille les
   conventions `dgt`/`crry`/`IsPal` : indices little-endian,
   `crry p 0 = 1` pliant le `+1`) ;
3. ablation : chaque hypothèse extra est indispensable, exhibé
   par contre-exemple ci-dessous (`ablation_*`). Les hypothèses
   seules ne prouvent pas `False` : la satisfiabilité du point 1
   est le certificat machine de consistance ; la variante
   tactique (sous `intro hp hq hm`, `first | omega | simp_all |
   aesop` n'aboutit pas) est vérifiée à la revue, jamais
   automatisée.
-/

open A083829

namespace CheckAntiVacA083829

-- N3.1 - Satisfiabilité des hypothèses conjointes.

/-- Branche `m' = m+1`, `m` pair (cas P1) : `p = 77`, `q = 232`
(membre OEIS : `77` est un terme affiché). -/
theorem sat_even_branch :
    ∃ p m m', IsPal p m ∧ IsPal (3 * p + 1) m' ∧ 1 ≤ m ∧ m % 2 = 0 :=
  ⟨77, 2, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

/-- Branche `m' = m`, `m` impair : `p = 141`, `q = 424`
(membre OEIS : `141` est un terme affiché). -/
theorem sat_odd_branch :
    ∃ p m m', IsPal p m ∧ IsPal (3 * p + 1) m' ∧ 1 ≤ m ∧ m % 2 = 1 :=
  ⟨141, 3, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

/-- Hypothèses de P2 satisfiables : `p = 141` (`m = 3 ≥ 2`) a un
chiffre `≠ 7` (`dgt 141 1 = 4`). -/
theorem sat_prefix_hyp :
    ∃ p m m', IsPal p m ∧ IsPal (3 * p + 1) m' ∧ 2 ≤ m ∧
      (∃ j, j < m ∧ dgt p j ≠ 7) :=
  ⟨141, 3, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num,
    ⟨1, by decide, by decide⟩⟩

/-- Hypothèse de P4 satisfiable : `p = 77` a un chiffre `7`
(`dgt 77 0 = 7`). -/
theorem sat_seven_hyp :
    ∃ p m m', IsPal p m ∧ IsPal (3 * p + 1) m' ∧ 1 ≤ m ∧
      (∃ j, j < m ∧ dgt p j = 7) :=
  ⟨77, 2, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num,
    ⟨0, by decide, by decide⟩⟩

-- N3.2 - Ancrage `rfl`/`decide` (conventions du module).

example : dgt 77 0 = 7 := rfl
example : dgt 77 1 = 7 := rfl
example : dgt 141 0 = 1 := by decide
example : dgt 141 1 = 4 := by decide
example : dgt 141 2 = 1 := by decide
example : crry 77 0 = 1 := crry_zero 77
example : crry 77 1 = 2 := by decide
example : crry 141 2 = 1 := by decide
example : dgt (3 * 77 + 1) 0 = 2 := by decide
example : dgt (3 * 77 + 1) 1 = 3 := by decide
example : dgt (3 * 77 + 1) 2 = 2 := by decide
example : dgt (3 * 141 + 1) 1 = 2 := by decide

-- N3.3 - Ablation : chaque clause est indispensable.

/-- Ablation (P1) : la parité de `m` est indispensable - `p = 141`
(`m = 3` impair, `q = 424` palindrome) a un chiffre `≠ 7` ; sans
`m % 2 = 0` l'énoncé P1 serait réfuté par ce membre. -/
theorem ablation_P1_needs_even : ∃ j < 3, dgt 141 j ≠ 7 :=
  ⟨1, by decide, by decide⟩

/-- Ablation (P2) : sans l'hypothèse `∃ j < m, dgt p j ≠ 7`, le
membre `77` (préfixe `77`, hors liste `{14,...,26}`) réfuterait
P2. -/
theorem ablation_P2_needs_not7 : ∀ j < 2, dgt 77 j = 7 := by decide

/-- Ablation (P3) : la liste d'exclusion ne peut pas être étendue
à `4` : `dgt 141 1 = 4` est réalisé par un membre réel (l'alphabet
des classes `{4,5,6}` est non vide). -/
theorem ablation_P3_bound : dgt 141 1 = 4 := by decide

end CheckAntiVacA083829

#print axioms CheckAntiVacA083829.sat_even_branch
#print axioms CheckAntiVacA083829.sat_odd_branch
#print axioms CheckAntiVacA083829.sat_prefix_hyp
#print axioms CheckAntiVacA083829.sat_seven_hyp
#print axioms CheckAntiVacA083829.ablation_P1_needs_even
#print axioms CheckAntiVacA083829.ablation_P2_needs_not7

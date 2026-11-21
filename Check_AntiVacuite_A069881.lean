import A069881

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_AntiVacuite_A069881 : protocole N3 pour A069881

Trois exigences, toutes kernel-pures (`decide`/`rfl`/`norm_num`) :

1. satisfiabilité des hypothèses conjointes de la classification
   par des membres réels de la suite : `55` (`2·55+1 = 111`,
   longueur paire, branche `m' = m+1`, repdigit `R_2(5)`) et
   `151` (`2·151+1 = 303`, longueur impaire, branche `m' = m`,
   réalise le second disjonct de la dichotomie) figurent dans les
   données affichées de la fiche OEIS ;
2. ancrage `rfl`/`decide` sur de petits cas (verrouille les
   conventions `dgt`/`crry`/`IsPal`), dont l'appartenance
   effective de `151` au disjonct « classes alternées » ;
3. ablation : la parité de `m` est indispensable à
   `A069881_even` (`ablation_even_needs_parity`) ; les hypothèses
   seules ne prouvent pas `False` : la satisfiabilité du point 1
   est le certificat machine de consistance ; la variante
   tactique (sous `intro hp hq hm`, `first | omega | simp_all |
   aesop` n'aboutit pas) est vérifiée à la revue, jamais
   automatisée.
-/

open A069881

namespace CheckAntiVacA069881

-- N3.1 - Satisfiabilité des hypothèses conjointes.

/-- Branche `m' = m+1`, `m` pair (cas Tangente) : `p = 55`,
`q = 111` (membre OEIS : `55` est un terme affiché, repdigit
`R_2(5)`). -/
theorem sat_even_branch :
    ∃ p m m', IsPal p m ∧ IsPal (2 * p + 1) m' ∧ 1 ≤ m ∧ m % 2 = 0 :=
  ⟨55, 2, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

/-- Branche `m' = m`, `m` impair : `p = 151`, `q = 303`
(membre OEIS : `151` est un terme affiché). -/
theorem sat_odd_branch :
    ∃ p m m', IsPal p m ∧ IsPal (2 * p + 1) m' ∧ 1 ≤ m ∧ m % 2 = 1 :=
  ⟨151, 3, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

-- N3.2 - Ancrage `rfl`/`decide` (conventions du module).

example : dgt 55 0 = 5 := rfl
example : dgt 55 1 = 5 := rfl
example : dgt 151 0 = 1 := by decide
example : dgt 151 1 = 5 := by decide
example : dgt 151 2 = 1 := by decide
example : crry 55 0 = 1 := crry_zero 55
example : crry 55 1 = 1 := by decide
example : crry 151 2 = 1 := by decide
example : dgt (2 * 55 + 1) 0 = 1 := by decide
example : dgt (2 * 55 + 1) 2 = 1 := by decide
example : dgt (2 * 151 + 1) 0 = 3 := by decide
example : dgt (2 * 151 + 1) 2 = 3 := by decide

/-- Le repdigit `55` réalise le premier disjonct de la
dichotomie : tous ses chiffres sont `5`. -/
theorem anchor_repdigit : ∀ j < 2, dgt 55 j = 5 := by decide

/-- `151` réalise le second disjonct (branche `m' = m`) : `m = 3`
impair, chiffre de tête `1 ∈ [1,4]`, `≤ 4` aux positions paires
(`j = 0, 2`), `≥ 5` aux positions impaires (`j = 1`). -/
theorem anchor_odd_class :
    Odd 3 ∧ 1 ≤ dgt 151 0 ∧ dgt 151 0 ≤ 4 ∧
      (∀ j, j < 3 → j % 2 = 0 → dgt 151 j ≤ 4) ∧
      (∀ j, j < 3 → j % 2 = 1 → 5 ≤ dgt 151 j) :=
  ⟨⟨1, rfl⟩, by decide, by decide, by decide, by decide⟩

-- N3.3 - Ablation : la parité est indispensable.

/-- Ablation : sans `m % 2 = 0`, le membre `151` (`m = 3` impair,
`q = 303` palindrome) a des chiffres `≠ 5` ; la conclusion « tout
`5` » serait réfutée. -/
theorem ablation_even_needs_parity : ∃ j < 3, dgt 151 j ≠ 5 :=
  ⟨0, by decide, by decide⟩

end CheckAntiVacA069881

#print axioms CheckAntiVacA069881.sat_even_branch
#print axioms CheckAntiVacA069881.sat_odd_branch
#print axioms CheckAntiVacA069881.anchor_repdigit
#print axioms CheckAntiVacA069881.anchor_odd_class
#print axioms CheckAntiVacA069881.ablation_even_needs_parity

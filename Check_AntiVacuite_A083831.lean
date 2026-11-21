import A083831

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_AntiVacuite_A083831 : protocole N3 pour A083831

Trois exigences, toutes kernel-pures (`decide`/`rfl`/`norm_num`) :

1. satisfiabilité des hypothèses conjointes des théorèmes
   `A083831_even`/`A083831_digits` par des membres réels de la
   suite : `p = 88` donne `q = 4·88+1 = 353` (longueur paire,
   branche `m' = m+1`, repdigit `R_2(8)`) et `p = 131` donne
   `q = 525` (longueur impaire, branche `m' = m`) ; `88` et
   `131` figurent dans les données affichées d'A083831, `353`
   et `525` dans celles d'A083832 ;
2. ancrage `rfl`/`decide` sur de petits cas (verrouille les
   conventions `dgt`/`crry`/`IsPal` : indices little-endian,
   `crry p 0 = 1` pliant le `+1`, `crry p j = 3` en branche
   successeur, `crry p 1 = 0` en branche même-longueur) ;
3. ablation : la parité de `m` est indispensable à
   `A083831_even` (`ablation_even_needs_parity`) et le disjonct
   `= 8` de `A083831_digits` est indispensable
   (`ablation_digits_needs8`), la borne `4` étant atteinte par
   un terme réel (`ablation_digits_tight`). Les hypothèses
   seules ne prouvent pas `False` : la satisfiabilité du point 1
   est le certificat machine de consistance ; la variante
   tactique (sous `intro hp hq hm`, `first | omega | simp_all |
   aesop` n'aboutit pas) est vérifiée à la revue, jamais
   automatisée.
-/

open A083831

namespace CheckAntiVacA083831

-- N3.1 - Satisfiabilité des hypothèses conjointes.

/-- Branche `m' = m+1`, `m` pair (cas E) : `p = 88`, `q = 353`
(membres OEIS : `88` terme d'A083831, `353` terme d'A083832). -/
theorem sat_even_branch :
    ∃ p m m', IsPal p m ∧ IsPal (4 * p + 1) m' ∧ 1 ≤ m ∧ m % 2 = 0 :=
  ⟨88, 2, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

/-- Branche `m' = m`, `m` impair : `p = 131`, `q = 525`
(membres OEIS : `131` terme d'A083831, `525` terme d'A083832). -/
theorem sat_odd_branch :
    ∃ p m m', IsPal p m ∧ IsPal (4 * p + 1) m' ∧ 1 ≤ m ∧ m % 2 = 1 :=
  ⟨131, 3, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

-- N3.2 - Ancrage `rfl`/`decide` (conventions du module).

example : dgt 88 0 = 8 := rfl
example : dgt 88 1 = 8 := rfl
example : dgt 131 0 = 1 := by decide
example : dgt 131 1 = 3 := by decide
example : dgt 131 2 = 1 := by decide
example : crry 88 0 = 1 := crry_zero 88
example : crry 88 1 = 3 := by decide
example : crry 131 1 = 0 := by decide
example : dgt (4 * 88 + 1) 0 = 3 := by decide
example : dgt (4 * 88 + 1) 1 = 5 := by decide
example : dgt (4 * 88 + 1) 2 = 3 := by decide
example : dgt (4 * 131 + 1) 1 = 2 := by decide

-- N3.3 - Ablation : chaque clause est indispensable / serrée.

/-- Ablation (E) : la parité de `m` est indispensable - `p = 131`
(`m = 3` impair, `q = 525` palindrome) a un chiffre `≠ 8` ; sans
`m % 2 = 0` l'énoncé E serait réfuté par ce membre. -/
theorem ablation_even_needs_parity : ∃ j < 3, dgt 131 j ≠ 8 :=
  ⟨1, by decide, by decide⟩

/-- Ablation (D) : le disjonct `dgt p j = 8` est indispensable -
le membre `88` a un chiffre `> 4` ; réduire la conclusion à
`dgt p j ≤ 4` serait réfuté par ce membre. -/
theorem ablation_digits_needs8 : ∃ j < 2, 4 < dgt 88 j :=
  ⟨0, by decide, by decide⟩

/-- Ablation (D) : la borne `4` est serrée - `p = 242` (membre
OEIS, `4·242+1 = 969` palindrome) atteint `dgt 242 1 = 4` :
l'alphabet `{0,...,4} ∪ {8}` ne peut pas être réduit à
`{0,...,3} ∪ {8}`. -/
theorem ablation_digits_tight : dgt 242 1 = 4 := by decide

end CheckAntiVacA083831

#print axioms CheckAntiVacA083831.sat_even_branch
#print axioms CheckAntiVacA083831.sat_odd_branch
#print axioms CheckAntiVacA083831.ablation_even_needs_parity
#print axioms CheckAntiVacA083831.ablation_digits_needs8
#print axioms CheckAntiVacA083831.ablation_digits_tight

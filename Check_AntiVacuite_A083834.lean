import A083833

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_AntiVacuite_A083834 : protocole N3 pour A083834

Trois exigences, toutes kernel-pures (`decide`/`rfl`/`norm_num`) :

1. satisfiabilité des hypothèses conjointes des théorèmes
   `A083834_C1`/`A083834_C2` par des membres réels des suites :
   `p = 121` donne `q = 5·121+1 = 606` (branche `m' = m`,
   `m'` impair) et `p = 222` donne `q = 5·222+1 = 1111`
   (branche `m' = m+1`, `m'` pair, repunit `R_4`) ; `121` et
   `222` figurent dans les données affichées d'A083833, `606`
   et `1111` dans celles d'A083834 ;
2. ancrage `rfl`/`decide` sur de petits cas (verrouille les
   conventions `dgt`/`crry`/`IsPal` : indices little-endian,
   `crry p 0 = 1` pliant le `+1`, `crry p j = 1` en branche
   successeur, `crry p 1 = 0` en branche même-longueur) ;
3. ablation : la parité de `m'` est indispensable à
   `A083834_C2` (`ablation_C2_needs_even`) et l'alphabet
   `{0,1,5,6}` de `A083834_C1` est serré
   (`ablation_C1_tight` : `0` et `5` réalisés par des termes
   affichés). Les hypothèses seules ne prouvent pas `False` :
   la satisfiabilité du point 1 est le certificat machine de
   consistance ; la variante tactique (sous `intro hp hq hm`,
   `first | omega | simp_all | aesop` n'aboutit pas) est
   vérifiée à la revue, jamais automatisée.
-/

open A083833

namespace CheckAntiVacA083834

-- N3.1 - Satisfiabilité des hypothèses conjointes.

/-- Branche `m' = m` (`m'` impair) : `p = 121`, `q = 606`
(membres OEIS : `121` terme d'A083833, `606` terme d'A083834). -/
theorem sat_odd_branch :
    ∃ p m m', IsPal p m ∧ IsPal (5 * p + 1) m' ∧ 1 ≤ m ∧ m' % 2 = 1 :=
  ⟨121, 3, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

/-- Branche `m' = m+1`, `m'` pair (cas C2) : `p = 222`,
`q = 1111` repunit (membres OEIS : `222` terme d'A083833,
`1111` terme d'A083834). -/
theorem sat_even_branch :
    ∃ p m m', IsPal p m ∧ IsPal (5 * p + 1) m' ∧ 1 ≤ m ∧ m' % 2 = 0 :=
  ⟨222, 3, 4, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

-- N3.2 - Ancrage `rfl`/`decide` (conventions du module).

example : dgt 222 0 = 2 := rfl
example : dgt 222 2 = 2 := by decide
example : dgt 121 0 = 1 := by decide
example : dgt 121 1 = 2 := by decide
example : dgt 121 2 = 1 := by decide
example : crry 222 0 = 1 := crry_zero 222
example : crry 222 1 = 1 := by decide
example : crry 121 1 = 0 := by decide
example : dgt (5 * 222 + 1) 0 = 1 := by decide
example : dgt (5 * 222 + 1) 3 = 1 := by decide
example : dgt (5 * 121 + 1) 0 = 6 := by decide
example : dgt (5 * 121 + 1) 1 = 0 := by decide
example : dgt (5 * 121 + 1) 2 = 6 := by decide
example : dgt (5 * 131 + 1) 1 = 5 := by decide

-- N3.3 - Ablation : chaque clause est indispensable / serrée.

/-- Ablation (C2) : la parité de `m'` est indispensable -
`q = 606` (`p = 121`, `m' = 3` impair, terme affiché d'A083834)
a un chiffre `≠ 1` ; sans `m' % 2 = 0` l'énoncé C2 serait
réfuté par ce membre. -/
theorem ablation_C2_needs_even : ∃ j < 3, dgt (5 * 121 + 1) j ≠ 1 :=
  ⟨0, by decide, by decide⟩

/-- Ablation (C1) : l'alphabet `{0,1,5,6}` est serré - `0` et `5`
sont réalisés par des termes affichés (`q = 606` depuis `p = 121`,
`q = 656` depuis `p = 131`, tous deux dans les données d'A083834) ;
aucun des quatre chiffres ne peut être retiré. -/
theorem ablation_C1_tight :
    dgt (5 * 121 + 1) 1 = 0 ∧ dgt (5 * 131 + 1) 1 = 5 :=
  ⟨by decide, by decide⟩

end CheckAntiVacA083834

#print axioms CheckAntiVacA083834.sat_even_branch
#print axioms CheckAntiVacA083834.sat_odd_branch
#print axioms CheckAntiVacA083834.ablation_C2_needs_even
#print axioms CheckAntiVacA083834.ablation_C1_tight

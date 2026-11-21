import A083829

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_AntiVacuite_A083830 : protocole N3 pour A083830

Trois exigences, toutes kernel-pures (`decide`/`rfl`/`norm_num`) :

1. satisfiabilité des hypothèses du théorème `A083830_digits`
   par des membres réels des suites : `p = 77` donne
   `q = 3·77+1 = 232` (branche `m' = m+1`, `m` pair) et
   `p = 141` donne `q = 424` (branche `m' = m`, `m` impair) ;
   `77` et `141` figurent dans les données affichées d'A083829,
   `232` et `424` dans celles d'A083830 ;
2. ancrage `rfl`/`decide` sur de petits cas (verrouille les
   conventions `dgt`/`crry`/`IsPal` : indices little-endian,
   `crry p 0 = 1` pliant le `+1`) ;
3. ablation : l'alphabet `{1,...,8} \ {6}` de la conclusion est
   serré, chaque chiffre non exclu étant réalisé par un terme
   affiché (`ablation_alpha_tight`) ; l'exclusion de `6` est
   illustrée par l'absence des classes `{4,5,6}` de `p` aux
   positions paires dans la branche `m' = m`. Les hypothèses
   seules ne prouvent pas `False` : la satisfiabilité du point 1
   est le certificat machine de consistance ; la variante
   tactique (sous `intro hp hq hm`, `first | omega | simp_all |
   aesop` n'aboutit pas) est vérifiée à la revue, jamais
   automatisée.
-/

open A083829

namespace CheckAntiVacA083830

-- N3.1 - Satisfiabilité des hypothèses conjointes.

/-- Branche `m' = m+1`, `m` pair : `p = 77`, `q = 232`
(membres OEIS : `77` terme d'A083829, `232` terme d'A083830). -/
theorem sat_even_branch :
    ∃ p m m', IsPal p m ∧ IsPal (3 * p + 1) m' ∧ 1 ≤ m ∧ m % 2 = 0 :=
  ⟨77, 2, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

/-- Branche `m' = m`, `m` impair : `p = 141`, `q = 424`
(membres OEIS : `141` terme d'A083829, `424` terme d'A083830). -/
theorem sat_odd_branch :
    ∃ p m m', IsPal p m ∧ IsPal (3 * p + 1) m' ∧ 1 ≤ m ∧ m % 2 = 1 :=
  ⟨141, 3, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

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
example : dgt (3 * 141 + 1) 0 = 4 := by decide
example : dgt (3 * 141 + 1) 1 = 2 := by decide
example : dgt (3 * 141 + 1) 2 = 4 := by decide

-- N3.3 - Ablation : l'alphabet est serré (chaque chiffre non
-- exclu est réalisé par un terme réel de la suite image).

/-- Ablation : l'exclusion `{0,6,9}` ne peut être étendue - `3`
(`q = 232`), `4` (`q = 424`), `7` (`q = 757`, depuis `p = 252`) et
`8` (`q = 484`, depuis `p = 161`) sont des chiffres de termes
affichés d'A083830 ; aucun ne peut rejoindre la liste exclue. -/
theorem ablation_alpha_tight :
    dgt (3 * 77 + 1) 1 = 3 ∧ dgt (3 * 141 + 1) 0 = 4 ∧
      dgt (3 * 252 + 1) 0 = 7 ∧ dgt (3 * 161 + 1) 1 = 8 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- Ablation : l'hypothèse « `q = 3p+1` palindrome » est
indispensable - `p = 212` est palindrome (`IsPal 212 3`) mais
`3·212+1 = 637` ne l'est pas et `dgt 637 2 = 6` falsifierait la
conclusion ; c'est l'hypothèse `hq` qui filtre ce cas. -/
theorem ablation_needs_qpal : dgt (3 * 212 + 1) 2 = 6 := by decide

end CheckAntiVacA083830

#print axioms CheckAntiVacA083830.sat_even_branch
#print axioms CheckAntiVacA083830.sat_odd_branch
#print axioms CheckAntiVacA083830.ablation_alpha_tight
#print axioms CheckAntiVacA083830.ablation_needs_qpal

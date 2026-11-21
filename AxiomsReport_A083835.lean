import A083835
import A083836
import Spec_A083835
import Spec_A083836
import Check_Spec_A083835
import Check_Spec_A083836
import Check_AntiVacuite_A083835
import Check_AntiVacuite_A083836

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AxiomsReport_A083835 : couverture exhaustive des axiomes

Perimetre cible A083835 + A083836 (8 modules) : le module principal
`A083835` (auto-contenu, `import Mathlib`), le re-export `A083836`,
`Spec_A083835`, `Check_Spec_A083835`, `Spec_A083836`,
`Check_Spec_A083836`, `Check_AntiVacuite_A083835`,
`Check_AntiVacuite_A083836`. Le module `A083835` declare aussi les
theoremes compagnons `A083836_*` (cible A083836).
Attendu partout : [propext, Classical.choice, Quot.sound].
-/

-- A083835 (32 decls, namespace A083835)
#print axioms A083835.dgt
#print axioms A083835.IsPal
#print axioms A083835.crry
#print axioms A083835.crry_zero
#print axioms A083835.crry_le
#print axioms A083835.decomp
#print axioms A083835.div_ten_pow
#print axioms A083835.qdgt
#print axioms A083835.crry_succ
#print axioms A083835.dgt_eq_zero_of_ge
#print axioms A083835.mp_cases
#print axioms A083835.crry_m_eq_zero_iff
#print axioms A083835.crry_sym_same
#print axioms A083835.crry_mirror
#print axioms A083835.qdgt_sym_succ
#print axioms A083835.carry_period_same
#print axioms A083835.carry_even_same
#print axioms A083835.carry_odd_same
#print axioms A083835.same_case_odd_a0
#print axioms A083835.same_case_digits
#print axioms A083835.same_case_c1
#print axioms A083835.succ_case_a0
#print axioms A083835.succ_case_chain
#print axioms A083835.succ_case_all9
#print axioms A083835.succ_case_carry
#print axioms A083835.A083835_even
#print axioms A083835.A083835_digits
#print axioms A083835.all9_gives_pal
#print axioms A083835.alt_gives_pal
#print axioms A083835.A083835
#print axioms A083835.A083836_digits
#print axioms A083835.A083836_even
#print axioms A083835.A083836_form

-- A083836 (3 decls, re-export racine)
#print axioms A083836_alphabet
#print axioms A083836_evenlen
#print axioms A083836_shape

-- Spec (2 decls)
#print axioms SpecA083835
#print axioms SpecA083836

-- Check_Spec (2 decls)
#print axioms proven_A083835
#print axioms proven_A083836

-- Check_AntiVacuite_A083835 (7 decls, namespace CheckAntiVacA083835)
#print axioms CheckAntiVacA083835.sat_even_branch
#print axioms CheckAntiVacA083835.sat_odd_branch
#print axioms CheckAntiVacA083835.ablation_odd_tight
#print axioms CheckAntiVacA083835.ablation_even_tight
#print axioms CheckAntiVacA083835.ablation_nine_needed
#print axioms CheckAntiVacA083835.ablation_parity_needed
#print axioms CheckAntiVacA083835.ablation_class_load_bearing

-- Check_AntiVacuite_A083836 (6 decls, namespace CheckAntiVacA083836)
#print axioms CheckAntiVacA083836.sat_even_branch
#print axioms CheckAntiVacA083836.sat_odd_branch
#print axioms CheckAntiVacA083836.ablation_alphabet_nine
#print axioms CheckAntiVacA083836.ablation_alphabet_five
#print axioms CheckAntiVacA083836.ablation_alphabet_two
#print axioms CheckAntiVacA083836.ablation_shape_exact

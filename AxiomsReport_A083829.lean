import A083829
import Spec_A083829
import Check_Spec_A083829
import Check_AntiVacuite_A083829

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AxiomsReport_A083829 : couverture exhaustive des axiomes

Perimetre cible A083829 (4 modules) : le module
principal `A083829` (auto-contenu, `import Mathlib`) +
`Spec_A083829` + `Check_Spec_A083829` +
`Check_AntiVacuite_A083829`. Le module `A083829`
declare aussi le theoreme compagnon `A083830_digits`
(cible A083830).
40 declarations auditees ci-dessous.
Attendu partout : [propext, Classical.choice, Quot.sound].
-/

-- A083829 (31 decls, namespace A083829)
#print axioms A083829.dgt
#print axioms A083829.IsPal
#print axioms A083829.crry
#print axioms A083829.crry_zero
#print axioms A083829.crry_le
#print axioms A083829.decomp
#print axioms A083829.div_ten_pow
#print axioms A083829.qdgt
#print axioms A083829.crry_succ
#print axioms A083829.dgt_eq_zero_of_ge
#print axioms A083829.mp_cases
#print axioms A083829.crry_m_eq_zero_iff
#print axioms A083829.crry_sym_same
#print axioms A083829.crry_mirror
#print axioms A083829.qdgt_sym_succ
#print axioms A083829.top_two_eq
#print axioms A083829.carry_period_same
#print axioms A083829.carry_even_same
#print axioms A083829.carry_odd_same
#print axioms A083829.same_case_odd_a0
#print axioms A083829.same_case_digits
#print axioms A083829.succ_case_a0
#print axioms A083829.succ_case_chain
#print axioms A083829.succ_case_all7
#print axioms A083829.succ_case_carry
#print axioms A083829.same_case_c1
#print axioms A083829.A083829_even
#print axioms A083829.A083829_digits
#print axioms A083829.A083829_seven
#print axioms A083829.A083829_prefix
#print axioms A083829.A083830_digits

-- Spec_A083829 (1 decl)
#print axioms SpecA083829

-- Check_Spec_A083829 (1 decl)
#print axioms proven_A083829

-- Check_AntiVacuite_A083829 (7 decls, namespace CheckAntiVacA083829)
#print axioms CheckAntiVacA083829.sat_even_branch
#print axioms CheckAntiVacA083829.sat_odd_branch
#print axioms CheckAntiVacA083829.sat_prefix_hyp
#print axioms CheckAntiVacA083829.sat_seven_hyp
#print axioms CheckAntiVacA083829.ablation_P1_needs_even
#print axioms CheckAntiVacA083829.ablation_P2_needs_not7
#print axioms CheckAntiVacA083829.ablation_P3_bound

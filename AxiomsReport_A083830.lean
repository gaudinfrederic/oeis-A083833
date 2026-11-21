import A083830
import Spec_A083830
import Check_Spec_A083830
import Check_AntiVacuite_A083830
import A083829

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AxiomsReport_A083830 : couverture exhaustive des axiomes

Perimetre cible A083830 (5 modules) : `A083830` +
`Spec_A083830` + `Check_Spec_A083830` +
`Check_AntiVacuite_A083830` + cloture transitive
projet (`A083830 -> A083829` ; `Spec_A083830` et
`Check_AntiVacuite_A083830` importent `A083829`
directement).
38 declarations auditees ci-dessous.
Attendu partout : [propext, Classical.choice, Quot.sound].
-/

-- A083830 (1 decl)
#print axioms A083830_alphabet

-- Spec_A083830 (1 decl)
#print axioms SpecA083830

-- Check_Spec_A083830 (1 decl)
#print axioms proven_A083830

-- Check_AntiVacuite_A083830 (4 decls, namespace CheckAntiVacA083830)
#print axioms CheckAntiVacA083830.sat_even_branch
#print axioms CheckAntiVacA083830.sat_odd_branch
#print axioms CheckAntiVacA083830.ablation_alpha_tight
#print axioms CheckAntiVacA083830.ablation_needs_qpal

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

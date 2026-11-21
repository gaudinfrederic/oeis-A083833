import A083834
import Spec_A083834
import Check_Spec_A083834
import Check_AntiVacuite_A083834
import A083833

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AxiomsReport_A083834 : couverture exhaustive des axiomes

Perimetre cible A083834 (5 modules) : `A083834` +
`Spec_A083834` + `Check_Spec_A083834` +
`Check_AntiVacuite_A083834` + cloture transitive
projet (`A083834 -> A083833` ; `Spec_A083834` et
`Check_AntiVacuite_A083834` importent `A083833`
directement).
36 declarations auditees ci-dessous.
Attendu partout : [propext, Classical.choice, Quot.sound].
-/

-- A083834 (2 decls)
#print axioms A083834_alphabet
#print axioms A083834_repunit

-- Spec_A083834 (1 decl)
#print axioms SpecA083834

-- Check_Spec_A083834 (1 decl)
#print axioms proven_A083834

-- Check_AntiVacuite_A083834 (4 decls, namespace CheckAntiVacA083834)
#print axioms CheckAntiVacA083834.sat_odd_branch
#print axioms CheckAntiVacA083834.sat_even_branch
#print axioms CheckAntiVacA083834.ablation_C2_needs_even
#print axioms CheckAntiVacA083834.ablation_C1_tight

-- A083833 (28 decls, namespace A083833)
#print axioms A083833.dgt
#print axioms A083833.IsPal
#print axioms A083833.crry
#print axioms A083833.crry_zero
#print axioms A083833.crry_le
#print axioms A083833.decomp
#print axioms A083833.div_ten_pow
#print axioms A083833.qdgt
#print axioms A083833.crry_succ
#print axioms A083833.dgt_eq_zero_of_ge
#print axioms A083833.mp_cases
#print axioms A083833.crry_m_eq_zero_iff
#print axioms A083833.crry_sym_same
#print axioms A083833.crry_sym_succ
#print axioms A083833.dgt_parity_succ
#print axioms A083833.carry_const_succ
#print axioms A083833.carry_period_same
#print axioms A083833.carry_even_same
#print axioms A083833.carry_odd_same
#print axioms A083833.same_case_odd_a0
#print axioms A083833.same_case_digits
#print axioms A083833.succ_case_all2
#print axioms A083833.A083833_C1
#print axioms A083833.A083833_C2
#print axioms A083833.same_case_c1
#print axioms A083833.succ_case_carry
#print axioms A083833.A083834_C1
#print axioms A083833.A083834_C2

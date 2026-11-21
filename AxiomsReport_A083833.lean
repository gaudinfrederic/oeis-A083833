import A083833
import Spec_A083833
import Check_Spec_A083833
import Check_AntiVacuite_A083833

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AxiomsReport_A083833 : couverture exhaustive des axiomes

Perimetre cible A083833 (4 modules) : le module
principal `A083833` (auto-contenu, `import Mathlib`) +
`Spec_A083833` + `Check_Spec_A083833` +
`Check_AntiVacuite_A083833`. Le module `A083833`
declare aussi les theoremes compagnons `A083834_C1`
et `A083834_C2` (cible A083834).
34 declarations auditees ci-dessous.
Attendu partout : [propext, Classical.choice, Quot.sound].
-/

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

-- Spec_A083833 (1 decl)
#print axioms SpecA083833

-- Check_Spec_A083833 (1 decl)
#print axioms proven_A083833

-- Check_AntiVacuite_A083833 (4 decls, namespace CheckAntiVacA083833)
#print axioms CheckAntiVacA083833.sat_even_branch
#print axioms CheckAntiVacA083833.sat_odd_branch
#print axioms CheckAntiVacA083833.ablation_C2_needs_even
#print axioms CheckAntiVacA083833.ablation_C1_tight

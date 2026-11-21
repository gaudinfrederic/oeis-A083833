import Spec_A083834
import A083833

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_Spec_A083834 : fermeture Spec↔preuve (Option B)

Le Spec (`Spec_A083834.lean`) ne contient aucune preuve ; ce
fichier vérifie que les théorèmes compilés satisfont EXACTEMENT
les deux énoncés de la spec, dans l'ordre de la conjonction
(C1 `A083834_C1`, C2 `A083834_C2`). Les théorèmes vivent dans
le namespace `A083833` du module homonyme (théorèmes compagnons
de la suite image A083834).
-/

/-- Les preuves compilées satisfont les énoncés record C1-C2. -/
theorem proven_A083834 : SpecA083834 :=
  ⟨A083833.A083834_C1, A083833.A083834_C2⟩

#print axioms proven_A083834

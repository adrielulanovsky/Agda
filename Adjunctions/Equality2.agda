module Adjunctions.Equality2 where

open import Library
open import Categories
open import Adjunctions
open import Functors
open Adj3
open Fun

--Adj3 -> AdjUC
--Adjunctions.Equality2 -> Adjunctions.EqualityUC
-- adjunction3 -> adjunctionUC

--Adj3-Eq -> AdjUC-Eq
--Adj3-Eq2 -> AdjUC-Eq2

--Igualdad entre adjunciones unit-counit
--Dos adjunciones UC son iguales si L, R, η y ε son iguales
Adj3-Eq : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} → (p q : Adj3 C D) →
         L p ≅ L q
      → R p ≅ R q
      → (∀{A} → η p {A} ≅ η q {A})
      → (∀{A} → ε p {A} ≅ ε q {A})
      → p ≅ q
Adj3-Eq (adjunction3 L R η ε η-nat ε-nat triangle1 triangle2)
            (adjunction3 .L .R η₁ ε₁ η-nat₁ ε-nat₁ triangle3 triangle4)
            refl refl l r with iext (λ A → l {A}) | iext (λ A → (r {A}))
Adj3-Eq (adjunction3 L R η ε η-nat ε-nat triangle1 triangle2)
           (adjunction3 .L .R .η .ε η-nat₁ ε-nat₁ triangle3 triangle4)
            refl refl l r | refl | refl = proof
   adjunction3 L R η ε η-nat ε-nat triangle1 triangle2
   ≅⟨ cong8 adjunction3 refl refl refl refl
                        (iext (λ _ → iext (λ _ → iext (λ _ → ir η-nat η-nat₁))))
                        (iext (λ _ → iext (λ _ → iext (λ _ → ir ε-nat ε-nat₁))))
                        (iir triangle1 triangle3)
                        (iir triangle2 triangle4) ⟩
   adjunction3 L R η ε η-nat₁ ε-nat₁ triangle3 triangle4
   ∎



--Es suficiente con tener que L, R y η son iguales para afirmar la igualdad
--de adjunciones UC
Adj3-Eq2 : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} → (p q : Adj3 C D) →
         L p ≅ L q
      → R p ≅ R q
      → (∀{A} → η p {A} ≅ η q {A})
      → p ≅ q
Adj3-Eq2 {C = C}{D}(adjunction3 L R η ε η-nat ε-nat triangle1 triangle2)
             (adjunction3 .L .R η₁ ε₁ η-nat₁ ε-nat₁ triangle3 triangle4)
        refl refl l =
  let open Cat C renaming (Obj to ObjC ; Hom to HomC ; _∙_ to _∙C_ )
      open Cat D renaming (Obj to ObjD ; Hom to HomD ; _∙_ to _∙D_ ; iden to idenD ; idl to idlD ; idr to idrD ; ass to assD ; congl to conglD ; congr to congrD)
  in Adj3-Eq (adjunction3 L R η ε η-nat ε-nat triangle1 triangle2)
             (adjunction3 L R η₁ ε₁ η-nat₁ ε-nat₁ triangle3 triangle4)
             refl refl l
             (λ {A} -> proof
                            ε
                            ≅⟨ sym idlD ⟩
                            idenD ∙D ε
                            ≅⟨ ε-nat ⟩
                            ε ∙D HMap (L ○ R) idenD
                            ≅⟨ congrD (cong (HMap L) (fid R)) ⟩
                            ε ∙D HMap L iden
                            ≅⟨ congrD (cong (HMap L) (sym triangle3)) ⟩
                            ε ∙D HMap L (HMap R ε₁ ∙C η₁)
                            ≅⟨ congrD (fcomp L) ⟩
                            ε ∙D HMap L (HMap R ε₁) ∙D HMap L η₁
                            ≅⟨ sym assD ⟩
                            (ε ∙D HMap L (HMap R ε₁)) ∙D HMap L η₁
                            ≅⟨ conglD (sym ε-nat) ⟩
                            (ε₁ ∙D ε) ∙D HMap L η₁
                            ≅⟨ congrD (cong (HMap L) (sym l)) ⟩
                            (ε₁ ∙D ε) ∙D HMap L η
                            ≅⟨ assD ⟩
                            ε₁ ∙D ε ∙D HMap L η
                            ≅⟨ congrD triangle2 ⟩
                            ε₁ ∙D idenD
                            ≅⟨ idrD ⟩
                            ε₁
                            ∎)

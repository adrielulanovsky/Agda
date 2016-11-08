module Adjunctions.Equality2 where

open import Library
open import Categories
open import Adjunctions

open Adj3


Adj3-Eq-aux : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} → (p q : Adj3 C D) →
         L p ≅ L q
      → R p ≅ R q
      → (∀{A} → η p {A} ≅ η q {A})
      → (∀{A} → ε p {A} ≅ ε q {A})
      → p ≅ q
Adj3-Eq-aux (adjunction3 L R η ε η-nat ε-nat triangle1 triangle2)
            (adjunction3 .L .R η₁ ε₁ η-nat₁ ε-nat₁ triangle3 triangle4)
            refl refl l r with iext (λ A → l {A}) | iext (λ A → (r {A}))
Adj3-Eq-aux (adjunction3 L R η ε η-nat ε-nat triangle1 triangle2)
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


Adj3-Eq : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} → (p q : Adj3 C D) →
         L p ≅ L q
      → R p ≅ R q
      → (∀{A} → η p {A} ≅ η q {A})
      → p ≅ q
Adj3-Eq {C = C}{D}(adjunction3 L R η ε η-nat ε-nat triangle1 triangle2)
             (adjunction3 .L .R η₁ ε₁ η-nat₁ ε-nat₁ triangle3 triangle4)
        refl refl l =
  let open Cat C renaming (Obj to ObjC ; Hom to HomC ; _∙_ to _∙C_ )
      open Cat D renaming (Obj to ObjD ; Hom to HomD ; _∙_ to _∙D_ ; iden to idenD ; idl to idlD )
  in Adj3-Eq-aux (adjunction3 L R η ε η-nat ε-nat triangle1 triangle2)
                 (adjunction3 L R η₁ ε₁ η-nat₁ ε-nat₁ triangle3 triangle4)
                 refl refl l
                 (λ {A} -> proof
                            ε
                            ≅⟨ sym idlD ⟩
                            idenD ∙D ε
                            ≅⟨ {!congl!} ⟩
                            {!!}
                            ≅⟨ {!!} ⟩
                            {!!}
                            ≅⟨ {!!} ⟩
                            {!!}
                            ≅⟨ {!!} ⟩
                            {!!}
                            ≅⟨ {!!} ⟩
                            ε₁
                            ∎)
{-
Adj-Eq : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} → (p q : Adj C D) →
         L p ≅ L q
      → R p ≅ R q
      → (∀{A B} → left p {A} {B} ≅ left q {A} {B})
      → p ≅ q
Adj-Eq {C = C}{D}(adjunction L R left right lawa lawb natleft natright)
       (adjunction .L .R left₁ right₁ lawa₁ lawb₁ natleft₁ natright₁)
       refl refl l =
  let open Cat C renaming (Obj to ObjC ; Hom to HomC ; _∙_ to _∙C_ )
      open Cat D renaming (Obj to ObjD ; Hom to HomD ; _∙_ to _∙D_ ; iden to idenD )
  in Adj-Eq-aux (adjunction L R left right lawa lawb natleft natright)
                (adjunction L R left₁ right₁ lawa₁ lawb₁ natleft₁ natright₁)
                 refl refl l (λ {A} {B} → ext (λ f →  proof
                               right f
                             ≅⟨ cong right (sym (lawb₁ f)) ⟩
                              right (left₁ (right₁ f))
                             ≅⟨ cong (λ x → right (x (right₁ f))) (sym l) ⟩
                             right (left (right₁ f))
                             ≅⟨ lawa (right₁ f) ⟩
                               right₁ f
                              ∎))

-}

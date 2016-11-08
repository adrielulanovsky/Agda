
module Adjunctions.Equality where

open import Library
open import Categories
open import Adjunctions

open Adj



Adj-Eq-aux : ∀{a b c d}{C : Cat {a}{b}}{D : Cat {c}{d}} → (p q : Adj C D) →
         L p ≅ L q
      → R p ≅ R q
      → (∀{A B} → left p {A} {B} ≅ left q {A} {B})
      → (∀{A B} → right p {A} {B} ≅ right q {A} {B})
      → p ≅ q
Adj-Eq-aux (adjunction L R left right lawa lawb natleft natright)
       (adjunction .L .R left₁ right₁ lawa₁ lawb₁ natleft₁ natright₁)
       refl refl l r with iext (λ A → iext (λ B → (l {A} {B})))
                        | iext (λ A → iext (λ B → (r {A} {B}))) 
Adj-Eq-aux (adjunction L R left right lawa lawb natleft natright)
           (adjunction .L .R .left .right lawa₁ lawb₁ natleft₁ natright₁)
           refl refl l r | refl | refl = proof
   adjunction L R left right lawa lawb natleft natright
   ≅⟨ cong8 adjunction refl refl refl refl
                       (iext (λ _ → iext (λ _ → ext (λ a → ir (lawa a) (lawa₁ a)))))
                       (iext (λ _ → iext (λ _ → ext (λ a → ir (lawb a) (lawb₁ a)))))
                       (iext (λ _ → iext (λ _ → iext (λ _ → iext (λ _ → ext (λ a → ext (λ b → ext (λ c → ir (natleft a b c) (natleft₁ a b c)))))))))
                       ((iext (λ _ → iext (λ _ → iext (λ _ → iext (λ _ → ext (λ a → ext (λ b → ext (λ c → ir (natright a b c) (natright₁ a b c))))))))))
                       ⟩
   adjunction L R left right lawa₁ lawb₁ natleft₁ natright₁
   ∎

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


-----------------------------------------------------
